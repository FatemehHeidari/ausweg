//! Step 13: liquidity, proved. `ausweg prove` writes a Halmos proof for an
//! ERC-4626 vault and runs it with the integer back end (`smt.rs`).
//!
//! The proof is an induction over a world of three users, alice, bob and
//! carol, the same world the fuzz harness drives:
//! - init: a fresh deployment satisfies the invariant;
//! - keeps: from any state that satisfies it, every state-changing call, by any
//!   user with any arguments, leads to a state that satisfies it;
//! - exit: from any state that satisfies it, each user can redeem every share
//!   they hold, with none left, and withdraw what `maxWithdraw` quotes, and gets
//!   what the previews promise. A preview or max view that reverts is a failure.
//!
//! All three proved means: from every reachable state, every user can get out.
//!
//! The invariant: the users (and any address the constructor takes, such as a
//! fee treasury) hold all the shares and all the asset tokens; the asset's
//! supply stays at or below 2^96; and the share price is at least 1, that is
//! `totalAssets() >= totalSupply()`.

use crate::abi::{Abi, Item, Param};
use crate::baseline::{Restore, Target, backup_path};
use crate::forge::Forge;
use crate::mutate;
use crate::plan::{self, CtorValue};
use crate::scaffold;
use anyhow::{Context, Result, bail};
use serde::Serialize;
use std::fs;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

pub struct ProveOptions {
    pub halmos: String,
    pub forge_bin: String,
    /// Seconds the solver may spend on one query.
    pub solver_timeout: u64,
    /// Include "share price >= 1" in the invariant.
    pub price: bool,
    /// Limit every amount argument to 2^128.
    pub bound_amounts: bool,
    pub mutation: bool,
    pub max_mutants: usize,
}

#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Verdict {
    Proved,
    Counterexample,
    Timeout,
    /// Every path was cut by an assumption or reverted: nothing was checked.
    Vacuous,
    Error,
}

#[derive(Debug, Serialize, Clone)]
pub struct Check {
    pub name: String,
    pub verdict: Verdict,
    pub seconds: f64,
    pub paths: u64,
    /// Named values of the first counterexample, e.g. ("i", "bob").
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub counterexample: Vec<(String, String)>,
}

#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ProofOutcome {
    /// A check proved on clean code has a counterexample on the mutant.
    Caught,
    /// No counterexample, but a check proved on clean code timed out.
    Unknown,
    Survived,
    Invalid,
}

#[derive(Debug, Serialize)]
pub struct ProofMutant {
    pub line: usize,
    pub change: String,
    pub outcome: ProofOutcome,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub caught_by: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub timed_out: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct ProofMutation {
    pub mutants: usize,
    pub caught: usize,
    pub unknown: usize,
    pub survived: usize,
    pub invalid: usize,
    /// caught / valid mutants.
    pub kill_rate: Option<f64>,
    pub detail: Vec<ProofMutant>,
}

#[derive(Debug, Serialize)]
pub struct ProveReport {
    pub contract: String,
    pub test_file: String,
    /// Addresses the invariant counts as holders, besides the three users.
    pub other_holders: Vec<String>,
    pub price_at_least_one: bool,
    /// Amount arguments limited to 2^128 (`--bound-amounts`).
    pub amounts_bounded: bool,
    /// For an ERC-7540 vault: how a request becomes claimable, and what the
    /// probe saw the vault do with one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub exit: Option<AsyncExit>,
    pub checks: Vec<Check>,
    /// Every check proved: exit holds in every reachable state of the world.
    pub liquidity_proved: bool,
    pub seconds: f64,
    pub mutation: Option<ProofMutation>,
}

/// Functions the proof needs on the vault.
const NEEDED: [&str; 13] = [
    "asset",
    "totalAssets",
    "totalSupply",
    "balanceOf",
    "deposit",
    "mint",
    "withdraw",
    "redeem",
    "maxRedeem",
    "maxWithdraw",
    "previewRedeem",
    "previewWithdraw",
    "transfer",
];

/// Calls that only need a signature: they change allowances, which the
/// invariant does not mention.
const SKIP: &[&str] = &["permit"];

pub fn supports(abi: &Abi) -> Result<()> {
    let missing: Vec<&str> = NEEDED
        .iter()
        .copied()
        .filter(|n| !abi.items.iter().any(|i| i.is_function() && i.name == *n))
        .collect();
    if !missing.is_empty() {
        bail!(
            "not an ERC-4626 vault ausweg can prove: missing {}",
            missing.join(", ")
        );
    }
    Ok(())
}

const RESERVED: &[&str] = &[
    "target", "asset", "alice", "bob", "carol", "svm", "vm", "CAP", "PRICE", "callerI", "u", "i",
];

pub(crate) fn ident(name: &str, fallback: String, taken: &[String]) -> String {
    let n = name.trim_matches('_');
    let ok = !n.is_empty()
        && n.starts_with(|c: char| c.is_ascii_alphabetic())
        && n.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !RESERVED.contains(&n)
        && !taken.iter().any(|t| t == n);
    if ok { n.to_string() } else { fallback }
}

pub(crate) fn typed(p: &Param, address_expr: &str) -> String {
    match p.contract_type() {
        Some(c) => format!("{c}({address_expr})"),
        None => address_expr.to_string(),
    }
}

/// The proof file, its check names, and the addresses counted as holders
/// besides the users.
pub struct Proof {
    pub source: String,
    pub checks: Vec<String>,
    pub other_holders: Vec<String>,
    /// For an ERC-7540 vault: how a request becomes claimable, and what the
    /// probe saw the vault do with one.
    pub exit: Option<AsyncExit>,
}

#[derive(Debug, Serialize, Clone)]
pub struct AsyncExit {
    pub progress: crate::asyncproof::Progress,
    pub style: crate::asyncproof::Style,
    /// The vault's running totals and price rule, as the probe read them.
    pub learned: crate::asyncproof::Learned,
}

fn keeps_check(item: &Item, name: &str, bound: bool) -> Option<String> {
    let mut params = vec!["uint256 callerI".to_string()];
    let mut assumes = vec!["callerI < 3".to_string()];
    let mut args = Vec::new();
    let mut taken: Vec<String> = Vec::new();
    for (i, p) in item.inputs.iter().enumerate() {
        if !p.is_supported() {
            return None;
        }
        let n = ident(&p.name, format!("a{i}"), &taken);
        taken.push(n.clone());
        if p.is_address() {
            params.push(format!("uint256 {n}I"));
            assumes.push(format!("{n}I < 3"));
            args.push(typed(p, &format!("_user({n}I)")));
        } else {
            params.push(format!("{} {n}", p.ty));
            if bound && p.ty.starts_with("uint") {
                assumes.push(format!("{n} <= MAX_AMOUNT"));
            }
            args.push(n);
        }
    }
    Some(format!(
        "    /// {sig}: keeps the invariant, for any caller and arguments.\n    function {name}({params}) public {{\n        vm.assume({assumes});\n        vm.assume(_inv());\n        _witness();\n        vm.prank(_user(callerI));\n        try target.{f}({args}) {{\n            assert(_holds());\n        }} catch {{}}\n    }}\n",
        sig = item.signature(),
        params = params.join(", "),
        assumes = assumes.join(" && "),
        f = item.name,
        args = args.join(", "),
    ))
}

/// The constructor's arguments in the proof's deployment, and the fixed
/// addresses made for its non-token address parameters (a fee treasury).
pub(crate) fn ctor_args(abi: &Abi) -> Result<(String, Vec<String>)> {
    let params = abi.constructor();
    let mut ctor = Vec::new();
    let mut passive: Vec<String> = Vec::new();
    let mut tokens = 0;
    for (i, p) in params.iter().enumerate() {
        let v = plan::default_ctor_value(i, p).with_context(|| {
            format!("constructor parameter {} ({}) has no default", p.name, p.ty)
        })?;
        ctor.push(match v {
            CtorValue::MockToken => {
                tokens += 1;
                if tokens > 1 {
                    bail!("the proof supports one asset token; the constructor takes more");
                }
                typed(p, "address(asset)")
            }
            CtorValue::User => typed(p, "alice"),
            CtorValue::NewAddress => {
                let n = ident(&p.name, format!("holder{i}"), &passive);
                passive.push(n.clone());
                typed(p, &n)
            }
            CtorValue::Number(n) => n,
            CtorValue::Bool(b) => b.to_string(),
            CtorValue::Str(s) => format!(
                "\"{}\"",
                s.chars()
                    .filter(|c| c.is_ascii_alphanumeric() || *c == ' ')
                    .collect::<String>()
            ),
        });
    }
    if tokens == 0 {
        bail!("no constructor parameter takes the asset token");
    }
    Ok((ctor.join(", "), passive))
}

pub fn render(
    contract: &str,
    import_path: &str,
    abi: &Abi,
    price: bool,
    bound: bool,
) -> Result<Proof> {
    let (ctor, passive) = ctor_args(abi)?;
    let c = contract;

    let passive_decls: String = passive
        .iter()
        .enumerate()
        // A fixed address: Halmos models `makeAddr` as an unknown function, so
        // the solver could make a treasury equal to a user.
        .map(|(k, n)| {
            format!(
                "    address internal constant {n} = address(0x{:X});\n",
                0x7EA50 + k
            )
        })
        .collect();
    let mut token_holders = vec!["alice", "bob", "carol", "address(target)"];
    token_holders.extend(passive.iter().map(String::as_str));
    let mut share_holders = vec!["alice", "bob", "carol"];
    share_holders.extend(passive.iter().map(String::as_str));
    let mut inv = String::from(
        "        uint256 supply = asset.totalSupply();\n        if (supply > CAP) return false;\n",
    );
    let mut terms = Vec::new();
    for (k, h) in token_holders.iter().enumerate() {
        inv.push_str(&format!(
            "        uint256 t{k} = asset.balanceOf({h});\n        if (t{k} > CAP) return false;\n"
        ));
        terms.push(format!("t{k}"));
    }
    inv.push_str(&format!(
        "        if ({} != supply) return false;\n",
        terms.join(" + ")
    ));
    let mut terms = Vec::new();
    for (k, h) in share_holders.iter().enumerate() {
        inv.push_str(&format!(
            "        uint256 s{k} = target.balanceOf({h});\n        if (s{k} > CAP) return false;\n"
        ));
        terms.push(format!("s{k}"));
    }
    inv.push_str(&format!(
        "        if ({} != target.totalSupply()) return false;\n",
        terms.join(" + ")
    ));
    if price {
        inv.push_str("        if (target.totalAssets() < target.totalSupply()) return false;\n");
    }
    inv.push_str("        return true;\n");

    let mut checks = vec!["check_init".to_string()];
    let mut keeps = String::new();
    for item in abi.mutating() {
        if SKIP.contains(&item.name.as_str()) {
            continue;
        }
        let base = format!("check_keeps_{}", item.name);
        let mut name = base.clone();
        let mut k = 2;
        while checks.contains(&name) {
            name = format!("{base}_{k}");
            k += 1;
        }
        if let Some(f) = keeps_check(item, &name, bound) {
            keeps.push_str(&f);
            keeps.push('\n');
            checks.push(name);
        }
    }
    for n in [
        "check_keeps_asset_transfer",
        "check_keeps_asset_transferFrom",
        "check_keeps_asset_approve",
        "check_keeps_asset_mint",
        "check_exit_redeem",
        "check_exit_withdraw",
    ] {
        checks.push(n.to_string());
    }

    let price_const = if price { "true" } else { "false" };
    let amount_bound = |v: &str| {
        if bound {
            format!(" && {v} <= MAX_AMOUNT")
        } else {
            String::new()
        }
    };
    let (b_transfer, b_from, b_approve) = (
        amount_bound("amount"),
        amount_bound("amount"),
        amount_bound("amount"),
    );
    let source = format!(
        r#"// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Written by ausweg (Step 13): a Halmos proof that every user can always get out.
// Run with `ausweg prove`, which gives Halmos ausweg's integer solver back end.
//
// World: three users (alice, bob, carol) act; {others}.
// Invariant (_inv): the users{and_others} hold every share and every asset
// token, the vault holding its own assets; the asset's supply is at most 2^96;
// {price_line}{amounts_line}
//
// check_init: a fresh deployment satisfies the invariant.
// check_keeps_*: every state-changing call keeps it, for any caller and arguments.
// check_exit_redeem: from any state that satisfies it, each user redeems every
// share they hold. check_exit_withdraw: each user withdraws what maxWithdraw
// quotes. A preview or max view that reverts fails the check.

import {{Test}} from "forge-std/Test.sol";
import "{import_path}";
import {{AuswegToken}} from "./{token_file}";

interface AuswegSVM {{
    function enableSymbolicStorage(address) external;
    function createUint256(string memory) external returns (uint256);
}}

contract {c}Proof is Test {{
    AuswegSVM internal constant svm = AuswegSVM(address(uint160(uint256(keccak256("svm cheat code")))));
    uint256 internal constant CAP = 2 ** 96;
    // Amount arguments are limited to this with --bound-amounts.
    uint256 internal constant MAX_AMOUNT = 2 ** 128;
    bool internal constant PRICE = {price_const};
    address internal constant alice = address(0xA11CE);
    address internal constant bob = address(0xB0B);
    address internal constant carol = address(0xCA201);
{passive_decls}    AuswegToken internal asset;
    {c} internal target;

    // Any state at all: Halmos makes every storage slot of both contracts symbolic.
    function setUp() public {{
        asset = new AuswegToken();
        target = new {c}({ctor});
        svm.enableSymbolicStorage(address(asset));
        svm.enableSymbolicStorage(address(target));
    }}

    function _user(uint256 i) internal pure returns (address) {{
        return i == 0 ? alice : i == 1 ? bob : carol;
    }}

    function _holder(uint256 i) internal view returns (address) {{
        return i < 3 ? _user(i) : address(target);
    }}

    function _inv() internal view returns (bool) {{
{inv}    }}

    /// The invariant, called from outside so that a revert can be caught.
    function auswegInvariant() external view returns (bool) {{
        return _inv();
    }}

    /// Whether the invariant holds after a call. A view that reverts counts
    /// as breaking it: Halmos drops a path that reverts.
    function _holds() internal view returns (bool) {{
        try this.auswegInvariant() returns (bool ok) {{
            return ok;
        }} catch {{
            return false;
        }}
    }}

    // Names for a counterexample's numbers.
    function _witness() internal {{
        vm.assume(target.totalSupply() == svm.createUint256("totalSupply"));
        vm.assume(target.totalAssets() == svm.createUint256("totalAssets"));
    }}

    function check_init() public {{
        asset = new AuswegToken();
        target = new {c}({ctor});
        assert(_holds());
    }}

{keeps}    /// The asset token moves between holders, the vault included: a donation.
    function check_keeps_asset_transfer(uint256 callerI, uint256 toI, uint256 amount) public {{
        vm.assume(callerI < 3 && toI < 4{b_transfer});
        vm.assume(_inv());
        _witness();
        vm.prank(_user(callerI));
        asset.transfer(_holder(toI), amount);
        assert(_holds());
    }}

    function check_keeps_asset_transferFrom(uint256 callerI, uint256 fromI, uint256 toI, uint256 amount) public {{
        vm.assume(callerI < 3 && fromI < 3 && toI < 4{b_from});
        vm.assume(_inv());
        _witness();
        vm.prank(_user(callerI));
        asset.transferFrom(_user(fromI), _holder(toI), amount);
        assert(_holds());
    }}

    function check_keeps_asset_approve(uint256 callerI, uint256 spenderI, uint256 amount) public {{
        vm.assume(callerI < 3 && spenderI < 4{b_approve});
        vm.assume(_inv());
        vm.prank(_user(callerI));
        asset.approve(_holder(spenderI), amount);
        assert(_holds());
    }}

    /// New asset tokens, to a user or to the vault (yield), up to the supply cap.
    function check_keeps_asset_mint(uint256 toI, uint256 amount) public {{
        vm.assume(toI < 4);
        vm.assume(_inv());
        _witness();
        vm.assume(amount <= CAP && asset.totalSupply() + amount <= CAP);
        asset.mint(_holder(toI), amount);
        assert(_holds());
    }}

    /// From any state that satisfies the invariant, user i redeems every share
    /// they hold, not just what maxRedeem quotes, and keeps none.
    function check_exit_redeem(uint256 i) public {{
        vm.assume(i < 3);
        address u = _user(i);
        vm.assume(_inv());
        _witness();
        uint256 shares = target.balanceOf(u);
        vm.assume(shares == svm.createUint256("userShares"));
        vm.assume(shares > 0);
        // A revert here would drop the state from the check: count it as a failure.
        uint256 promised;
        try target.previewRedeem(shares) returns (uint256 p) {{
            promised = p;
        }} catch {{
            assert(false);
        }}
        uint256 before = asset.balanceOf(u);
        vm.prank(u);
        try target.redeem(shares, u, u) returns (uint256 paid) {{
            assert(paid >= promised);
            assert(asset.balanceOf(u) == before + paid);
            assert(target.balanceOf(u) == 0);
        }} catch {{
            assert(false);
        }}
    }}

    /// From any state that satisfies the invariant, user i withdraws what
    /// maxWithdraw quotes.
    function check_exit_withdraw(uint256 i) public {{
        vm.assume(i < 3);
        address u = _user(i);
        vm.assume(_inv());
        _witness();
        vm.assume(target.balanceOf(u) == svm.createUint256("userShares"));
        uint256 assets;
        try target.maxWithdraw(u) returns (uint256 a) {{
            assets = a;
        }} catch {{
            assert(false);
        }}
        vm.assume(assets > 0);
        uint256 cost;
        try target.previewWithdraw(assets) returns (uint256 c) {{
            cost = c;
        }} catch {{
            assert(false);
        }}
        uint256 sharesBefore = target.balanceOf(u);
        uint256 before = asset.balanceOf(u);
        vm.prank(u);
        try target.withdraw(assets, u, u) returns (uint256 burned) {{
            assert(burned <= cost);
            assert(target.balanceOf(u) + burned == sharesBefore);
            assert(asset.balanceOf(u) == before + assets);
        }} catch {{
            assert(false);
        }}
    }}
}}
"#,
        others = if passive.is_empty() {
            "nobody else holds anything".to_string()
        } else {
            format!("{} only receives", passive.join(", "))
        },
        and_others = if passive.is_empty() {
            String::new()
        } else {
            format!(" and {}", passive.join(", "))
        },
        price_line = if price {
            "and the share price is at least 1: totalAssets() >= totalSupply()."
        } else {
            "the share price is not constrained (--no-price)."
        },
        token_file = scaffold::TOKEN_FILE,
        amounts_line = if bound {
            "\n// Amount arguments are at most 2^128 (--bound-amounts)."
        } else {
            ""
        },
    );
    Ok(Proof {
        source,
        checks,
        other_holders: passive,
        exit: None,
    })
}

// ---------------------------------------------------------------- running

/// What a run of Halmos says about each check; None when the build failed.
fn run_halmos(
    repo: &Path,
    proof_contract: &str,
    opts: &ProveOptions,
    early_exit: bool,
) -> Result<(Option<Vec<Check>>, String)> {
    let exe = std::env::current_exe().context("finding the ausweg executable")?;
    let json = std::env::temp_dir().join(format!(
        "ausweg-halmos-{}-{proof_contract}.json",
        std::process::id()
    ));
    let _ = fs::remove_file(&json);
    let mut cmd = Command::new(&opts.halmos);
    cmd.arg("--root")
        .arg(repo)
        .args(["--contract", proof_contract])
        .arg("--solver-command")
        .arg(format!("{} smt", exe.display()))
        .arg("--solver-timeout-assertion")
        .arg(format!("{}s", opts.solver_timeout + 5))
        .arg("--json-output")
        .arg(&json)
        .env("FOUNDRY_DYNAMIC_TEST_LINKING", "false")
        .env("AUSWEG_SMT_TIMEOUT", opts.solver_timeout.to_string())
        .current_dir(repo);
    if early_exit {
        cmd.arg("--early-exit");
    }
    // Halmos calls `forge` itself: make the one ausweg was given come first.
    let forge = Path::new(&opts.forge_bin);
    if let Some(dir) = forge.parent().filter(|d| !d.as_os_str().is_empty()) {
        let path = std::env::var_os("PATH").unwrap_or_default();
        let mut dirs = vec![dir.to_path_buf()];
        dirs.extend(std::env::split_paths(&path));
        cmd.env("PATH", std::env::join_paths(dirs)?);
    }
    if early_exit {
        // On a mutant one counterexample settles it: stop at the first [FAIL].
        cmd.stdout(Stdio::piped()).stderr(Stdio::null());
        own_group(&mut cmd);
        let mut child = cmd
            .spawn()
            .with_context(|| format!("running {} (install Halmos: see the README)", opts.halmos))?;
        let stdout = child.stdout.take().context("reading Halmos's output")?;
        let mut log = String::new();
        let mut failed = None;
        for line in BufReader::new(stdout).lines() {
            let line = strip_ansi(&line?);
            log.push_str(&line);
            log.push('\n');
            if let Some(rest) = line.trim_start().strip_prefix("[FAIL]") {
                failed = rest
                    .split_whitespace()
                    .next()
                    .map(|f| f.split('(').next().unwrap_or(f).to_string());
                break;
            }
        }
        if let Some(name) = failed {
            stop_group(&mut child);
            let _ = fs::remove_file(&json);
            let check = Check {
                name,
                verdict: Verdict::Counterexample,
                seconds: 0.0,
                paths: 0,
                counterexample: Vec::new(),
            };
            return Ok((Some(vec![check]), log));
        }
        let _ = child.wait();
        let Ok(text) = fs::read_to_string(&json) else {
            return Ok((None, log));
        };
        let _ = fs::remove_file(&json);
        return Ok((parse_results(&text, proof_contract)?, log));
    }
    let out = cmd
        .output()
        .with_context(|| format!("running {} (install Halmos: see the README)", opts.halmos))?;
    let log = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let Ok(text) = fs::read_to_string(&json) else {
        return Ok((None, log));
    };
    let _ = fs::remove_file(&json);
    Ok((parse_results(&text, proof_contract)?, log))
}

/// The end of Halmos's output, without forge's lint warnings.
fn log_tail(log: &str) -> String {
    let lines: Vec<&str> = log
        .lines()
        .filter(|l| {
            let t = l.trim();
            !t.is_empty()
                && !t.starts_with("warning[")
                && !t.starts_with(|c: char| "│╭╰━|".contains(c))
                && !t.chars().next().is_some_and(|c| c.is_ascii_digit()) | !t.contains('│')
        })
        .collect();
    lines[lines.len().saturating_sub(30)..].join("\n")
}

/// Halmos colours its result lines.
fn strip_ansi(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' {
            for d in chars.by_ref() {
                if d.is_ascii_alphabetic() {
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

fn user_name(v: u64) -> String {
    match v {
        0 => "alice".into(),
        1 => "bob".into(),
        2 => "carol".into(),
        3 => "the vault".into(),
        other => other.to_string(),
    }
}

/// Halmos's `--json-output`, for the checks of one proof contract.
pub fn parse_results(text: &str, proof_contract: &str) -> Result<Option<Vec<Check>>> {
    let v: serde_json::Value = serde_json::from_str(text).context("reading Halmos's JSON")?;
    let Some(results) = v.get("test_results").and_then(|r| r.as_object()) else {
        return Ok(None);
    };
    let suffix = format!(":{proof_contract}");
    let matching: Vec<(&String, &serde_json::Value)> = results
        .iter()
        .filter(|(k, _)| k.ends_with(&suffix))
        .collect();
    // Another contract of the same name runs too (Halmos selects by name):
    // the one ausweg wrote is in test/generated/.
    let chosen = matching
        .iter()
        .find(|(k, _)| k.contains("test/generated/"))
        .or_else(|| matching.first());
    if matching.len() > 1
        && let Some((k, _)) = chosen
    {
        eprintln!(
            "note: {} contracts named {proof_contract} ran; ausweg reads {k}",
            matching.len()
        );
    }
    let Some(list) = chosen.and_then(|(_, l)| l.as_array()) else {
        return Ok(None);
    };
    let mut checks = Vec::new();
    for r in list {
        let full = r.get("name").and_then(|n| n.as_str()).unwrap_or("");
        let name = full.split('(').next().unwrap_or(full).to_string();
        let verdict = match r.get("exitcode").and_then(|e| e.as_i64()) {
            Some(0) => Verdict::Proved,
            Some(1) => Verdict::Counterexample,
            Some(2) => Verdict::Timeout,
            Some(4) => Verdict::Vacuous,
            _ => Verdict::Error,
        };
        let seconds = r
            .get("time")
            .and_then(|t| t.get(0))
            .and_then(|t| t.as_f64())
            .unwrap_or(0.0);
        let paths = r
            .get("num_paths")
            .and_then(|t| t.get(0))
            .and_then(|t| t.as_u64())
            .unwrap_or(0);
        let mut counterexample = Vec::new();
        if let Some(model) = r
            .get("models")
            .and_then(|m| m.get(0))
            .and_then(|m| m.get("model"))
            .and_then(|m| m.as_object())
        {
            let mut vars: Vec<(String, String)> = model
                .values()
                .filter_map(|var| {
                    let name = var.get("variable_name")?.as_str()?.to_string();
                    let value = var.get("value")?;
                    let n = value.as_u64();
                    let shown = if name == "callerI" && n == Some(3) {
                        // ERC-7540 proofs: the fourth caller is the owner.
                        "the owner".to_string()
                    } else if name == "i" || name.ends_with('I') {
                        n.map(user_name).unwrap_or_else(|| value.to_string())
                    } else {
                        n.map(|n| n.to_string())
                            .unwrap_or_else(|| value.to_string())
                    };
                    Some((name, shown))
                })
                .collect();
            vars.sort();
            counterexample = vars;
        }
        checks.push(Check {
            name,
            verdict,
            seconds,
            paths,
            counterexample,
        });
    }
    Ok(Some(checks))
}

/// The proof file written into the project, ready for Halmos.
struct Prepared {
    target: Target,
    proof: Proof,
    proof_contract: String,
    test_rel: PathBuf,
}

fn prepare(
    repo: &Path,
    contract: &Path,
    forge: &dyn Forge,
    price: bool,
    bound_amounts: bool,
) -> Result<Prepared> {
    let target = Target::open(repo, contract)?;
    let file_name = contract
        .file_name()
        .and_then(|f| f.to_str())
        .context("contract path has no file name")?;
    let gen_dir = repo.join("test/generated");
    fs::create_dir_all(&gen_dir)?;
    let test_rel = PathBuf::from("test/generated").join(format!("{}.proof.t.sol", target.name));
    let test_abs = repo.join(&test_rel);
    let _ = fs::remove_file(&test_abs);
    fs::write(gen_dir.join(scaffold::TOKEN_FILE), scaffold::TOKEN_SOURCE)?;

    let build = forge.build_json(repo)?;
    if !build.ok {
        bail!(
            "the project does not compile before ausweg adds anything:\n{}",
            build.output
        );
    }
    let abi = Abi::load(repo, file_name, &target.name)?;
    let import_path = format!("../../{}", contract.display());
    let proof = match crate::asyncproof::kind(&abi) {
        Some(progress) => {
            crate::asyncproof::supports(&abi)?;
            let stored = crate::abi::load_stored_totals(repo, file_name, &target.name);
            let (style, learned) = probe(
                repo,
                forge,
                &target.name,
                &import_path,
                &abi,
                progress,
                &stored,
            )?;
            for u in &learned.unread {
                eprintln!(
                    "note: ausweg could not tell which requests {u} counts; the invariant leaves it out"
                );
            }
            if progress == crate::asyncproof::Progress::Time && !stored.is_empty() {
                eprintln!(
                    "note: ausweg reads running totals of owner-fulfilled vaults only; the invariant leaves {} out",
                    stored
                        .iter()
                        .map(|s| s.label.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
            let mut p = crate::asyncproof::render(
                &target.name,
                &import_path,
                &abi,
                progress,
                style,
                &learned,
                price,
                bound_amounts,
            )?;
            p.exit = Some(AsyncExit {
                progress,
                style,
                learned,
            });
            p
        }
        None => {
            supports(&abi)?;
            render(&target.name, &import_path, &abi, price, bound_amounts)?
        }
    };
    fs::write(&test_abs, &proof.source)?;
    let proof_contract = format!("{}Proof", target.name);
    Ok(Prepared {
        target,
        proof,
        proof_contract,
        test_rel,
    })
}

/// Walks one request through an ERC-7540 vault in a forge test and reads off
/// where its shares and assets go, what its running totals count, and how it
/// prices a share.
fn probe(
    repo: &Path,
    forge: &dyn Forge,
    contract: &str,
    import_path: &str,
    abi: &Abi,
    progress: crate::asyncproof::Progress,
    stored: &[crate::abi::Stored],
) -> Result<(crate::asyncproof::Style, crate::asyncproof::Learned)> {
    use crate::asyncproof as a;
    let rel = PathBuf::from("test/generated").join(a::probe_file(contract));
    fs::write(
        repo.join(&rel),
        a::probe_source(contract, import_path, abi, progress, stored)?,
    )?;
    let result = forge.test(repo, &rel.display().to_string())?;
    if !result.ran {
        bail!(
            "the request probe {} did not run:\n{}",
            rel.display(),
            log_tail(&result.output)
        );
    }
    if !result.passed.iter().any(|t| t == a::PROBE_RUNS) {
        let why = result
            .failed
            .iter()
            .find(|f| f.name == a::PROBE_RUNS)
            .map(|f| f.reason.clone())
            .unwrap_or_default();
        bail!(
            "ausweg could not take a request from request to claimable in {} ({}): {why}",
            rel.display(),
            match progress {
                a::Progress::Owner => "deposit, requestRedeem, then fulfillRedeem by the owner",
                a::Progress::Time => "deposit, requestRedeem, then ten years pass",
            }
        );
    }
    let stored = if progress == a::Progress::Owner {
        stored
    } else {
        &[]
    };
    Ok((
        a::style_from(&result.passed),
        a::learned_from(&result.passed, stored),
    ))
}

pub fn run(
    repo: &Path,
    contract: &Path,
    forge: &dyn Forge,
    opts: &ProveOptions,
) -> Result<ProveReport> {
    let started = Instant::now();
    let Prepared {
        target,
        proof,
        proof_contract,
        test_rel,
    } = prepare(repo, contract, forge, opts.price, opts.bound_amounts)?;

    let (checks, log) = run_halmos(repo, &proof_contract, opts, false)?;
    let Some(checks) = checks else {
        bail!("Halmos did not run the proof:\n{}", log_tail(&log));
    };
    let liquidity_proved = !checks.is_empty()
        && checks.iter().all(|c| c.verdict == Verdict::Proved)
        && proof
            .checks
            .iter()
            .all(|n| checks.iter().any(|c| &c.name == n));

    let mut report = ProveReport {
        contract: contract.display().to_string(),
        test_file: test_rel.display().to_string(),
        other_holders: proof.other_holders,
        price_at_least_one: opts.price,
        amounts_bounded: opts.bound_amounts,
        exit: proof.exit,
        checks,
        liquidity_proved,
        seconds: 0.0,
        mutation: None,
    };
    let proved: Vec<String> = report
        .checks
        .iter()
        .filter(|c| c.verdict == Verdict::Proved)
        .map(|c| c.name.clone())
        .collect();
    if opts.mutation && !proved.is_empty() {
        report.mutation = Some(score(repo, &target, &proof_contract, &proved, opts)?);
    }
    report.seconds = started.elapsed().as_secs_f64();
    Ok(report)
}

fn score(
    repo: &Path,
    target: &Target,
    proof_contract: &str,
    proved: &[String],
    opts: &ProveOptions,
) -> Result<ProofMutation> {
    let ms = mutate::mutants(&target.source, opts.max_mutants);
    let backup = backup_path(&target.abs);
    fs::write(&backup, &target.source)?;
    let _restore = Restore {
        path: &target.abs,
        backup: &backup,
        original: &target.source,
    };
    let mut detail = Vec::with_capacity(ms.len());
    for (k, m) in ms.iter().enumerate() {
        eprintln!(
            "  mutant {}/{}: line {}: {}",
            k + 1,
            ms.len(),
            m.line,
            m.change
        );
        fs::write(&target.abs, &m.source)?;
        let (checks, _) = run_halmos(repo, proof_contract, opts, true)?;
        let (outcome, caught_by, timed_out) = match checks {
            None => (ProofOutcome::Invalid, Vec::new(), Vec::new()),
            Some(checks) => {
                let pick = |v: &[Verdict]| -> Vec<String> {
                    checks
                        .iter()
                        .filter(|c| proved.contains(&c.name) && v.contains(&c.verdict))
                        .map(|c| c.name.clone())
                        .collect()
                };
                let caught = pick(&[Verdict::Counterexample]);
                let timed = pick(&[Verdict::Timeout, Verdict::Error]);
                let outcome = if !caught.is_empty() {
                    ProofOutcome::Caught
                } else if !timed.is_empty() {
                    ProofOutcome::Unknown
                } else {
                    ProofOutcome::Survived
                };
                (outcome, caught, timed)
            }
        };
        detail.push(ProofMutant {
            line: m.line,
            change: m.change.clone(),
            outcome,
            caught_by,
            timed_out,
        });
    }
    let count = |o: ProofOutcome| detail.iter().filter(|d| d.outcome == o).count();
    let (caught, unknown) = (count(ProofOutcome::Caught), count(ProofOutcome::Unknown));
    let (survived, invalid) = (count(ProofOutcome::Survived), count(ProofOutcome::Invalid));
    let valid = caught + unknown + survived;
    Ok(ProofMutation {
        mutants: ms.len(),
        caught,
        unknown,
        survived,
        invalid,
        kill_rate: (valid > 0).then(|| caught as f64 / valid as f64),
        detail,
    })
}

/// Runs Halmos in a process group of its own. Halmos starts each solver as its
/// child; killing Halmos alone leaves them running, still using CPU and memory.
fn own_group(cmd: &mut Command) {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0);
    }
}

/// Stops Halmos and every solver still running in its group.
fn stop_group(child: &mut std::process::Child) {
    #[cfg(unix)]
    // SAFETY: killpg only sends a signal, to the group `own_group` made.
    unsafe {
        libc::killpg(child.id() as libc::pid_t, libc::SIGKILL);
    }
    let _ = child.kill();
    let _ = child.wait();
}

// ---------------------------------------------------------------- benchmark

pub struct BenchOptions {
    pub halmos: String,
    pub forge_bin: String,
    /// Seconds per solver query, the same for every solver.
    pub solver_timeout: u64,
    /// Wall-clock seconds one check may take with one solver.
    pub cap: u64,
    pub price: bool,
    pub bound_amounts: bool,
    /// `ausweg` for the integer back end; anything else is passed to
    /// `halmos --solver` (yices, bitwuzla, z3, cvc5, ...).
    pub solvers: Vec<String>,
    /// Checks whose name starts with this, e.g. `check_exit` or `test_RT`.
    pub checks: String,
    /// `halmos --loop`, for suites with loops (a16z's needs 4).
    pub loop_bound: Option<u32>,
}

/// What to benchmark.
pub enum BenchTarget {
    /// A vault: ausweg writes its liquidity proof and runs those checks.
    Proof(PathBuf),
    /// Halmos tests already in the project, e.g. a16z's ERC-4626 suite.
    Suite { file: PathBuf, contract: String },
}

impl BenchTarget {
    /// `test/OZVault.a16z.t.sol:OZVaultA16z`
    pub fn suite(spec: &str) -> Result<Self> {
        let (file, contract) = spec
            .rsplit_once(':')
            .context("a suite is <test file>:<contract>, e.g. test/Vault.t.sol:VaultTest")?;
        Ok(Self::Suite {
            file: PathBuf::from(file),
            contract: contract.to_string(),
        })
    }
}

#[derive(Debug, Serialize)]
pub struct BenchCell {
    pub solver: String,
    /// None: still running when the cap was reached.
    pub verdict: Option<Verdict>,
    pub seconds: f64,
}

impl BenchCell {
    /// `proved 3s`, `unfinished at 300s`.
    pub fn text(&self) -> String {
        match self.verdict {
            Some(Verdict::Proved) => format!("proved {:.0}s", self.seconds),
            Some(Verdict::Counterexample) => format!("counterexample {:.0}s", self.seconds),
            Some(Verdict::Timeout) => format!("timeout {:.0}s", self.seconds),
            Some(Verdict::Vacuous) => format!("vacuous {:.0}s", self.seconds),
            Some(Verdict::Error) => format!("error {:.0}s", self.seconds),
            None => format!("unfinished at {:.0}s", self.seconds),
        }
    }
}

#[derive(Debug, Serialize)]
pub struct BenchRow {
    pub check: String,
    pub cells: Vec<BenchCell>,
}

#[derive(Debug, Serialize)]
pub struct BenchReport {
    pub contract: String,
    pub test_file: String,
    pub solver_timeout: u64,
    pub cap: u64,
    pub rows: Vec<BenchRow>,
}

/// One check with one solver, stopped at the cap.
fn bench_one(
    repo: &Path,
    test_contract: &str,
    check: &str,
    solver: &str,
    opts: &BenchOptions,
) -> Result<BenchCell> {
    let exe = std::env::current_exe().context("finding the ausweg executable")?;
    let json = std::env::temp_dir().join(format!(
        "ausweg-bench-{}-{test_contract}-{check}-{solver}.json",
        std::process::id()
    ));
    let _ = fs::remove_file(&json);
    let mut cmd = Command::new(&opts.halmos);
    cmd.arg("--root")
        .arg(repo)
        .args(["--contract", test_contract])
        .arg("--match-test")
        .arg(format!("^{check}\\("))
        .arg("--solver-timeout-assertion")
        .arg(format!("{}s", opts.solver_timeout))
        .arg("--json-output")
        .arg(&json)
        .env("FOUNDRY_DYNAMIC_TEST_LINKING", "false")
        .env("HALMOS_ALLOW_DOWNLOAD", "1")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .current_dir(repo);
    if let Some(n) = opts.loop_bound {
        cmd.args(["--loop", &n.to_string()]);
    }
    if solver == "ausweg" {
        cmd.arg("--solver-command")
            .arg(format!("{} smt", exe.display()))
            .env(
                "AUSWEG_SMT_TIMEOUT",
                opts.solver_timeout.saturating_sub(5).max(1).to_string(),
            );
    } else {
        cmd.args(["--solver", solver]);
    }
    let forge = Path::new(&opts.forge_bin);
    if let Some(dir) = forge.parent().filter(|d| !d.as_os_str().is_empty()) {
        let path = std::env::var_os("PATH").unwrap_or_default();
        let mut dirs = vec![dir.to_path_buf()];
        dirs.extend(std::env::split_paths(&path));
        cmd.env("PATH", std::env::join_paths(dirs)?);
    }
    own_group(&mut cmd);
    let started = Instant::now();
    let mut child = cmd
        .spawn()
        .with_context(|| format!("running {} (install Halmos: see the README)", opts.halmos))?;
    let cap = std::time::Duration::from_secs(opts.cap);
    loop {
        if child.try_wait()?.is_some() {
            // A solver Halmos left behind would slow the next cell down.
            stop_group(&mut child);
            break;
        }
        if started.elapsed() >= cap {
            stop_group(&mut child);
            let _ = fs::remove_file(&json);
            return Ok(BenchCell {
                solver: solver.to_string(),
                verdict: None,
                seconds: started.elapsed().as_secs_f64(),
            });
        }
        std::thread::sleep(std::time::Duration::from_millis(500));
    }
    let seconds = started.elapsed().as_secs_f64();
    let verdict = fs::read_to_string(&json)
        .ok()
        .and_then(|t| parse_results(&t, test_contract).ok().flatten())
        .and_then(|cs| cs.into_iter().find(|c| c.name == check))
        .map(|c| c.verdict)
        .unwrap_or(Verdict::Error);
    let _ = fs::remove_file(&json);
    Ok(BenchCell {
        solver: solver.to_string(),
        verdict: Some(verdict),
        seconds,
    })
}

/// The same checks, run once per solver.
pub fn bench(
    repo: &Path,
    target: &BenchTarget,
    forge: &dyn Forge,
    opts: &BenchOptions,
) -> Result<BenchReport> {
    let (name, test_contract, test_file, all) = match target {
        BenchTarget::Proof(contract) => {
            let p = prepare(repo, contract, forge, opts.price, opts.bound_amounts)?;
            (
                contract.display().to_string(),
                p.proof_contract,
                p.test_rel,
                p.proof.checks,
            )
        }
        BenchTarget::Suite { file, contract } => {
            let build = forge.build_json(repo)?;
            if !build.ok {
                bail!("the project does not compile:\n{}", build.output);
            }
            let file_name = file
                .file_name()
                .and_then(|f| f.to_str())
                .context("suite path has no file name")?;
            let abi = Abi::load(repo, file_name, contract)?;
            let mut names: Vec<String> = abi
                .items
                .iter()
                .filter(|i| i.is_function())
                .map(|i| i.name.clone())
                .collect();
            names.dedup();
            (
                format!("{}:{contract}", file.display()),
                contract.clone(),
                file.clone(),
                names,
            )
        }
    };
    let checks: Vec<&String> = all.iter().filter(|c| c.starts_with(&opts.checks)).collect();
    if checks.is_empty() {
        bail!("no check starts with {}", opts.checks);
    }
    let mut rows = Vec::new();
    for check in checks {
        let mut cells = Vec::new();
        for solver in &opts.solvers {
            let cell = bench_one(repo, &test_contract, check, solver, opts)?;
            eprintln!("  {} with {solver}: {}", label(check), cell.text());
            cells.push(cell);
        }
        rows.push(BenchRow {
            check: check.clone(),
            cells,
        });
    }
    Ok(BenchReport {
        contract: name,
        test_file: test_file.display().to_string(),
        solver_timeout: opts.solver_timeout,
        cap: opts.cap,
        rows,
    })
}

/// `check_keeps_deposit` -> `keeps deposit`.
pub fn label(check: &str) -> String {
    match check.strip_prefix("check_") {
        Some(rest) => rest.replacen('_', " ", 1),
        None => check.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::OZ_VAULT_ABI;

    #[test]
    fn renders_init_keeps_and_exit_checks() {
        let abi = Abi::parse(OZ_VAULT_ABI).unwrap();
        let p = render("OZVault", "../../src/OZVault.sol", &abi, true, false).unwrap();
        assert!(p.source.contains("contract OZVaultProof is Test"));
        assert!(
            p.source
                .contains("target = new OZVault(IERC20(address(asset)));")
        );
        assert!(p.source.contains(
            "function check_keeps_deposit(uint256 callerI, uint256 assets, uint256 receiverI)"
        ));
        // The call is made in a try: only a call that succeeds is checked.
        assert!(
            p.source
                .contains("try target.deposit(assets, _user(receiverI)) {")
        );
        assert!(
            p.source
                .contains("if (target.totalAssets() < target.totalSupply()) return false;")
        );
        for c in [
            "check_init",
            "check_keeps_deposit",
            "check_exit_redeem",
            "check_exit_withdraw",
        ] {
            assert!(p.checks.iter().any(|n| n == c), "{c}");
        }
        assert!(!p.checks.iter().any(|n| n.contains("permit")));
        assert!(!p.source.contains("assets <= MAX_AMOUNT"));
        assert!(!p.source.contains("makeAddr"));
        let p = render("OZVault", "../../src/OZVault.sol", &abi, false, true).unwrap();
        assert!(
            !p.source
                .contains("if (target.totalAssets() < target.totalSupply()) return false;")
        );
        assert!(
            p.source
                .contains("vm.assume(callerI < 3 && assets <= MAX_AMOUNT && receiverI < 3);")
        );
    }

    #[test]
    fn exit_redeem_takes_the_whole_position() {
        let abi = Abi::parse(OZ_VAULT_ABI).unwrap();
        let p = render("OZVault", "../../src/OZVault.sol", &abi, true, false).unwrap();
        // Every share the user holds, not what maxRedeem quotes, and none left.
        assert!(p.source.contains("uint256 shares = target.balanceOf(u);"));
        assert!(!p.source.contains("target.maxRedeem(u)"));
        assert!(p.source.contains("assert(target.balanceOf(u) == 0);"));
        // A view that reverts fails the check instead of dropping the state.
        for view in [
            "try target.previewRedeem(shares) returns (uint256 p) {",
            "try target.maxWithdraw(u) returns (uint256 a) {",
            "try target.previewWithdraw(assets) returns (uint256 c) {",
        ] {
            assert!(p.source.contains(view), "{view}");
        }
    }

    #[test]
    fn reads_halmos_results_and_names_users() {
        let json = r#"{"exitcode": 1, "test_results": {"test/generated/V.proof.t.sol:VProof": [
            {"name": "check_exit_redeem(uint256)", "exitcode": 1, "num_models": 1,
             "models": [{"model": {
                "p_i_uint256_a_00": {"variable_name": "i", "value": 1},
                "halmos_totalSupply_uint256_b_01": {"variable_name": "totalSupply", "value": 2}}, "is_valid": true}],
             "num_paths": [30, 6, 0], "time": [1.5, 1.4, 0.1], "num_bounded_loops": 0},
            {"name": "check_init()", "exitcode": 0, "num_models": 0, "models": [],
             "num_paths": [1, 1, 0], "time": [0.1, 0.1, 0.0], "num_bounded_loops": 0},
            {"name": "check_keeps_mint(uint256,uint256,uint256)", "exitcode": 2, "models": [],
             "num_paths": [9, 9, 0], "time": [70.0, 1.0, 69.0]}]}}"#;
        let checks = parse_results(json, "VProof").unwrap().unwrap();
        assert_eq!(checks[0].name, "check_exit_redeem");
        assert_eq!(checks[0].verdict, Verdict::Counterexample);
        assert_eq!(
            checks[0].counterexample,
            vec![
                ("i".to_string(), "bob".to_string()),
                ("totalSupply".to_string(), "2".to_string())
            ]
        );
        assert_eq!(checks[1].verdict, Verdict::Proved);
        assert_eq!(checks[2].verdict, Verdict::Timeout);
        assert_eq!(label("check_keeps_mint"), "keeps mint");
        assert!(parse_results(json, "Other").unwrap().is_none());
        let twins = r#"{"test_results":{"test/Old.t.sol:VProof":[{"name":"check_init()","exitcode":1}],"test/generated/V.proof.t.sol:VProof":[{"name":"check_init()","exitcode":0}]}}"#;
        let checks = parse_results(twins, "VProof").unwrap().unwrap();
        assert_eq!(checks[0].verdict, Verdict::Proved);
    }

    #[test]
    fn failure_log_skips_lint_warnings() {
        let log = "warning[solmate-safe-transfer-lib]: the lib\n   │\n56 │  asset.safeTransfer(x);\n   ╰ help: url\nError: compilation failed\n";
        assert_eq!(log_tail(log), "Error: compilation failed");
    }

    #[test]
    fn strips_halmos_colours() {
        assert_eq!(
            strip_ansi("\u{1b}[31m[FAIL]\u{1b}[0m check_exit_redeem(uint256) (paths: 3)"),
            "[FAIL] check_exit_redeem(uint256) (paths: 3)"
        );
    }

    #[test]
    fn reads_bench_suites_and_labels_their_tests() {
        match BenchTarget::suite("test/OZVault.a16z.t.sol:OZVaultA16z").unwrap() {
            BenchTarget::Suite { file, contract } => {
                assert_eq!(file, PathBuf::from("test/OZVault.a16z.t.sol"));
                assert_eq!(contract, "OZVaultA16z");
            }
            BenchTarget::Proof(_) => panic!("expected a suite"),
        }
        assert!(BenchTarget::suite("test/OZVault.a16z.t.sol").is_err());
        assert_eq!(label("test_RT_deposit_redeem"), "test_RT_deposit_redeem");
    }

    /// The bug this prevents: a capped Halmos run killed alone left its
    /// solvers running, and they slowed every later cell down.
    #[cfg(unix)]
    #[test]
    fn stopping_the_group_stops_the_solvers_too() {
        let dir = std::env::temp_dir().join(format!("ausweg-group-test-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        let pid_file = dir.join("pid");
        let mut cmd = Command::new("sh");
        cmd.arg("-c")
            .arg(format!("sleep 30 & echo $! > {}; wait", pid_file.display()));
        own_group(&mut cmd);
        let mut child = cmd.spawn().unwrap();
        let started = Instant::now();
        let pid = loop {
            if let Some(p) = fs::read_to_string(&pid_file)
                .ok()
                .and_then(|t| t.trim().parse::<u32>().ok())
            {
                break p;
            }
            assert!(started.elapsed().as_secs() < 10, "the child never started");
            std::thread::sleep(std::time::Duration::from_millis(20));
        };
        stop_group(&mut child);
        std::thread::sleep(std::time::Duration::from_millis(200));
        // Gone, or a zombie waiting to be reaped: either way no longer running.
        let out = Command::new("ps")
            .args(["-o", "stat=", "-p", &pid.to_string()])
            .output()
            .unwrap();
        let stat = String::from_utf8_lossy(&out.stdout).trim().to_string();
        assert!(
            stat.is_empty() || stat.starts_with('Z'),
            "still running: {stat}"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn refuses_contracts_without_the_vault_functions() {
        let abi = Abi::parse(r#"{"abi":[{"type":"function","name":"deposit","inputs":[],"outputs":[],"stateMutability":"nonpayable"}]}"#).unwrap();
        let e = supports(&abi).unwrap_err().to_string();
        assert!(e.contains("missing asset"), "{e}");
    }
}
