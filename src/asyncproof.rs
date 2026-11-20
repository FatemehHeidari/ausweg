//! Step 15: liquidity for ERC-7540 vaults, whose exits take three calls.
//!
//! A user first calls `requestRedeem`; then the owner calls `fulfillRedeem`, or
//! a delay passes; only then can the user `redeem` or `withdraw`. ausweg
//! proves, from every state the vault can reach:
//! - request: each user can turn all their shares into a request;
//! - fulfil (owner) or mature (delay): their whole request becomes claimable;
//! - claim: they can claim everything claimable and are paid every claimable
//!   asset;
//! - stable: no call by alice (for any other user) or the owner shrinks bob's
//!   request, or, for a delay, pushes back what he can claim;
//! - fair: no call by alice or the owner lowers the share price;
//! - keeps: the invariant is inductive, as in Step 13.
//!
//! The chain is checked for each of the three users. Stable and fair take bob
//! for every user and alice for every other one: the users are interchangeable
//! unless the vault's code singles out an address, since every storage slot is
//! symbolic. The owner fulfilling eventually, or time passing, is the fairness
//! assumption; a user's own steps are their choice, so they only need to succeed.
//!
//! Vaults keep requested shares in different ways: in the vault until the
//! claim, or burned at the request or at the fulfilment, with their assets set
//! aside at one of those moments. ausweg reads which from a concrete run (the
//! probe) before it writes the invariant.
//!
//! Step 16: the probe also reads the vault's own running totals (uint256
//! state variables named `total...`, private ones included) at each step of
//! the request, and learns which request records each one sums; the invariant
//! then pins it to that sum, read from storage. And it reads how the vault
//! prices a share: exactly, or with one virtual share and asset as
//! OpenZeppelin does. Without both, OpenZeppelin's ERC-7540 cannot be proved:
//! its price depends on a private total of claimable shares.

use crate::abi::{Abi, Item, Stored};
use crate::prove::{Proof, ctor_args, ident, typed};
use crate::scaffold;
use anyhow::{Result, bail};
use serde::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Progress {
    /// The owner's `fulfillRedeem(controller, shares)` makes a request claimable.
    Owner,
    /// A request becomes claimable once enough time has passed.
    Time,
}

/// What the probe saw the vault do with a request.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize)]
pub struct Style {
    /// totalSupply drops at the request.
    pub burns_at_request: bool,
    /// totalAssets drops at the request.
    pub reserves_at_request: bool,
    /// totalSupply drops at the fulfilment.
    pub burns_at_fulfil: bool,
    /// totalAssets drops at the fulfilment.
    pub reserves_at_fulfil: bool,
}

/// An ERC-7540 vault with asynchronous redemption, and how its requests become
/// claimable; None for anything else.
pub fn kind(abi: &Abi) -> Option<Progress> {
    let async_redeem = abi.has("requestRedeem", &["uint256", "address", "address"])
        && abi.has("pendingRedeemRequest", &["uint256", "address"])
        && abi.has("claimableRedeemRequest", &["uint256", "address"]);
    if !async_redeem {
        return None;
    }
    Some(if abi.has("fulfillRedeem", &["address", "uint256"]) {
        Progress::Owner
    } else {
        Progress::Time
    })
}

/// What one of the vault's running totals sums over the users, as the probe
/// read it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Counts {
    /// Stays 0, like a deposit-side total when deposits are synchronous.
    Nothing,
    /// Shares of pending requests.
    Pending,
    /// Shares of claimable requests.
    Claimable,
    /// Shares of pending and claimable requests.
    Requested,
    /// Assets owed to claimable requests.
    Owed,
}

const COUNTS: [Counts; 5] = [
    Counts::Nothing,
    Counts::Pending,
    Counts::Claimable,
    Counts::Requested,
    Counts::Owed,
];

impl Counts {
    fn name(self) -> &'static str {
        match self {
            Counts::Nothing => "nothing",
            Counts::Pending => "pending",
            Counts::Claimable => "claimable",
            Counts::Requested => "requested",
            Counts::Owed => "owed",
        }
    }

    /// The total before the request, after it, after the fulfilment and after
    /// the claim, if it sums this record. `paid` is what the claim paid; with
    /// the price moved off 1 first, it differs from the 400 shares requested.
    fn pattern(self) -> &'static str {
        match self {
            Counts::Nothing => "v[0] == 0 && v[1] == 0 && v[2] == 0 && v[3] == 0",
            Counts::Pending => "v[0] == 0 && v[1] == 400 && v[2] == 0 && v[3] == 0",
            Counts::Claimable => {
                "v[0] == 0 && v[1] == 0 && v[2] == 400 && v[3] == 0 && paid != 400"
            }
            Counts::Requested => "v[0] == 0 && v[1] == 400 && v[2] == 400 && v[3] == 0",
            Counts::Owed => "v[0] == 0 && v[1] == 0 && v[2] == paid && v[3] == 0 && paid != 400",
        }
    }

    fn uses_paid(self) -> bool {
        matches!(self, Counts::Claimable | Counts::Owed)
    }

    /// The sum, in the names the proof's `_requests()` returns.
    fn sum(self) -> &'static str {
        match self {
            Counts::Nothing => "0",
            Counts::Pending => "pending",
            Counts::Claimable => "claimS",
            Counts::Requested => "pending + claimS",
            Counts::Owed => "owed",
        }
    }

    pub fn describe(self) -> &'static str {
        match self {
            Counts::Nothing => "stays 0",
            Counts::Pending => "shares of pending requests",
            Counts::Claimable => "shares of claimable requests",
            Counts::Requested => "shares of pending and claimable requests",
            Counts::Owed => "assets owed to claimable requests",
        }
    }
}

/// A running total of the vault, and what it sums.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Total {
    pub label: String,
    pub slot: String,
    pub counts: Counts,
}

/// How the vault prices a share, as the probe read it.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum PriceRule {
    /// totalAssets / shares, as Solmate prices.
    #[default]
    Exact,
    /// (totalAssets + 1) / (shares + 1): one virtual share and one virtual
    /// asset, as OpenZeppelin and Solady price with no decimals offset.
    Virtual,
}

impl PriceRule {
    pub fn describe(self) -> &'static str {
        match self {
            PriceRule::Exact => "totalAssets / shares",
            PriceRule::Virtual => "(totalAssets + 1) / (shares + 1)",
        }
    }
}

/// What the probe read besides the style.
#[derive(Debug, Clone, Default, PartialEq, Serialize)]
pub struct Learned {
    pub totals: Vec<Total>,
    pub price: PriceRule,
    /// Totals whose walk matched no record, or more than one: the invariant
    /// leaves them out.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub unread: Vec<String>,
    /// Totals that stayed 0 through the walk but are not named for requests,
    /// like a `totalFees` the walk never touches: pinning one to 0 would make a
    /// keeps check fail as soon as a call raises it, so the invariant leaves
    /// them out.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub idle: Vec<String>,
}

/// Whether a total's name says it is about requests, as a deposit-side total
/// that stays 0 in a vault with synchronous deposits is
/// (`_totalPendingDepositAssets`).
fn about_requests(label: &str) -> bool {
    let l = label.to_ascii_lowercase();
    ["pending", "claimable", "request", "queue"]
        .iter()
        .any(|w| l.contains(w))
}

fn total_test(slot: &str, c: Counts) -> String {
    format!("test_ausweg_total_{slot}_{}", c.name())
}

const PROBE_PRICE_EXACT: &str = "test_ausweg_price_exact";
const PROBE_PRICE_VIRTUAL: &str = "test_ausweg_price_virtual";

/// What the probe's passing tests say about the totals and the price.
pub fn learned_from(passed: &[String], stored: &[Stored]) -> Learned {
    let p = |n: &str| passed.iter().any(|t| t == n);
    let mut l = Learned::default();
    for s in stored {
        let hits: Vec<Counts> = COUNTS
            .into_iter()
            .filter(|c| p(&total_test(&s.slot, *c)))
            .collect();
        match hits.as_slice() {
            [Counts::Nothing] if !about_requests(&s.label) => l.idle.push(s.label.clone()),
            [c] => l.totals.push(Total {
                label: s.label.clone(),
                slot: s.slot.clone(),
                counts: *c,
            }),
            _ => l.unread.push(s.label.clone()),
        }
    }
    if p(PROBE_PRICE_VIRTUAL) && !p(PROBE_PRICE_EXACT) {
        l.price = PriceRule::Virtual;
    }
    l
}

const NEEDED: &[&str] = &[
    "asset",
    "totalAssets",
    "totalSupply",
    "balanceOf",
    "allowance",
    "approve",
    "deposit",
    "redeem",
    "withdraw",
    "maxWithdraw",
    "maxRedeem",
    "isOperator",
    "owner",
];

pub fn supports(abi: &Abi) -> Result<()> {
    let missing: Vec<&str> = NEEDED
        .iter()
        .copied()
        .filter(|n| !abi.items.iter().any(|i| i.is_function() && i.name == *n))
        .collect();
    if !missing.is_empty() {
        bail!(
            "not an ERC-7540 vault ausweg can prove: missing {}",
            missing.join(", ")
        );
    }
    // ERC-7540 leaves the owner's fulfilment to each vault. Without the one
    // ausweg calls, a vault with another would be taken for one whose
    // requests mature with time, and the probe would wait ten years for nothing.
    let fulfils = other_fulfils(abi);
    if !fulfils.is_empty() {
        bail!(
            "the vault fulfils requests with {}, but ausweg calls fulfillRedeem(address controller, \
             uint256 shares); wrap the vault with that function, calling yours",
            fulfils.join(", ")
        );
    }
    Ok(())
}

/// State-changing functions named like a fulfilment (`fulfil…`, `fulfill…`)
/// when the vault has no `fulfillRedeem(address, uint256)`.
fn other_fulfils(abi: &Abi) -> Vec<String> {
    if abi.has("fulfillRedeem", &["address", "uint256"]) {
        return Vec::new();
    }
    abi.mutating()
        .into_iter()
        .filter(|i| i.name.to_ascii_lowercase().starts_with("fulfil"))
        .map(crate::prove::short_signature)
        .collect()
}

/// Whether `requestRedeem` returns its request id, which the probe then reads.
fn returns_request_id(abi: &Abi) -> bool {
    abi.items.iter().any(|i| {
        i.is_function()
            && i.name == "requestRedeem"
            && i.inputs
                .iter()
                .map(|p| p.ty.as_str())
                .eq(["uint256", "address", "address"])
            && i.outputs.len() == 1
            && i.outputs[0].ty == "uint256"
    })
}

pub const PROBE_RUNS: &str = "test_ausweg_runs";
/// Passes when the vault gives a request the id 0: ausweg reads requests there.
pub const PROBE_ID_ZERO: &str = "test_ausweg_request_id_zero";
const PROBE_BURNS_AT_REQUEST: &str = "test_ausweg_burns_at_request";
const PROBE_RESERVES_AT_REQUEST: &str = "test_ausweg_reserves_at_request";
const PROBE_BURNS_AT_FULFIL: &str = "test_ausweg_burns_at_fulfil";
const PROBE_RESERVES_AT_FULFIL: &str = "test_ausweg_reserves_at_fulfil";

pub fn probe_file(contract: &str) -> String {
    format!("{contract}.style.t.sol")
}

/// A forge test that walks one request through the vault; each test function
/// checks one thing the vault might do, and passes when it does. `stored` are
/// the vault's running totals; the probe reads them for owner-fulfilled
/// vaults.
pub fn probe_source(
    contract: &str,
    import_path: &str,
    abi: &Abi,
    progress: Progress,
    stored: &[Stored],
) -> Result<String> {
    let (ctor, passive) = ctor_args(abi)?;
    if !passive.is_empty() {
        bail!("ausweg's ERC-7540 proof supports no constructor addresses besides the asset");
    }
    let step = match progress {
        Progress::Owner => "        target.fulfillRedeem(alice, 400);\n",
        Progress::Time => "        vm.warp(block.timestamp + 3650 days);\n",
    };
    let mut extra = String::new();
    if returns_request_id(abi) {
        extra.push_str(&PROBE_ID.replace("@ID@", PROBE_ID_ZERO));
    }
    if abi.has("convertToShares", &["uint256"]) {
        extra.push_str(
            &PROBE_PRICE
                .replace("@EXACT@", PROBE_PRICE_EXACT)
                .replace("@VIRTUAL@", PROBE_PRICE_VIRTUAL),
        );
    }
    if progress == Progress::Owner && !stored.is_empty() {
        extra.push_str(PROBE_WALK);
        for s in stored {
            for c in COUNTS {
                let bind = if c.uses_paid() {
                    "(uint256[4] memory v, uint256 paid)"
                } else {
                    "(uint256[4] memory v,)"
                };
                extra.push_str(&format!(
                    "\n    /// {label}: {what}?\n    function {name}() public {{\n        {bind} = _walk({slot});\n        assertTrue({pattern});\n    }}\n",
                    label = s.label,
                    what = c.describe(),
                    name = total_test(&s.slot, c),
                    slot = s.slot,
                    pattern = c.pattern(),
                ));
            }
        }
    }
    Ok(TEMPLATE_PROBE
        .replace("@EXTRA@", &extra)
        .replace("@C@", contract)
        .replace("@IMPORT@", import_path)
        .replace("@TOKEN@", scaffold::TOKEN_FILE)
        .replace("@CTOR@", &ctor)
        .replace("@STEP@", step)
        .replace("@RUNS@", PROBE_RUNS)
        .replace("@BURNS_AT_REQUEST@", PROBE_BURNS_AT_REQUEST)
        .replace("@RESERVES_AT_REQUEST@", PROBE_RESERVES_AT_REQUEST)
        .replace("@BURNS_AT_FULFIL@", PROBE_BURNS_AT_FULFIL)
        .replace("@RESERVES_AT_FULFIL@", PROBE_RESERVES_AT_FULFIL))
}

/// The style from the probe tests that passed.
pub fn style_from(passed: &[String]) -> Style {
    let p = |n: &str| passed.iter().any(|t| t == n);
    Style {
        burns_at_request: p(PROBE_BURNS_AT_REQUEST),
        reserves_at_request: p(PROBE_RESERVES_AT_REQUEST),
        burns_at_fulfil: p(PROBE_BURNS_AT_FULFIL),
        reserves_at_fulfil: p(PROBE_RESERVES_AT_FULFIL),
    }
}

impl Style {
    /// One line for the report: where a request's shares and assets go.
    pub fn describe(&self, progress: Progress) -> String {
        let shares = if self.burns_at_request {
            "burned at the request"
        } else if self.burns_at_fulfil {
            match progress {
                Progress::Owner => "burned at the fulfilment",
                Progress::Time => "burned once claimable",
            }
        } else {
            "held by the vault until the claim"
        };
        let assets = if self.reserves_at_request {
            "set aside at the request"
        } else if self.reserves_at_fulfil {
            "set aside at the fulfilment"
        } else {
            "counted in totalAssets until the claim"
        };
        format!("requested shares {shares}; their assets {assets}")
    }
}

/// Calls the checks leave out: signatures, and changes of owner (the fairness
/// assumption is about whoever owns the vault).
const SKIP: &[(&str, &str)] = &[
    ("permit", "needs a signature"),
    ("authorizeOperator", "needs a signature"),
    ("transferOwnership", "changes the owner"),
    ("renounceOwnership", "changes the owner"),
    ("acceptOwnership", "changes the owner"),
];

/// One generated check per family for a vault function.
struct Call {
    params: Vec<String>,
    assumes: Vec<String>,
    call: String,
}

fn call(item: &Item, bound: bool) -> Option<Call> {
    let mut params = Vec::new();
    let mut assumes = Vec::new();
    let mut args = Vec::new();
    let mut taken: Vec<String> = vec!["callerI".into(), "caller".into()];
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
    Some(Call {
        params,
        assumes,
        call: format!("target.{}({})", item.name, args.join(", ")),
    })
}

fn signature_params(first: &str, c: &Call) -> String {
    let mut all = vec![first.to_string()];
    all.extend(c.params.iter().cloned());
    all.join(", ")
}

fn assumes(first: &str, c: &Call) -> String {
    let mut all = vec![first.to_string()];
    all.extend(c.assumes.iter().cloned());
    all.join(" && ")
}

fn unique(checks: &[String], base: String) -> String {
    let mut name = base.clone();
    let mut k = 2;
    while checks.contains(&name) {
        name = format!("{base}_{k}");
        k += 1;
    }
    name
}

/// The proof: the chain, then keeps, stable and fair checks for every
/// state-changing function of the vault.
#[allow(clippy::too_many_arguments)]
pub fn render(
    contract: &str,
    import_path: &str,
    abi: &Abi,
    progress: Progress,
    style: Style,
    learned: &Learned,
    price: bool,
    bound: bool,
) -> Result<Proof> {
    supports(abi)?;
    let (ctor, passive) = ctor_args(abi)?;
    if !passive.is_empty() {
        bail!("ausweg's ERC-7540 proof supports no constructor addresses besides the asset");
    }
    if progress == Progress::Owner && style.reserves_at_request {
        bail!(
            "this vault sets assets aside at the request but needs the owner to fulfil it; ausweg's proof does not cover that accounting yet"
        );
    }
    let timed = progress == Progress::Time;
    let any_time = if timed { "        _anyTime();\n" } else { "" };

    let mut checks: Vec<String> = vec!["check_init".into(), "check_request".into()];
    checks.push(
        if timed {
            "check_mature"
        } else {
            "check_fulfil"
        }
        .into(),
    );
    checks.push("check_claim_redeem".into());
    checks.push("check_claim_withdraw".into());

    let mut keeps = String::new();
    let mut stable = String::new();
    let mut fair = String::new();
    let mut got: Vec<String> = Vec::new();
    for item in abi.mutating() {
        if SKIP.iter().any(|(n, _)| *n == item.name) {
            continue;
        }
        let Some(c) = call(item, bound) else {
            continue;
        };
        got.push(crate::prove::short_signature(item));
        let k = unique(&checks, format!("check_keeps_{}", item.name));
        keeps.push_str(&format!(
            "    /// {sig}: keeps the invariant, for any user or the owner as caller.\n    function {k}({ps}) public {{\n        vm.assume({asm});\n{any_time}        vm.assume(_inv());\n        _witness();\n        vm.prank(_caller(callerI));\n        try {call} {{\n            assert(_holds());\n        }} catch {{}}\n    }}\n\n",
            sig = item.signature(),
            ps = signature_params("uint256 callerI", &c),
            asm = assumes("callerI < 4", &c),
            call = c.call,
        ));
        checks.push(k);
        let s = unique(&checks, format!("check_stable_{}", item.name));
        stable.push_str(&format!(
            "    /// {sig}: called by alice or the owner, it leaves bob's request whole.\n    function {s}({ps}) public {{\n        vm.assume({asm});\n        address caller = _other(callerI);\n{any_time}        vm.assume(_inv());\n        _noDelegation(caller);\n        Request memory r = _requestOf();\n        vm.prank(caller);\n        try {call} {{\n            _stable(r);\n        }} catch {{}}\n    }}\n\n",
            sig = item.signature(),
            ps = signature_params("uint256 callerI", &c),
            asm = assumes("(callerI == 0 || callerI == 3)", &c),
            call = c.call,
        ));
        checks.push(s);
        let f = unique(&checks, format!("check_fair_{}", item.name));
        fair.push_str(&format!(
            "    /// {sig}: called by alice or the owner, it does not lower the share price.\n    function {f}({ps}) public {{\n        vm.assume({asm});\n        address caller = _other(callerI);\n{any_time}        vm.assume(_sized());\n        _witness();\n        _noDelegation(caller);\n        Price memory p = _price();\n        vm.prank(caller);\n        try {call} {{\n            _fair(p);\n        }} catch {{}}\n    }}\n\n",
            sig = item.signature(),
            ps = signature_params("uint256 callerI", &c),
            asm = assumes("(callerI == 0 || callerI == 3)", &c),
            call = c.call,
        ));
        checks.push(f);
    }
    let (left_out, unchecked) = crate::prove::coverage(abi, SKIP, &|item| {
        got.contains(&crate::prove::short_signature(item))
    });
    for n in [
        "check_keeps_asset_transfer",
        "check_keeps_asset_transferFrom",
        "check_keeps_asset_approve",
        "check_keeps_asset_mint",
    ] {
        checks.push(n.into());
    }
    if timed {
        checks.push("check_keeps_time".into());
    }

    let bound_amount = |v: &str| {
        if bound {
            format!(" && {v} <= MAX_AMOUNT")
        } else {
            String::new()
        }
    };

    // Where the vault keeps a request's shares and assets, phase by phase.
    let held_pending = !style.burns_at_request;
    let held_claimable = !style.burns_at_request && !style.burns_at_fulfil;
    // Burned at the request, but their assets stay in totalAssets until the
    // fulfilment: pending shares still share in gains and losses, so the
    // price counts them.
    let pool_pending = !timed && style.burns_at_request && !style.reserves_at_request;
    let totals = if timed { &[][..] } else { &learned.totals[..] };
    let uses = |cs: &[Counts]| totals.iter().any(|t| cs.contains(&t.counts));
    let sum_pending = held_pending || pool_pending || uses(&[Counts::Pending, Counts::Requested]);
    let sum_claimable = held_claimable || uses(&[Counts::Claimable, Counts::Requested]);
    let totals_ok = if totals.is_empty() {
        String::new()
    } else {
        let mut body = String::new();
        for t in totals {
            body.push_str(&format!(
                "        // {label}: {what}.\n        if (_stored({slot}) > 8 * CAP || _stored({slot}) != {sum}) return false;\n",
                label = t.label,
                what = t.counts.describe(),
                slot = t.slot,
                sum = t.counts.sum(),
            ));
        }
        // Name only the parameters a line uses, so solc warns about nothing.
        let param = |name: &str, used: bool| {
            if used {
                format!("uint256 {name}")
            } else {
                "uint256".to_string()
            }
        };
        let params = [
            param("pending", uses(&[Counts::Pending, Counts::Requested])),
            param("claimS", uses(&[Counts::Claimable, Counts::Requested])),
            param("owed", uses(&[Counts::Owed])),
        ];
        TOTALS_FNS
            .replace("@PARAMS@", &params.join(", "))
            .replace("@TOTALS@", &body)
    };
    let inv_totals = if totals.is_empty() {
        ""
    } else {
        "        if (!_totalsOk(pending, claimS, owed)) return false;\n"
    };
    let sized_extra = match (totals.is_empty(), pool_pending) {
        (true, false) => "",
        (true, true) => {
            "        (bool requestsOk,,,) = _requests();\n        if (!requestsOk || _shares() > CAP) return false;\n"
        }
        (false, _) => {
            "        (bool requestsOk, uint256 pending, uint256 claimS, uint256 owed) = _requests();\n        if (!requestsOk || _shares() > CAP) return false;\n        if (!_totalsOk(pending, claimS, owed)) return false;\n"
        }
    };
    let mut learned_lines = String::new();
    if !totals.is_empty() {
        let list: Vec<String> = totals
            .iter()
            .map(|t| format!("{} ({})", t.label, t.counts.describe()))
            .collect();
        learned_lines.push_str(&format!(
            "// Its running totals, read from storage, each pinned to a sum over the\n// users: {}.\n",
            list.join("; ")
        ));
    }
    learned_lines.push_str(&format!(
        "// Its share price: {}{}.\n",
        learned.price.describe(),
        if pool_pending {
            ", where the shares include pending requests' burned shares until the fulfilment"
        } else {
            ""
        }
    ));
    let shares_eq = match (held_pending, held_claimable) {
        // A timed vault's sums are read when every request is claimable.
        _ if timed && held_pending => "claimS",
        (true, true) => "pending + claimS",
        (true, false) => "pending",
        (false, _) => "0",
    };
    let reserved = if timed {
        if style.reserves_at_request || style.reserves_at_fulfil {
            "owed"
        } else {
            "0"
        }
    } else if style.reserves_at_fulfil {
        "owed"
    } else {
        "0"
    };

    let chain = if timed { CHAIN_TIME } else { CHAIN_OWNER };
    let stable_fns = if timed { STABLE_TIME } else { STABLE_OWNER };
    let view = if timed { "" } else { " view" };
    let owed_fn = if timed { OWED_LATER } else { OWED_NOW };
    let time_helpers = if timed { TIME_HELPERS } else { "" };
    let keeps_time = if timed { KEEPS_TIME } else { "" };
    let progress_line = match progress {
        Progress::Owner => {
            "// The owner (this test contract) fulfils requests; it is assumed to do so\n// eventually. That is the only trust placed in it."
        }
        Progress::Time => {
            "// Requests become claimable once a delay passes; time passing is the\n// fairness assumption."
        }
    };

    let source = TEMPLATE
        .replace("@CHAIN@", chain)
        .replace("@STABLE_FNS@", stable_fns)
        .replace("@TIME_HELPERS@", time_helpers)
        .replace("@KEEPS_TIME@", keeps_time)
        .replace("@OWED_FN@", owed_fn)
        .replace(
            "@REQUESTS@",
            if timed { REQUESTS_TIME } else { REQUESTS_OWNER },
        )
        .replace("@KEEPS@", &keeps)
        .replace("@STABLE@", &stable)
        .replace("@FAIR@", &fair)
        .replace("@TOTALS_FNS@", &totals_ok)
        .replace("@INV_TOTALS@", inv_totals)
        .replace("@SIZED_EXTRA@", sized_extra)
        .replace("@LEARNED_LINES@", &learned_lines)
        .replace("@SUM_PENDING@", if sum_pending { "true" } else { "false" })
        .replace(
            "@SUM_CLAIMABLE@",
            if sum_claimable { "true" } else { "false" },
        )
        .replace(
            "@POOL_PENDING@",
            if pool_pending { "true" } else { "false" },
        )
        .replace(
            "@BACKED@",
            if sum_claimable && !held_claimable && price {
                "true"
            } else {
                "false"
            },
        )
        .replace(
            "@VIRTUAL@",
            match learned.price {
                PriceRule::Exact => "0",
                PriceRule::Virtual => "1",
            },
        )
        .replace("@VIEW@", view)
        .replace("@ANY_TIME@", any_time)
        .replace("@C@", contract)
        .replace("@IMPORT@", import_path)
        .replace("@TOKEN@", scaffold::TOKEN_FILE)
        .replace("@CTOR@", &ctor)
        .replace("@PROGRESS_LINE@", progress_line)
        .replace("@STYLE_LINE@", &style.describe(progress))
        .replace("@SHARES_EQ@", shares_eq)
        .replace("@RESERVED@", reserved)
        .replace(
            "@HELD_PENDING@",
            if held_pending { "true" } else { "false" },
        )
        .replace(
            "@HELD_CLAIMABLE@",
            if held_claimable { "true" } else { "false" },
        )
        .replace(
            "@PRICE@",
            if price {
                "        if (target.totalAssets() < _shares()) return false;\n"
            } else {
                ""
            },
        )
        .replace("@B_AMOUNT@", &bound_amount("amount"));
    Ok(Proof {
        source,
        checks,
        left_out,
        unchecked,
        other_holders: Vec::new(),
        exit: None,
    })
}

const TEMPLATE_PROBE: &str = r#"// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Written by ausweg (Step 15): one request walked through the vault. Each test
// checks one thing the vault might do with it; ausweg reads which pass to write
// the proof's invariant.

import {Test} from "forge-std/Test.sol";
import "@IMPORT@";
import {AuswegToken} from "./@TOKEN@";

contract @C@Style is Test {
    address internal constant alice = address(0xA11CE);
    AuswegToken internal asset;
    @C@ internal target;

    function setUp() public {
        asset = new AuswegToken();
        target = new @C@(@CTOR@);
        asset.mint(alice, 1000);
        vm.startPrank(alice);
        asset.approve(address(target), 1000);
        target.deposit(1000, alice);
        target.approve(address(target), type(uint256).max);
        vm.stopPrank();
    }

    function _request() internal {
        vm.prank(alice);
        target.requestRedeem(400, alice, alice);
    }

    function _progress() internal {
@STEP@    }

    function @RUNS@() public {
        _request();
        _progress();
        assertGt(target.claimableRedeemRequest(0, alice), 0);
    }

    function @BURNS_AT_REQUEST@() public {
        uint256 s = target.totalSupply();
        _request();
        assertLt(target.totalSupply(), s);
    }

    function @RESERVES_AT_REQUEST@() public {
        uint256 a = target.totalAssets();
        _request();
        assertLt(target.totalAssets(), a);
    }

    function @BURNS_AT_FULFIL@() public {
        _request();
        uint256 s = target.totalSupply();
        _progress();
        assertLt(target.totalSupply(), s);
    }

    function @RESERVES_AT_FULFIL@() public {
        _request();
        uint256 a = target.totalAssets();
        _progress();
        assertLt(target.totalAssets(), a);
    }
@EXTRA@}
"#;

const PROBE_ID: &str = r#"
    /// ausweg reads every request at id 0: one request per controller, as in
    /// ERC-7540's controller-only requests.
    function @ID@() public {
        vm.prank(alice);
        uint256 id = target.requestRedeem(400, alice, alice);
        assertEq(id, 0);
    }
"#;

const PROBE_PRICE: &str = r#"
    /// Yield moves the share price off 1; then the vault prices 10^24 assets.
    function _priced() internal returns (uint256 a, uint256 s, uint256 got) {
        asset.mint(address(target), 1000);
        a = target.totalAssets();
        s = target.totalSupply();
        got = target.convertToShares(1e24);
    }

    /// Priced exactly: totalAssets / totalSupply.
    function @EXACT@() public {
        (uint256 a, uint256 s, uint256 got) = _priced();
        assertEq(got, 1e24 * s / a);
    }

    /// Priced with one virtual share and one virtual asset.
    function @VIRTUAL@() public {
        (uint256 a, uint256 s, uint256 got) = _priced();
        assertEq(got, 1e24 * (s + 1) / (a + 1));
    }
"#;

const PROBE_WALK: &str = r#"
    function _stored(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(address(target), bytes32(slot)));
    }

    /// The request walked through once more, reading a total before it, after
    /// it, after the fulfilment and after the claim. Yield first moves the
    /// share price off 1, so the claim pays a number of assets other than 400.
    function _walk(uint256 slot) internal returns (uint256[4] memory v, uint256 paid) {
        asset.mint(address(target), 1000);
        v[0] = _stored(slot);
        _request();
        v[1] = _stored(slot);
        _progress();
        v[2] = _stored(slot);
        uint256 c = target.claimableRedeemRequest(0, alice);
        vm.prank(alice);
        paid = target.redeem(c, alice, alice);
        v[3] = _stored(slot);
    }
"#;

const TEMPLATE: &str = r#"// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Written by ausweg (Step 15): a Halmos proof that every user can always get out
// of an ERC-7540 vault, whose exits take three calls. Run with `ausweg prove`.
//
// World: alice, bob and carol act; the owner acts too but holds nothing;
// nobody else holds anything.
@PROGRESS_LINE@
// The vault, as the probe saw it: @STYLE_LINE@.
@LEARNED_LINES@//
// The chain, each link proved for each user from any state that satisfies _inv():
//   check_request: the user can turn all their shares into a request;
//   check_fulfil / check_mature: their whole request becomes claimable;
//   check_claim_*: they can claim everything claimable and are paid for it.
// check_stable_*: no call by alice (for any other user) or the owner shrinks bob's
//   request. check_fair_*: none lowers the share price. These two take bob for
//   every user and alice for every other one, and assume no delegation: the
//   caller has no allowance or operator rights over bob's shares.
// check_keeps_*: the invariant is inductive.
// Each check makes its call in a try: a call that reverts changes nothing, so
// only a call that succeeds is checked, and a check is vacuous only when its
// assumptions leave no state at all.

import {Test} from "forge-std/Test.sol";
import "@IMPORT@";
import {AuswegToken} from "./@TOKEN@";

interface AuswegSVM {
    function enableSymbolicStorage(address) external;
    function createUint256(string memory) external returns (uint256);
}

contract @C@Proof is Test {
    AuswegSVM internal constant svm = AuswegSVM(address(uint160(uint256(keccak256("svm cheat code")))));
    uint256 internal constant CAP = 2 ** 96;
    // Amount arguments are limited to this with --bound-amounts.
    uint256 internal constant MAX_AMOUNT = 2 ** 128;
    address internal constant alice = address(0xA11CE);
    address internal constant bob = address(0xB0B);
    address internal constant carol = address(0xCA201);
    // Shares of pending and of claimable requests are still held by the vault.
    bool internal constant HELD_PENDING = @HELD_PENDING@;
    bool internal constant HELD_CLAIMABLE = @HELD_CLAIMABLE@;
    // The invariant sums these request records over the users.
    bool internal constant SUM_PENDING = @SUM_PENDING@;
    bool internal constant SUM_CLAIMABLE = @SUM_CLAIMABLE@;
    // Pending requests' shares are burned, but share in gains and losses until
    // the fulfilment: the price counts them.
    bool internal constant POOL_PENDING = @POOL_PENDING@;
    // Each burned claimable request is owed at least its shares in assets.
    bool internal constant BACKED = @BACKED@;
    // The vault prices a share at (totalAssets + VIRTUAL) / (shares + VIRTUAL).
    uint256 internal constant VIRTUAL = @VIRTUAL@;
    AuswegToken internal asset;
    @C@ internal target;

    struct Request {
        uint256 shares;
        uint256 now_;
        uint256 owed;
    }

    struct Price {
        uint256 assets;
        uint256 shares;
        uint256 held;
    }

    // Any state at all: Halmos makes every storage slot of both contracts symbolic.
    function setUp() public {
        asset = new AuswegToken();
        target = new @C@(@CTOR@);
        svm.enableSymbolicStorage(address(asset));
        svm.enableSymbolicStorage(address(target));
    }

    function _user(uint256 i) internal pure returns (address) {
        return i == 0 ? alice : i == 1 ? bob : carol;
    }

    function _holder(uint256 i) internal view returns (address) {
        return i < 3 ? _user(i) : address(target);
    }

    /// The three users, or the owner (this contract).
    function _caller(uint256 i) internal view returns (address) {
        return i < 3 ? _user(i) : address(this);
    }

    /// Who acts against bob: alice (0, for any other user), or the owner (3).
    function _other(uint256 i) internal view returns (address) {
        return i == 0 ? alice : address(this);
    }
@TIME_HELPERS@
    function _pending(address u) internal view returns (uint256) {
        return target.pendingRedeemRequest(0, u);
    }

    function _claimable(address u) internal view returns (uint256) {
        return target.claimableRedeemRequest(0, u);
    }
@OWED_FN@
    function _assetsClosed() internal view returns (bool ok, uint256 held) {
        uint256 supply = asset.totalSupply();
        uint256 a0 = asset.balanceOf(alice);
        uint256 a1 = asset.balanceOf(bob);
        uint256 a2 = asset.balanceOf(carol);
        held = asset.balanceOf(address(target));
        ok = supply <= CAP && a0 <= CAP && a1 <= CAP && a2 <= CAP && held <= CAP && a0 + a1 + a2 + held == supply;
    }

    function _sharesClosed() internal view returns (bool ok, uint256 held) {
        uint256 s0 = target.balanceOf(alice);
        uint256 s1 = target.balanceOf(bob);
        uint256 s2 = target.balanceOf(carol);
        held = target.balanceOf(address(target));
        ok = s0 <= CAP && s1 <= CAP && s2 <= CAP && held <= CAP && s0 + s1 + s2 + held == target.totalSupply();
    }

@REQUESTS@
    function _inv() internal@VIEW@ returns (bool) {
        // The owner (this contract) fulfils requests but holds nothing.
        if (target.owner() != address(this)) return false;
        if (asset.balanceOf(address(this)) != 0 || target.balanceOf(address(this)) != 0) return false;
        (bool assetsOk, uint256 vaultAssets) = _assetsClosed();
        if (!assetsOk) return false;
        (bool sharesOk, uint256 vaultShares) = _sharesClosed();
        if (!sharesOk) return false;
        (bool requestsOk, uint256 pending, uint256 claimS, uint256 owed) = _requests();
        if (!requestsOk) return false;
@INV_TOTALS@        // Every claim is backed by assets the vault holds.
        if (owed > vaultAssets) return false;
        // The vault holds exactly the shares of the requests it keeps, and sets
        // aside exactly the assets it owes for them.
        if (vaultShares != @SHARES_EQ@) return false;
        if (target.totalAssets() + @RESERVED@ != vaultAssets) return false;
@PRICE@        return true;
    }

    /// The invariant, called from outside so that a revert can be caught.
    function auswegInvariant() external@VIEW@ returns (bool) {
        return _inv();
    }

    /// Whether the invariant holds after a call. A view that reverts counts
    /// as breaking it: Halmos drops a path that reverts, so asserting _inv()
    /// directly would skip any state where, say, totalAssets() underflows.
    function _holds() internal@VIEW@ returns (bool) {
        try this.auswegInvariant() returns (bool ok) {
            return ok;
        } catch {
            return false;
        }
    }

    /// The shares the price is spread over: the supply, plus pending
    /// requests' shares while they are burned but not yet fulfilled.
    function _shares() internal view returns (uint256 s) {
        s = target.totalSupply();
        if (POOL_PENDING) s += _pending(alice) + _pending(bob) + _pending(carol);
    }
@TOTALS_FNS@
    // Names for a counterexample's numbers.
    function _witness() internal {
        vm.assume(target.totalSupply() == svm.createUint256("totalSupply"));
        vm.assume(target.totalAssets() == svm.createUint256("totalAssets"));
    }

    /// Bob has given the other party no allowance and made it no operator.
    function _noDelegation(address other) internal view {
        vm.assume(target.allowance(bob, other) == 0);
        vm.assume(!target.isOperator(bob, other));
    }

    function check_init() public {
        asset = new AuswegToken();
        target = new @C@(@CTOR@);
        assert(_holds());
    }

    /// User i can turn all their shares into a request, keeping the one they had.
    function check_request(uint256 i) public {
        vm.assume(i < 3);
        address u = _user(i);
@ANY_TIME@        vm.assume(_inv());
        _witness();
        uint256 s = target.balanceOf(u);
        vm.assume(s == svm.createUint256("userShares"));
        vm.assume(s > 0);
        uint256 before = _pending(u) + _claimable(u);
        // Records of up to 2^96 shares, the supply cap.
        vm.assume(before <= CAP);
        vm.startPrank(u);
        target.approve(address(target), s);
        try target.requestRedeem(s, u, u) {
            assert(_pending(u) + _claimable(u) == before + s);
        } catch {
            assert(false);
        }
        vm.stopPrank();
    }
@CHAIN@
    /// User i can redeem everything claimable, and is paid every claimable asset.
    function check_claim_redeem(uint256 i) public {
        vm.assume(i < 3);
        address u = _user(i);
@ANY_TIME@        vm.assume(_inv());
        _witness();
        uint256 c = _claimable(u);
        vm.assume(c == svm.createUint256("userClaimable"));
        vm.assume(c > 0 && c <= CAP);
        uint256 owed = target.maxWithdraw(u);
        uint256 before = asset.balanceOf(u);
        vm.prank(u);
        try target.redeem(c, u, u) returns (uint256 paid) {
            assert(paid >= owed);
            assert(asset.balanceOf(u) == before + paid);
        } catch {
            assert(false);
        }
    }

    /// User i can withdraw every claimable asset.
    function check_claim_withdraw(uint256 i) public {
        vm.assume(i < 3);
        address u = _user(i);
@ANY_TIME@        vm.assume(_inv());
        _witness();
        uint256 owed = target.maxWithdraw(u);
        vm.assume(owed == svm.createUint256("userClaimableAssets"));
        vm.assume(owed > 0 && _claimable(u) <= CAP);
        uint256 before = asset.balanceOf(u);
        vm.prank(u);
        try target.withdraw(owed, u, u) {
            assert(asset.balanceOf(u) == before + owed);
        } catch {
            assert(false);
        }
    }

@KEEPS@    /// The asset token moves between holders, the vault included: a donation.
    function check_keeps_asset_transfer(uint256 callerI, uint256 toI, uint256 amount) public {
        vm.assume(callerI < 3 && toI < 4@B_AMOUNT@);
@ANY_TIME@        vm.assume(_inv());
        _witness();
        vm.prank(_user(callerI));
        asset.transfer(_holder(toI), amount);
        assert(_holds());
    }

    function check_keeps_asset_transferFrom(uint256 callerI, uint256 fromI, uint256 toI, uint256 amount) public {
        vm.assume(callerI < 3 && fromI < 3 && toI < 4@B_AMOUNT@);
@ANY_TIME@        vm.assume(_inv());
        _witness();
        vm.prank(_user(callerI));
        asset.transferFrom(_user(fromI), _holder(toI), amount);
        assert(_holds());
    }

    function check_keeps_asset_approve(uint256 callerI, uint256 spenderI, uint256 amount) public {
        vm.assume(callerI < 3 && spenderI < 4@B_AMOUNT@);
@ANY_TIME@        vm.assume(_inv());
        vm.prank(_user(callerI));
        asset.approve(_holder(spenderI), amount);
        assert(_holds());
    }

    /// New asset tokens, to a user or to the vault (yield), up to the supply cap.
    function check_keeps_asset_mint(uint256 toI, uint256 amount) public {
        vm.assume(toI < 4);
@ANY_TIME@        vm.assume(_inv());
        _witness();
        vm.assume(amount <= CAP && asset.totalSupply() + amount <= CAP);
        asset.mint(_holder(toI), amount);
        assert(_holds());
    }
@KEEPS_TIME@
@STABLE_FNS@
@STABLE@    // No call by anyone else lowers the share price, so bob's shares keep
    // their value. Checked from any state with the shares accounted for (a
    // stronger result than from the invariant, and a smaller query), as a cross
    // product to keep the division out of the query.
    function _sized() internal view returns (bool) {
        (bool sharesOk,) = _sharesClosed();
        if (!(target.owner() == address(this) && sharesOk && target.totalSupply() <= CAP
            && target.totalAssets() <= CAP)) return false;
@SIZED_EXTRA@        return true;
    }

    function _price() internal view returns (Price memory p) {
        p.assets = target.totalAssets();
        p.shares = _shares();
        p.held = target.balanceOf(bob);
    }

    function _fair(Price memory p) internal view {
        Price memory q = _price();
        assert(q.held >= p.held);
        if (p.held > 0) {
            assert((q.assets + VIRTUAL) * (p.shares + VIRTUAL) >= (p.assets + VIRTUAL) * (q.shares + VIRTUAL));
        }
    }

@FAIR@}
"#;

const TOTALS_FNS: &str = r#"
    function _stored(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(address(target), bytes32(slot)));
    }

    /// The vault's own running totals, read from storage: each is the sum of
    /// one request record over the users, as the probe saw. Each is also at
    /// most 8 * 2^96, which the sums imply; the solver uses it as a bound.
    function _totalsOk(@PARAMS@) internal view returns (bool) {
@TOTALS@        return true;
    }
"#;

const REQUESTS_OWNER: &str = r#"    /// Request records, each at most 2^96: the shares where the invariant
    /// needs them (while the vault holds them, or the price or a total counts
    /// them), the assets always.
    function _requests() internal view returns (bool ok, uint256 pending, uint256 claimS, uint256 owed) {
        uint256 w0 = _owed(alice);
        uint256 w1 = _owed(bob);
        uint256 w2 = _owed(carol);
        ok = w0 <= CAP && w1 <= CAP && w2 <= CAP;
        owed = w0 + w1 + w2;
        if (SUM_PENDING) {
            uint256 p0 = _pending(alice);
            uint256 p1 = _pending(bob);
            uint256 p2 = _pending(carol);
            ok = ok && p0 <= CAP && p1 <= CAP && p2 <= CAP;
            pending = p0 + p1 + p2;
        }
        if (SUM_CLAIMABLE) {
            uint256 c0 = _claimable(alice);
            uint256 c1 = _claimable(bob);
            uint256 c2 = _claimable(carol);
            ok = ok && c0 <= CAP && c1 <= CAP && c2 <= CAP;
            // A claimable request whose shares are burned is owed at least as
            // many assets as it has shares: it was fulfilled at a price of at
            // least 1. Partial claims round in the vault's favour, so this
            // holds after them too.
            if (BACKED) ok = ok && c0 <= w0 && c1 <= w1 && c2 <= w2;
            claimS = c0 + c1 + c2;
        }
    }
"#;

const REQUESTS_TIME: &str = r#"    /// Request records, read at the latest time in one go: the views branch on
    /// the time, and at the latest time every request is claimable, so nothing
    /// is pending. Shares only while the vault still holds them (a burned
    /// record can grow past any cap), assets always.
    function _requests() internal returns (bool ok, uint256 pending, uint256 claimS, uint256 owed) {
        uint256 t = block.timestamp;
        vm.warp(LATEST);
        // maxRedeem is a request's claimable shares (ERC-7540); unlike
        // claimableRedeemRequest it often has no branch on the amount.
        uint256 c0 = target.maxRedeem(alice);
        uint256 c1 = target.maxRedeem(bob);
        uint256 c2 = target.maxRedeem(carol);
        uint256 w0 = target.maxWithdraw(alice);
        uint256 w1 = target.maxWithdraw(bob);
        uint256 w2 = target.maxWithdraw(carol);
        vm.warp(t);
        ok = w0 <= CAP && w1 <= CAP && w2 <= CAP;
        owed = w0 + w1 + w2;
        pending = 0;
        if (HELD_PENDING) {
            ok = ok && c0 <= CAP && c1 <= CAP && c2 <= CAP;
            claimS = c0 + c1 + c2;
        }
    }
"#;

const TIME_HELPERS: &str = r#"
    // Later than any claim time a uint32 can hold.
    uint256 internal constant LATEST = type(uint32).max;

    /// Any moment before the latest claim time.
    function _anyTime() internal {
        uint256 t = svm.createUint256("now");
        vm.assume(t < LATEST);
        vm.warp(t);
    }
"#;

const OWED_NOW: &str = r#"
    /// The assets u can claim now.
    function _owed(address u) internal view returns (uint256) {
        return target.maxWithdraw(u);
    }
"#;

const OWED_LATER: &str = r#"
    /// The assets u's request will pay once the delay is over.
    function _owed(address u) internal returns (uint256 owed) {
        uint256 t = block.timestamp;
        vm.warp(LATEST);
        owed = target.maxWithdraw(u);
        vm.warp(t);
    }
"#;

const CHAIN_OWNER: &str = r#"
    /// The owner can make user i's whole pending request claimable.
    function check_fulfil(uint256 i) public {
        vm.assume(i < 3);
        address u = _user(i);
        vm.assume(_inv());
        _witness();
        uint256 p = _pending(u);
        vm.assume(p == svm.createUint256("userPending"));
        vm.assume(p > 0);
        uint256 before = _claimable(u);
        // Records of up to 2^96 shares, the supply cap.
        vm.assume(before <= CAP);
        try target.fulfillRedeem(u, p) {
            assert(_pending(u) == 0);
            assert(_claimable(u) == before + p);
        } catch {
            assert(false);
        }
    }
"#;

const CHAIN_TIME: &str = r#"
    /// Once the delay is over, user i's whole request is claimable.
    function check_mature(uint256 i) public {
        vm.assume(i < 3);
        address u = _user(i);
        _anyTime();
        vm.assume(_inv());
        _witness();
        uint256 r = _pending(u) + _claimable(u);
        vm.assume(r == svm.createUint256("userRequested"));
        vm.assume(r > 0);
        vm.warp(LATEST);
        assert(_claimable(u) == r);
    }
"#;

const KEEPS_TIME: &str = r#"
    /// Time passes.
    function check_keeps_time(uint256 later) public {
        _anyTime();
        vm.assume(_inv());
        vm.assume(later >= block.timestamp && later < LATEST);
        vm.warp(later);
        assert(_holds());
    }
"#;

const STABLE_OWNER: &str = r#"
    function _requestOf() internal view returns (Request memory r) {
        r.shares = _pending(bob) + _claimable(bob);
        r.owed = target.maxWithdraw(bob);
    }

    /// Bob's request has as many shares, and he is owed as much, as before.
    function _stable(Request memory r) internal view {
        Request memory q = _requestOf();
        assert(q.shares >= r.shares && q.owed >= r.owed);
    }
"#;

const STABLE_TIME: &str = r#"
    function _requestOf() internal returns (Request memory r) {
        r.shares = _pending(bob) + _claimable(bob);
        r.now_ = _claimable(bob);
        r.owed = _owed(bob);
    }

    /// Bob's request has as many shares, he can claim as much now, and he is
    /// owed as much once the delay is over: nobody pushed his claim back.
    function _stable(Request memory r) internal {
        Request memory q = _requestOf();
        assert(q.shares >= r.shares && q.now_ >= r.now_ && q.owed >= r.owed);
    }
"#;

#[cfg(test)]
mod tests {
    use super::*;

    const CONTROLLED: &str = r#"{"abi":[
      {"type":"constructor","inputs":[{"name":"_asset","type":"address","internalType":"contract ERC20"},{"name":"_name","type":"string"},{"name":"_symbol","type":"string"}]},
      {"type":"function","name":"asset","inputs":[],"outputs":[{"name":"","type":"address"}],"stateMutability":"view"},
      {"type":"function","name":"totalAssets","inputs":[],"outputs":[{"name":"","type":"uint256"}],"stateMutability":"view"},
      {"type":"function","name":"totalSupply","inputs":[],"outputs":[{"name":"","type":"uint256"}],"stateMutability":"view"},
      {"type":"function","name":"balanceOf","inputs":[{"name":"","type":"address"}],"outputs":[{"name":"","type":"uint256"}],"stateMutability":"view"},
      {"type":"function","name":"allowance","inputs":[{"name":"","type":"address"},{"name":"","type":"address"}],"outputs":[{"name":"","type":"uint256"}],"stateMutability":"view"},
      {"type":"function","name":"isOperator","inputs":[{"name":"","type":"address"},{"name":"","type":"address"}],"outputs":[{"name":"","type":"bool"}],"stateMutability":"view"},
      {"type":"function","name":"owner","inputs":[],"outputs":[{"name":"","type":"address"}],"stateMutability":"view"},
      {"type":"function","name":"maxWithdraw","inputs":[{"name":"controller","type":"address"}],"outputs":[{"name":"","type":"uint256"}],"stateMutability":"view"},
      {"type":"function","name":"maxRedeem","inputs":[{"name":"controller","type":"address"}],"outputs":[{"name":"","type":"uint256"}],"stateMutability":"view"},
      {"type":"function","name":"approve","inputs":[{"name":"spender","type":"address"},{"name":"amount","type":"uint256"}],"outputs":[{"name":"","type":"bool"}],"stateMutability":"nonpayable"},
      {"type":"function","name":"deposit","inputs":[{"name":"assets","type":"uint256"},{"name":"receiver","type":"address"}],"outputs":[{"name":"shares","type":"uint256"}],"stateMutability":"nonpayable"},
      {"type":"function","name":"redeem","inputs":[{"name":"shares","type":"uint256"},{"name":"receiver","type":"address"},{"name":"controller","type":"address"}],"outputs":[{"name":"assets","type":"uint256"}],"stateMutability":"nonpayable"},
      {"type":"function","name":"withdraw","inputs":[{"name":"assets","type":"uint256"},{"name":"receiver","type":"address"},{"name":"controller","type":"address"}],"outputs":[{"name":"shares","type":"uint256"}],"stateMutability":"nonpayable"},
      {"type":"function","name":"requestRedeem","inputs":[{"name":"shares","type":"uint256"},{"name":"controller","type":"address"},{"name":"owner","type":"address"}],"outputs":[{"name":"requestId","type":"uint256"}],"stateMutability":"nonpayable"},
      {"type":"function","name":"pendingRedeemRequest","inputs":[{"name":"","type":"uint256"},{"name":"controller","type":"address"}],"outputs":[{"name":"","type":"uint256"}],"stateMutability":"view"},
      {"type":"function","name":"claimableRedeemRequest","inputs":[{"name":"","type":"uint256"},{"name":"controller","type":"address"}],"outputs":[{"name":"","type":"uint256"}],"stateMutability":"view"},
      {"type":"function","name":"fulfillRedeem","inputs":[{"name":"controller","type":"address"},{"name":"shares","type":"uint256"}],"outputs":[{"name":"assets","type":"uint256"}],"stateMutability":"nonpayable"},
      {"type":"function","name":"transferOwnership","inputs":[{"name":"newOwner","type":"address"}],"outputs":[],"stateMutability":"nonpayable"}
    ]}"#;

    #[test]
    fn finds_the_kind_of_exit() {
        let abi = Abi::parse(CONTROLLED).unwrap();
        assert_eq!(kind(&abi), Some(Progress::Owner));
        let timed = CONTROLLED.replace("\"fulfillRedeem\"", "\"setTimelock\"");
        assert_eq!(kind(&Abi::parse(&timed).unwrap()), Some(Progress::Time));
        let sync = CONTROLLED.replace("\"requestRedeem\"", "\"requestSomething\"");
        assert_eq!(kind(&Abi::parse(&sync).unwrap()), None);
    }

    #[test]
    fn reads_the_style_from_the_probe() {
        let s = style_from(&[
            PROBE_RUNS.to_string(),
            PROBE_BURNS_AT_FULFIL.to_string(),
            PROBE_RESERVES_AT_FULFIL.to_string(),
        ]);
        assert!(s.burns_at_fulfil && s.reserves_at_fulfil && !s.burns_at_request);
        assert_eq!(
            s.describe(Progress::Owner),
            "requested shares burned at the fulfilment; their assets set aside at the fulfilment"
        );
    }

    #[test]
    fn renders_the_chain_and_three_checks_per_function() {
        let abi = Abi::parse(CONTROLLED).unwrap();
        let style = Style {
            burns_at_fulfil: true,
            reserves_at_fulfil: true,
            ..Style::default()
        };
        let p = render(
            "ControlledAsyncRedeemFixed",
            "../../src/ControlledAsyncRedeemFixed.sol",
            &abi,
            Progress::Owner,
            style,
            &Learned::default(),
            true,
            false,
        )
        .unwrap();
        for c in [
            "check_init",
            "check_request",
            "check_fulfil",
            "check_claim_redeem",
            "check_keeps_requestRedeem",
            "check_stable_fulfillRedeem",
            "check_fair_redeem",
        ] {
            assert!(p.checks.iter().any(|n| n == c), "missing {c}");
            assert!(
                p.source.contains(&format!("function {c}(")),
                "no {c} in source"
            );
        }
        assert!(!p.source.contains("transferOwnership"));
        // Left out by the model, and said so; nothing else goes unchecked.
        assert!(
            p.left_out
                .contains(&"transferOwnership (changes the owner)".to_string())
        );
        assert!(p.unchecked.is_empty(), "{:?}", p.unchecked);
        // The chain runs for each of the three users, not only bob.
        for f in [
            "check_request",
            "check_fulfil",
            "check_claim_redeem",
            "check_claim_withdraw",
        ] {
            assert!(
                p.source.contains(&format!(
                    "function {f}(uint256 i) public {{\n        vm.assume(i < 3);\n        address u = _user(i);"
                )),
                "{f} is not per user"
            );
        }
        assert!(p.source.contains("try target.requestRedeem(s, u, u) {"));
        assert!(p.source.contains("try target.fulfillRedeem(u, p) {"));
        assert!(!p.source.contains("requestRedeem(s, bob, bob)"));
        assert!(!p.source.contains('@'), "unfilled placeholder");
        assert!(
            p.source
                .contains("if (vaultShares != pending) return false;")
        );
        assert!(
            p.source
                .contains("target.totalAssets() + owed != vaultAssets")
        );
        assert!(!p.source.contains("function check_mature("));
        // Step 15's vaults keep their invariant: no totals, exact price.
        assert!(p.source.contains("uint256 internal constant VIRTUAL = 0;"));
        assert!(
            p.source
                .contains("bool internal constant POOL_PENDING = false;")
        );
        assert!(!p.source.contains("_totalsOk"));
        // A view that reverts after a call breaks the invariant; a call that
        // reverts is not checked.
        assert!(p.source.contains("assert(_holds());"));
        assert!(p.source.contains("try target.requestRedeem("));
        assert!(!p.source.contains("assert(_inv());"));
    }

    fn stored(label: &str, slot: &str) -> Stored {
        Stored {
            label: label.into(),
            slot: slot.into(),
        }
    }

    #[test]
    fn the_probe_walks_each_total_through_a_request() {
        let abi = Abi::parse(CONTROLLED).unwrap();
        let totals = [stored("_totalClaimableShares", "10")];
        let src = probe_source("V", "../../src/V.sol", &abi, Progress::Owner, &totals).unwrap();
        for c in COUNTS {
            assert!(src.contains(&format!("function test_ausweg_total_10_{}()", c.name())));
        }
        assert!(src.contains("_walk(10)"));
        assert!(!src.contains('@'), "unfilled placeholder");
        // No convertToShares in this ABI: no price tests.
        assert!(!src.contains(PROBE_PRICE_VIRTUAL));
        // A timed vault's totals are not walked.
        let timed = probe_source("V", "../../src/V.sol", &abi, Progress::Time, &totals).unwrap();
        assert!(!timed.contains("_walk("));
        // requestRedeem returns its id here, so the probe checks it is 0.
        assert!(src.contains(&format!("function {PROBE_ID_ZERO}() public {{")));
        assert!(src.contains("uint256 id = target.requestRedeem(400, alice, alice);"));
    }

    #[test]
    fn refuses_a_fulfilment_it_cannot_call() {
        assert!(supports(&Abi::parse(CONTROLLED).unwrap()).is_ok());
        // The same vault with the arguments the other way round.
        let reversed = CONTROLLED.replace(
            r#""name":"fulfillRedeem","inputs":[{"name":"controller","type":"address"},{"name":"shares","type":"uint256"}]"#,
            r#""name":"fulfillRedeem","inputs":[{"name":"shares","type":"uint256"},{"name":"controller","type":"address"}]"#,
        );
        assert_ne!(reversed, CONTROLLED);
        let abi = Abi::parse(&reversed).unwrap();
        // Before: taken for a vault whose requests mature with time.
        assert_eq!(kind(&abi), Some(Progress::Time));
        let err = supports(&abi).unwrap_err().to_string();
        assert!(
            err.contains("fulfils requests with fulfillRedeem(uint256, address)"),
            "{err}"
        );
        // A vault with no fulfilment at all is a timed vault, as before.
        let timed = CONTROLLED.replace("\"fulfillRedeem\"", "\"setTimelock\"");
        assert!(supports(&Abi::parse(&timed).unwrap()).is_ok());
    }

    #[test]
    fn reads_what_each_total_counts() {
        let totals = [
            stored("_totalPendingDepositAssets", "6"),
            stored("_totalPendingRedeemShares", "7"),
            stored("_totalClaimableAssets", "9"),
            stored("_totalClaimableShares", "10"),
            stored("_totalCached", "12"),
            stored("_totalTwice", "13"),
            stored("totalFees", "14"),
        ];
        let passed: Vec<String> = [
            "test_ausweg_total_6_nothing",
            "test_ausweg_total_14_nothing",
            "test_ausweg_total_7_requested",
            "test_ausweg_total_9_owed",
            "test_ausweg_total_10_claimable",
            "test_ausweg_total_13_claimable",
            "test_ausweg_total_13_owed",
            PROBE_PRICE_VIRTUAL,
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        let l = learned_from(&passed, &totals);
        let got: Vec<(&str, Counts)> = l
            .totals
            .iter()
            .map(|t| (t.label.as_str(), t.counts))
            .collect();
        assert_eq!(
            got,
            [
                ("_totalPendingDepositAssets", Counts::Nothing),
                ("_totalPendingRedeemShares", Counts::Requested),
                ("_totalClaimableAssets", Counts::Owed),
                ("_totalClaimableShares", Counts::Claimable),
            ]
        );
        // Matched nothing, or two records: left out.
        assert_eq!(l.unread, ["_totalCached", "_totalTwice"]);
        // Stayed 0 but not about requests: left out, not pinned to 0.
        assert_eq!(l.idle, ["totalFees"]);
        assert_eq!(l.price, PriceRule::Virtual);
        // Both price tests passing (a price of exactly 1) reads as exact.
        let both = [
            PROBE_PRICE_EXACT.to_string(),
            PROBE_PRICE_VIRTUAL.to_string(),
        ];
        assert_eq!(learned_from(&both, &[]).price, PriceRule::Exact);
    }

    #[test]
    fn pins_the_totals_and_prices_burned_pending_shares() {
        let abi = Abi::parse(CONTROLLED).unwrap();
        let style = Style {
            burns_at_request: true,
            reserves_at_fulfil: true,
            ..Style::default()
        };
        let learned = Learned {
            totals: vec![
                Total {
                    label: "_totalPendingRedeemShares".into(),
                    slot: "7".into(),
                    counts: Counts::Requested,
                },
                Total {
                    label: "_totalClaimableShares".into(),
                    slot: "10".into(),
                    counts: Counts::Claimable,
                },
            ],
            price: PriceRule::Virtual,
            unread: Vec::new(),
            idle: Vec::new(),
        };
        let p = render(
            "OZAdminVault",
            "../../src/OZAdminVault.sol",
            &abi,
            Progress::Owner,
            style,
            &learned,
            true,
            true,
        )
        .unwrap();
        let s = &p.source;
        assert!(
            s.contains("if (_stored(7) > 8 * CAP || _stored(7) != pending + claimS) return false;")
        );
        assert!(s.contains("if (_stored(10) > 8 * CAP || _stored(10) != claimS) return false;"));
        // Only the parameters the lines use are named.
        assert!(s.contains("function _totalsOk(uint256 pending, uint256 claimS, uint256)"));
        assert!(s.contains("if (!_totalsOk(pending, claimS, owed)) return false;"));
        assert!(s.contains("bool internal constant POOL_PENDING = true;"));
        assert!(s.contains("bool internal constant SUM_PENDING = true;"));
        assert!(s.contains("bool internal constant SUM_CLAIMABLE = true;"));
        assert!(s.contains("uint256 internal constant VIRTUAL = 1;"));
        assert!(s.contains("if (target.totalAssets() < _shares()) return false;"));
        assert!(s.contains("if (!requestsOk || _shares() > CAP) return false;"));
        assert!(s.contains("// Its share price: (totalAssets + 1) / (shares + 1), where"));
        assert!(!s.contains('@'), "unfilled placeholder");
    }

    #[test]
    fn a_timed_vault_gets_time_checks() {
        let timed = CONTROLLED.replace("\"fulfillRedeem\"", "\"setTimelock\"");
        let abi = Abi::parse(&timed).unwrap();
        let style = Style {
            reserves_at_request: true,
            ..Style::default()
        };
        let p = render(
            "Timelocked",
            "../../src/Timelocked.sol",
            &abi,
            Progress::Time,
            style,
            &Learned::default(),
            true,
            false,
        )
        .unwrap();
        assert!(p.checks.iter().any(|n| n == "check_mature"));
        assert!(p.checks.iter().any(|n| n == "check_keeps_time"));
        assert!(p.source.contains("_anyTime();"));
        assert!(
            p.source
                .contains("if (vaultShares != claimS) return false;")
        );
        assert!(!p.source.contains('@'), "unfilled placeholder");
    }
}
