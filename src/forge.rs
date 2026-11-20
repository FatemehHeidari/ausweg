//! Foundry adapter (Step 4 architecture). Behind a trait so the pipeline can be
//! tested without Foundry installed.

use anyhow::{Context, Result};
use std::path::Path;
use std::process::Command;

#[derive(Debug, Clone)]
pub struct BuildResult {
    pub ok: bool,
    pub output: String,
}

/// One compiler error and where it is.
#[derive(Debug, Clone, PartialEq)]
pub struct CompileError {
    pub file: String,
    /// Byte offsets as solc reports them. With dynamic test linking (on by
    /// default in forge 1.9) forge rewrites `new C(...)` in test files before
    /// compiling, so these point into the rewritten text, not the file on disk.
    pub start: usize,
    pub end: usize,
    /// Line and column (1-based) from solc's formatted message. The rewrite
    /// keeps lines intact, so these match the file on disk.
    pub line: Option<usize>,
    pub col: Option<usize>,
    pub message: String,
}

impl CompileError {
    /// Byte offset of the error in `source`, the file as written to disk.
    pub fn offset_in(&self, source: &str) -> usize {
        let Some(line) = self.line else {
            return self.start;
        };
        let line_start: usize = source
            .split_inclusive('\n')
            .take(line.saturating_sub(1))
            .map(str::len)
            .sum();
        (line_start + self.col.unwrap_or(1).saturating_sub(1)).min(source.len())
    }
}

/// `--> test/X.t.sol:206:18:` in solc's formatted message, as (line, column).
fn line_col(formatted: &str) -> Option<(usize, usize)> {
    let rest = formatted.split("--> ").nth(1)?.lines().next()?;
    let mut parts = rest.trim().trim_end_matches(':').rsplitn(3, ':');
    let col = parts.next()?.parse().ok()?;
    let line = parts.next()?.parse().ok()?;
    Some((line, col))
}

/// `forge build --json`: errors with their exact positions.
#[derive(Debug, Clone)]
pub struct BuildJson {
    pub ok: bool,
    pub errors: Vec<CompileError>,
    /// Raw output, for messages when something unexpected happens.
    pub output: String,
}

/// Number of calls and reverts for one handler function in an invariant campaign.
#[derive(Debug, Clone, PartialEq)]
pub struct SelectorStats {
    pub selector: String,
    pub calls: u64,
    pub reverts: u64,
}

/// How a test failed, read from the reason forge prints in `[FAIL: <reason>]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FailKind {
    /// An assertion or expectation in the test failed: the property caught it.
    Assertion,
    /// The code reverted or panicked before any assertion decided anything.
    Revert,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Failure {
    pub name: String,
    pub reason: String,
}

impl Failure {
    pub fn kind(&self) -> FailKind {
        classify(&self.reason)
    }
}

#[derive(Debug, Clone, Default)]
pub struct TestResult {
    /// Compiled and ran (a failing test still counts as ran).
    pub ran: bool,
    pub passed: Vec<String>,
    pub failed: Vec<Failure>,
    pub output: String,
    /// Invariant campaigns: total handler calls and how many reverted.
    pub calls: Option<u64>,
    pub reverts: Option<u64>,
    /// Invariant campaigns: forge's per-function table.
    pub selectors: Vec<SelectorStats>,
}

impl TestResult {
    pub fn failed_names(&self) -> Vec<String> {
        self.failed.iter().map(|f| f.name.clone()).collect()
    }
}

pub trait Forge {
    fn build(&self, repo: &Path) -> Result<BuildResult>;
    /// Run only the tests in `test_file` (path relative to `repo`).
    fn test(&self, repo: &Path, test_file: &str) -> Result<TestResult>;
    /// Build and report errors with positions. The default has no positions.
    fn build_json(&self, repo: &Path) -> Result<BuildJson> {
        let b = self.build(repo)?;
        Ok(BuildJson {
            ok: b.ok,
            errors: Vec::new(),
            output: b.output,
        })
    }
}

pub struct ForgeCli {
    pub bin: String,
    /// Passed as `--fuzz-seed`, so every run sees the same fuzz inputs.
    pub fuzz_seed: Option<String>,
    /// Extra environment, e.g. `FOUNDRY_INVARIANT_RUNS`.
    pub env: Vec<(String, String)>,
}

impl ForgeCli {
    fn run(&self, repo: &Path, args: &[&str]) -> Result<(bool, String)> {
        let out = Command::new(&self.bin)
            .args(args)
            .envs(self.env.iter().map(|(k, v)| (k.as_str(), v.as_str())))
            .current_dir(repo)
            .output()
            .with_context(|| {
                format!(
                    "running `{} {}` (is Foundry installed?)",
                    self.bin,
                    args.join(" ")
                )
            })?;
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        Ok((out.status.success(), text))
    }
}

impl Forge for ForgeCli {
    fn build(&self, repo: &Path) -> Result<BuildResult> {
        let (ok, output) = self.run(repo, &["build"])?;
        Ok(BuildResult { ok, output })
    }

    fn test(&self, repo: &Path, test_file: &str) -> Result<TestResult> {
        // forge saves failing invariant sequences and replays them on the next
        // run. Each run (the clean one and every mutant) must start fresh.
        let _ = std::fs::remove_dir_all(repo.join("cache").join("invariant"));
        let mut args = vec!["test", "--match-path", test_file];
        if let Some(seed) = &self.fuzz_seed {
            args.extend(["--fuzz-seed", seed.as_str()]);
        }
        let (_, output) = self.run(repo, &args)?;
        Ok(parse_test_output(&output))
    }

    fn build_json(&self, repo: &Path) -> Result<BuildJson> {
        // Halmos builds with the AST and these extra outputs. Build the same
        // way, or Halmos may find our cache up to date and run without the AST.
        let out = Command::new(&self.bin)
            .args([
                "build",
                "--json",
                "--ast",
                "--extra-output",
                "storageLayout",
                "metadata",
            ])
            .envs(self.env.iter().map(|(k, v)| (k.as_str(), v.as_str())))
            .current_dir(repo)
            .output()
            .with_context(|| {
                format!(
                    "running `{} build --json` (is Foundry installed?)",
                    self.bin
                )
            })?;
        let stdout = String::from_utf8_lossy(&out.stdout).to_string();
        let stderr = String::from_utf8_lossy(&out.stderr).to_string();
        Ok(parse_build_json(&stdout, &stderr))
    }
}

/// Reads `forge build --json`. Anything that is not the expected JSON counts as a
/// failed build without positions, with the raw text kept for the message.
pub fn parse_build_json(stdout: &str, stderr: &str) -> BuildJson {
    let raw = format!("{stdout}{stderr}");
    let Ok(v) = serde_json::from_str::<serde_json::Value>(stdout.trim()) else {
        return BuildJson {
            ok: false,
            errors: Vec::new(),
            output: raw,
        };
    };
    let mut errors = Vec::new();
    let mut any_error = false;
    for e in v
        .get("errors")
        .and_then(|e| e.as_array())
        .into_iter()
        .flatten()
    {
        if e.get("severity").and_then(|s| s.as_str()) != Some("error") {
            continue;
        }
        any_error = true;
        let loc = e.get("sourceLocation");
        let num = |k: &str| {
            loc.and_then(|l| l.get(k))
                .and_then(|n| n.as_u64())
                .map(|n| n as usize)
        };
        let lc = e
            .get("formattedMessage")
            .and_then(|m| m.as_str())
            .and_then(line_col);
        errors.push(CompileError {
            file: loc
                .and_then(|l| l.get("file"))
                .and_then(|f| f.as_str())
                .unwrap_or("")
                .to_string(),
            start: num("start").unwrap_or(0),
            end: num("end").unwrap_or(0),
            line: lc.map(|(l, _)| l),
            col: lc.map(|(_, c)| c),
            message: e
                .get("message")
                .and_then(|m| m.as_str())
                .unwrap_or("")
                .to_string(),
        });
    }
    BuildJson {
        ok: !any_error,
        errors,
        output: raw,
    }
}

/// Parse forge's text output: lines like `[PASS] testFuzz_x(uint256) (runs: 256, ...)`
/// and `[FAIL: reason; counterexample: ...] testFuzz_y(uint256) ...`
/// (older forge: `[FAIL. Reason: ...]`).
pub fn parse_test_output(output: &str) -> TestResult {
    let mut r = TestResult {
        output: output.to_string(),
        ..Default::default()
    };
    // A contract with a single invariant prints its failure over several lines:
    // `[FAIL: reason]`, the call sequence (indented), then
    // ` invariant_x() (runs: 1, calls: 4, reverts: 2)`. This holds the reason
    // until the name arrives.
    let mut pending: Option<String> = None;
    for line in output.lines().map(str::trim) {
        if let Some(rest) = line.strip_prefix("[PASS]") {
            pending = None;
            if let Some(name) = test_name(rest) {
                r.passed.push(name);
            }
        } else if line.starts_with("[FAIL") {
            // The reason can itself contain brackets (`args=[1]`), so find the
            // bracket that closes the opening one.
            let Some(end) = closing_bracket(line) else {
                continue;
            };
            let reason = fail_reason(&line[1..end]);
            match test_name(&line[end + 1..]) {
                Some(name) => {
                    pending = None;
                    r.failed.push(Failure { name, reason });
                }
                None => pending = Some(reason),
            }
        } else if pending.is_some()
            && let Some(name) = name_line(line)
        {
            r.failed.push(Failure {
                name,
                reason: pending.take().unwrap_or_default(),
            });
        }
    }
    r.ran = !r.passed.is_empty() || !r.failed.is_empty();
    parse_campaign_stats(output, &mut r);
    // forge repeats every failure in a "Failing tests:" summary at the end of
    // the run; without this each flagged test would be counted twice.
    dedup_by(&mut r.passed, |n| n.clone());
    dedup_by(&mut r.failed, |f| f.name.clone());
    r
}

/// Invariant campaigns end with a line such as
/// ` VaultInvariants invariants (runs: 32, calls: 2048, reverts: 513)` and a table
/// with one row per handler function: `| Handler | call_deposit | 230 | 12 | 0 |`.
/// Both are printed twice when something fails, so only the first copy counts.
fn parse_campaign_stats(output: &str, r: &mut TestResult) {
    let number_after = |line: &str, key: &str| -> Option<u64> {
        let rest = &line[line.find(key)? + key.len()..];
        rest.trim_start()
            .chars()
            .take_while(char::is_ascii_digit)
            .collect::<String>()
            .parse()
            .ok()
    };
    let mut seen_lines = std::collections::HashSet::new();
    let (mut calls, mut reverts) = (None, None);
    // A contract with one invariant has no campaign line; its stats sit on the
    // test's own line: `[PASS] invariant_x() (runs: 32, calls: 2048, reverts: 712)`.
    let mut seen_tests = std::collections::HashSet::new();
    let (mut test_calls, mut test_reverts) = (None, None);
    for line in output.lines() {
        let t = line.trim();
        if t.contains("invariants (runs:")
            && seen_lines.insert(t.to_string())
            && let (Some(c), Some(v)) = (number_after(t, "calls:"), number_after(t, "reverts:"))
        {
            calls = Some(calls.unwrap_or(0) + c);
            reverts = Some(reverts.unwrap_or(0) + v);
        } else if t.contains("(runs:")
            && let (Some(c), Some(v)) = (number_after(t, "calls:"), number_after(t, "reverts:"))
            && let Some(name) =
                name_line(t.trim_start_matches("[PASS]").trim()).or_else(|| name_line(t))
            && seen_tests.insert(name)
        {
            test_calls = Some(test_calls.unwrap_or(0) + c);
            test_reverts = Some(test_reverts.unwrap_or(0) + v);
        }
        if t.starts_with('|') {
            let cells: Vec<&str> = t.trim_matches('|').split('|').map(str::trim).collect();
            if cells.len() == 5
                && let (Ok(c), Ok(v)) = (cells[2].parse::<u64>(), cells[3].parse::<u64>())
                && !r.selectors.iter().any(|s| s.selector == cells[1])
            {
                r.selectors.push(SelectorStats {
                    selector: cells[1].to_string(),
                    calls: c,
                    reverts: v,
                });
            }
        }
    }
    r.calls = calls.or(test_calls);
    r.reverts = reverts.or(test_reverts);
}

/// forge-std assertions fail with `assertion failed[: a != b]`, or with
/// `<custom message>: a != b` when the test passes a message. Failed
/// expectations read `call did not revert as expected` or
/// `Error != expected error: ...`. Anything else (panics, revert strings,
/// custom errors, `EvmError`) means the code reverted before an assertion ran.
///
/// Known gap: `assertTrue(x, "msg")` fails with just `msg` and is counted as a
/// revert, so assertion kills are a lower bound.
pub fn classify(reason: &str) -> FailKind {
    const COMPARISONS: [&str; 6] = [" != ", " == ", " < ", " > ", " <= ", " >= "];
    let r = reason.trim();
    let assertion = r.is_empty() // DSTest-style `fail()` leaves no revert data
        || r.starts_with("assertion failed")
        || r.starts_with("call did not revert")
        // The tool's exit checks turn a reverted exit into this message.
        || r.starts_with("ausweg exit:")
        || COMPARISONS.iter().any(|c| r.contains(c));
    if assertion {
        FailKind::Assertion
    } else {
        FailKind::Revert
    }
}

/// `FAIL: reason; counterexample: ...` or `FAIL. Reason: reason` -> `reason`.
fn fail_reason(inner: &str) -> String {
    let s = inner.trim_start_matches("FAIL");
    let s = s.trim_start_matches(['.', ':']).trim();
    let s = s.strip_prefix("Reason:").unwrap_or(s).trim();
    s.split("; counterexample:")
        .next()
        .unwrap_or("")
        .trim()
        .to_string()
}

/// `invariant_x() (runs: 1, ...)`: a test's name line, as opposed to the
/// `[Sequence]` and `sender=...` lines printed between a failure and its name.
fn name_line(line: &str) -> Option<String> {
    let ident: String = line
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    let starts_well = ident
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_');
    (starts_well && line[ident.len()..].starts_with('(')).then_some(ident)
}

fn test_name(rest: &str) -> Option<String> {
    let name = rest.trim().split('(').next().unwrap_or("").trim();
    (!name.is_empty()).then(|| name.to_string())
}

fn dedup_by<T, K: std::hash::Hash + Eq>(v: &mut Vec<T>, key: impl Fn(&T) -> K) {
    let mut seen = std::collections::HashSet::new();
    v.retain(|x| seen.insert(key(x)));
}

/// Index of the `]` matching the `[` at position 0.
fn closing_bracket(s: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (i, c) in s.char_indices() {
        match c {
            '[' => depth += 1,
            ']' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_names_and_reasons() {
        let out = "Ran 3 tests for test/generated/Vault.base.t.sol:VaultPropertyTest\n\
                   [PASS] testFuzz_a(uint256) (runs: 256, μ: 1, ~: 1)\n\
                   [FAIL: assertion failed: 2 > 1; counterexample: calldata=0x args=[1]] testFuzz_b(uint256) (runs: 3)\n\
                   [FAIL. Reason: revert] testFuzz_c() (gas: 1)\n";
        let r = parse_test_output(out);
        assert!(r.ran);
        assert_eq!(r.passed, vec!["testFuzz_a"]);
        assert_eq!(
            r.failed,
            vec![
                Failure {
                    name: "testFuzz_b".into(),
                    reason: "assertion failed: 2 > 1".into()
                },
                Failure {
                    name: "testFuzz_c".into(),
                    reason: "revert".into()
                },
            ]
        );
    }

    #[test]
    fn failing_summary_is_not_counted_twice() {
        let out = "[PASS] testFuzz_a(uint256) (runs: 256, μ: 1, ~: 1)\n\
                   [FAIL: assertion failed] testFuzz_b(uint256) (runs: 3, μ: 1, ~: 1)\n\
                   Suite result: FAILED. 1 passed; 1 failed; 0 skipped\n\
                   \n\
                   Failing tests:\n\
                   Encountered 1 failing test in test/generated/Bank.base.t.sol:BankPropertyTest\n\
                   [FAIL: assertion failed] testFuzz_b(uint256) (runs: 3, μ: 1, ~: 1)\n";
        let r = parse_test_output(out);
        assert_eq!(r.passed, vec!["testFuzz_a"]);
        assert_eq!(r.failed_names(), vec!["testFuzz_b"]);
    }

    #[test]
    fn compile_failure_means_not_ran() {
        let r =
            parse_test_output("Error: Compiler run failed:\nError (7576): Undeclared identifier.");
        assert!(!r.ran);
    }

    /// Output of forge 1.9.0 for a campaign with one broken invariant, trimmed.
    const INVARIANT_RUN: &str = "Ran 1 test for test/generated/OZVault.inv.t.sol:OZVaultInvariants
[FAIL: assertion failed: 23 >= 15] invariant_small
\t[Sequence] (original: 4, shrunk: 2)
\t\tsender=0x13aa addr=[test/x:H]0x56 calldata=call_deposit(uint256) args=[6232]

OZVaultInvariants invariants: 1/2 invariants broken
[PASS] invariant_alwaysTrue
[FAIL: assertion failed: 23 >= 15] invariant_small
 OZVaultInvariants invariants (runs: 8, calls: 128, reverts: 56)

| Contract | Selector     | Calls | Reverts | Discards |
+==================================================+
| Handler  | call_deposit | 69    | 0       | 0        |
|----------+----------+-------+---------+----------|
| Handler  | call_redeem  | 59    | 56      | 0        |

Failing tests:
Encountered 1 failing test in test/generated/OZVault.inv.t.sol:OZVaultInvariants
[FAIL: assertion failed: 23 >= 15] invariant_small
OZVaultInvariants invariants: 1/2 invariants broken
[PASS] invariant_alwaysTrue
[FAIL: assertion failed: 23 >= 15] invariant_small
 OZVaultInvariants invariants (runs: 8, calls: 128, reverts: 56)
";

    #[test]
    fn reads_invariant_results_and_campaign_stats() {
        let r = parse_test_output(INVARIANT_RUN);
        assert_eq!(r.passed, vec!["invariant_alwaysTrue"]);
        assert_eq!(r.failed_names(), vec!["invariant_small"]);
        assert_eq!(r.failed[0].reason, "assertion failed: 23 >= 15");
        assert_eq!((r.calls, r.reverts), (Some(128), Some(56)));
        assert_eq!(
            r.selectors,
            vec![
                SelectorStats {
                    selector: "call_deposit".into(),
                    calls: 69,
                    reverts: 0
                },
                SelectorStats {
                    selector: "call_redeem".into(),
                    calls: 59,
                    reverts: 56
                },
            ]
        );
    }

    /// Shape of forge 1.9.0's output for a bad assertion in a generated harness.
    #[test]
    fn reads_build_errors_with_positions() {
        let json = r#"{"errors":[
            {"severity":"warning","message":"unused","sourceLocation":{"file":"a.sol","start":1,"end":2}},
            {"severity":"error","type":"TypeError","message":"Member \"nope\" not found","sourceLocation":{"file":"test/generated/V.inv.t.sol","start":8115,"end":8126},
             "formattedMessage":"TypeError: Member \"nope\" not found\n   --> test/generated/V.inv.t.sol:206:18:\n    |\n206 |         assertGe(target.nope(), 0);\n"}],
            "sources":{},"contracts":{}}"#;
        let b = parse_build_json(json, "");
        assert!(!b.ok);
        assert_eq!(
            b.errors,
            vec![CompileError {
                file: "test/generated/V.inv.t.sol".into(),
                start: 8115,
                end: 8126,
                line: Some(206),
                col: Some(18),
                message: "Member \"nope\" not found".into()
            }]
        );
        assert!(parse_build_json(r#"{"errors":[],"contracts":{}}"#, "").ok);
        assert!(!parse_build_json("Error: not json", "").ok);
    }

    /// forge 1.9.0, a contract with one invariant, run on a Solady mutant.
    const ONE_INVARIANT_FAIL: &str = "Ran 1 test for test/generated/SoladyVault.inv.t.sol:SoladyVaultInvariants
[FAIL: assertion failed: 3 > 2]
\t[Sequence] (original: 2, shrunk: 1)
\t\tsender=0x0000000000000000000000000000000000000b28 addr=[test/generated/SoladyVault.inv.t.sol:SoladyVaultHandler]0xa0Cb889707d426A7A386870A03bc70d1b0697598 calldata=call_mint(uint256,uint256,uint256) args=[1, 2, 3]
 invariant_solvency() (runs: 1, calls: 4, reverts: 2)

| SoladyVaultHandler | call_deposit      | 1     | 0       | 0        |
Suite result: FAILED. 0 passed; 1 failed; 0 skipped; finished in 5.53ms (2.74ms CPU time)

Failing tests:
Encountered 1 failing test in test/generated/SoladyVault.inv.t.sol:SoladyVaultInvariants
[FAIL: assertion failed: 3 > 2]
\t[Sequence] (original: 2, shrunk: 1)
\t\tsender=0x0000000000000000000000000000000000000b28 addr=[test/generated/SoladyVault.inv.t.sol:SoladyVaultHandler]0xa0Cb889707d426A7A386870A03bc70d1b0697598 calldata=call_mint(uint256,uint256,uint256) args=[1, 2, 3]
 invariant_solvency() (runs: 1, calls: 4, reverts: 2)
";

    #[test]
    fn reads_a_single_invariant_failing_over_several_lines() {
        let r = parse_test_output(ONE_INVARIANT_FAIL);
        assert!(r.ran);
        assert_eq!(
            r.failed,
            vec![Failure {
                name: "invariant_solvency".into(),
                reason: "assertion failed: 3 > 2".into()
            }]
        );
        assert_eq!(classify(&r.failed[0].reason), FailKind::Assertion);
        assert_eq!((r.calls, r.reverts), (Some(4), Some(2)));
        let pass = parse_test_output(
            "[PASS] invariant_solvency() (runs: 32, calls: 2048, reverts: 712)\n",
        );
        assert_eq!(pass.passed, ["invariant_solvency"]);
        assert_eq!((pass.calls, pass.reverts), (Some(2048), Some(712)));
        assert_eq!(name_line("sender=0x1 addr=[a]"), None);
        assert_eq!(name_line("[Sequence] (original: 2, shrunk: 1)"), None);
    }

    #[test]
    fn locates_errors_by_line_when_forge_rewrote_the_file() {
        let source = "line one\nline two\n    assertGe(target.nope(), 0);\n";
        let mut e = CompileError {
            file: "t.sol".into(),
            start: 400,
            end: 411,
            line: Some(3),
            col: Some(14),
            message: String::new(),
        };
        assert_eq!(&source[e.offset_in(source)..][..11], "target.nope");
        e.line = None;
        assert_eq!(e.offset_in(source), 400);
        assert_eq!(line_col("x\n --> a/b.sol:12:5:\n"), Some((12, 5)));
        assert_eq!(line_col("no location"), None);
    }

    /// Reasons as forge prints them in the runs on Bank.sol.
    #[test]
    fn classifies_assertions_apart_from_reverts() {
        use FailKind::*;
        let cases = [
            ("assertion failed: 0 != 9533", Assertion),
            ("assertion failed", Assertion),
            ("balance mismatch: 1 != 2", Assertion),
            ("call did not revert as expected", Assertion),
            (
                "Error != expected error: panic: arithmetic underflow or overflow (0x11) != insufficient balance",
                Assertion,
            ),
            ("", Assertion),
            ("ausweg exit: redeem(maxRedeem) reverted", Assertion),
            (
                "ausweg exit: redeem paid less than previewRedeem: 5 < 6",
                Assertion,
            ),
            ("panic: arithmetic underflow or overflow (0x11)", Revert),
            ("insufficient balance", Revert),
            ("InsufficientBalance(0, 100)", Revert),
            ("EvmError: Revert", Revert),
        ];
        for (reason, want) in cases {
            assert_eq!(classify(reason), want, "reason: {reason:?}");
        }
    }
}
