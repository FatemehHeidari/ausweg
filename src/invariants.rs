//! Milestone 2, design C: the tool writes the setup and a handler that drives the
//! contract through random call sequences; the model writes only invariant
//! assertions. Stages follow the Step 4 pipeline: facts, plan, scaffold,
//! compile and repair, run on clean code, mutation score.

use crate::abi::Abi;
use crate::baseline::{self, MutationScore, Options, Target};
use crate::forge::{BuildJson, Forge};
use crate::model::Model;
use crate::plan::{self, Invariant, Names, Rejected};
use crate::scaffold::{self, Harness, span_at};
use crate::vacuous;
use anyhow::{Context, Result, bail};
use serde::Serialize;
use std::fs;
use std::path::{Path, PathBuf};

pub struct InvOptions {
    /// Mutation settings; `max_tries` is unused here.
    pub base: Options,
    /// Model repair calls allowed per invariant before it is dropped.
    pub max_repairs: usize,
    /// Larger sources are left out of the prompt; the ABI stands in for them.
    pub max_source_chars: usize,
    /// Model calls allowed to get a usable plan.
    pub plan_attempts: usize,
    /// Invariants kept from the plan; the rest are noted and dropped.
    pub max_invariants: usize,
    /// Refuse assertions that can never fail, such as `assertGe(x, 0)` on a
    /// uint256, and ask the model for others. Off reproduces version 0.2.0.
    pub reject_never_failing: bool,
    /// Model calls allowed for replacing refused invariants.
    pub replace_rounds: usize,
    /// Add the rules of a standard the contract implements (ERC-4626 so far)
    /// to the plan prompt. Off reproduces version 0.2.1.
    pub hints: bool,
    /// Add the tool's exit checks when the contract is an ERC-4626 vault. Off
    /// reproduces version 0.2.3.
    pub exit_checks: bool,
}

#[derive(Debug, Serialize)]
pub struct Dropped {
    pub id: String,
    pub assert: String,
    pub error: String,
}

#[derive(Debug, Serialize)]
pub struct InvReport {
    pub contract: String,
    pub test_file: String,
    pub model: String,
    /// Handler functions the campaign can call.
    pub handler: Vec<String>,
    /// The tool's exit checks in the test file, by test name.
    pub exit_checks: Vec<String>,
    /// ABI functions the handler leaves out, with the reason.
    pub skipped: Vec<String>,
    /// Standards whose rules went into the prompt, such as "ERC-4626".
    pub hints: Vec<String>,
    /// What the tool filled in or threw away from the plan.
    pub notes: Vec<String>,
    /// Invariants in the model's first plan.
    pub proposed: usize,
    /// Invariants that can never fail, refused before compiling.
    pub rejected: Vec<Rejected>,
    /// Invariants the model sent in place of refused ones.
    pub replacements: usize,
    /// Model calls spent asking for replacements.
    pub replace_calls: usize,
    pub kept: Vec<Invariant>,
    pub dropped: Vec<Dropped>,
    /// Model calls spent repairing assertions.
    pub repairs: usize,
    /// Repairs refused because the fixed assertion could never fail.
    pub repairs_refused: usize,
    pub passed_on_clean: Vec<String>,
    /// Invariants that fail on the unchanged contract: wrong, or a real bug.
    pub flagged: Vec<String>,
    pub calls: Option<u64>,
    pub reverts: Option<u64>,
    /// Handler functions with the most reverted calls on the clean run.
    pub top_reverts: Vec<(String, u64, u64)>,
    pub mutation: Option<MutationScore>,
}

/// `contract OZVault is ERC4626`, from the source, for the prompt.
fn declaration(source: &str, name: &str) -> String {
    source
        .lines()
        .map(str::trim)
        .find(|l| {
            let mut words = l.split_whitespace();
            let first = words.next();
            let second = words.next().map(|w| w.trim_end_matches('{'));
            matches!(first, Some("contract") | Some("abstract")) && {
                let second = if first == Some("abstract") {
                    words.next().map(|w| w.trim_end_matches('{'))
                } else {
                    second
                };
                second == Some(name)
            }
        })
        .map(|l| l.trim_end_matches('{').trim().to_string())
        .unwrap_or_else(|| format!("contract {name}"))
}

fn same_file(a: &str, b: &str) -> bool {
    a.trim_start_matches("./") == b.trim_start_matches("./")
}

fn describe_errors(b: &BuildJson) -> String {
    if b.errors.is_empty() {
        return b.output.chars().take(2000).collect();
    }
    b.errors
        .iter()
        .take(5)
        .map(|e| match e.line {
            Some(l) => format!("{}:{l}: {}", e.file, e.message),
            None => format!("{}: {}", e.file, e.message),
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Stage 2b: refuses invariants that can never fail and asks the model for
/// others, at most `replace_rounds` times. Returns the invariants to compile.
fn screen(
    first: Vec<Invariant>,
    base_prompt: &str,
    abi: &Abi,
    model: &dyn Model,
    opts: &InvOptions,
    report: &mut InvReport,
) -> Result<Vec<Invariant>> {
    let mut kept: Vec<Invariant> = Vec::new();
    let mut batch = first;
    let mut round = 0;
    loop {
        let before = report.rejected.len();
        for inv in batch {
            match vacuous::never_fails(&inv.assert, abi) {
                Some(reason) => {
                    eprintln!("  rejected {}: can never fail ({reason})", inv.id);
                    report.rejected.push(Rejected {
                        id: inv.id,
                        assert: inv.assert,
                        reason,
                    });
                }
                None => kept.push(inv),
            }
        }
        let refused_now = report.rejected.len() - before;
        let wanted = refused_now.min(opts.max_invariants.saturating_sub(kept.len()));
        if wanted == 0 || round == opts.replace_rounds {
            return Ok(kept);
        }
        round += 1;
        report.replace_calls += 1;
        let prompt = plan::replace_prompt(base_prompt, &report.rejected, &kept, wanted);
        let answer = model.complete_json(&prompt)?;
        // Names and assertions already seen, kept or refused, are not reused.
        let taken: Vec<Invariant> = kept
            .iter()
            .cloned()
            .chain(report.rejected.iter().map(|r| Invariant {
                id: r.id.clone(),
                statement: String::new(),
                assert: r.assert.clone(),
            }))
            .collect();
        match plan::parse_replacements(&answer, &taken, wanted) {
            Ok((new, notes)) => {
                report.notes.extend(notes);
                report.replacements += new.len();
                batch = new;
            }
            Err(e) => {
                report
                    .notes
                    .push(format!("replacement answer {round} not usable: {e}"));
                return Ok(kept);
            }
        }
    }
}

pub fn run(
    repo: &Path,
    contract: &Path,
    model: &dyn Model,
    forge: &dyn Forge,
    opts: &InvOptions,
) -> Result<InvReport> {
    let target = Target::open(repo, contract)?;
    let file_name = contract
        .file_name()
        .and_then(|f| f.to_str())
        .context("contract path has no file name")?;
    let gen_dir = repo.join("test/generated");
    fs::create_dir_all(&gen_dir)?;
    let test_rel = PathBuf::from("test/generated").join(format!("{}.inv.t.sol", target.name));
    let test_rel_str = test_rel.display().to_string();
    let test_abs = repo.join(&test_rel);
    // A broken file left by an interrupted run would stop the first build.
    let _ = fs::remove_file(&test_abs);
    fs::write(gen_dir.join(scaffold::TOKEN_FILE), scaffold::TOKEN_SOURCE)?;

    // Stage 1: facts.
    let build = forge.build_json(repo)?;
    if !build.ok {
        bail!(
            "the project does not compile before ausweg adds anything:\n{}",
            describe_errors(&build)
        );
    }
    let abi = Abi::load(repo, file_name, &target.name)?;

    // Stage 2: plan.
    let decl = declaration(&target.source, &target.name);
    let source = (target.source.len() <= opts.max_source_chars).then_some(target.source.as_str());
    let rules = (opts.hints && plan::is_erc4626(&abi)).then_some(plan::ERC4626_RULES);
    let prompt = plan::prompt(
        &target.name,
        &contract.display().to_string(),
        &decl,
        &abi,
        source,
        target.source.len(),
        rules,
    );
    let mut plan = None;
    let mut last_error = String::new();
    for attempt in 1..=opts.plan_attempts {
        let p = if attempt == 1 {
            prompt.clone()
        } else {
            format!(
                "{prompt}\nYour previous answer was rejected: {last_error}. Return only the JSON."
            )
        };
        match plan::parse(&model.complete_json(&p)?, &abi, opts.max_invariants) {
            Ok(pl) => {
                plan = Some(pl);
                break;
            }
            Err(e) => {
                eprintln!("  plan attempt {attempt}/{}: {e}", opts.plan_attempts);
                last_error = e.to_string();
            }
        }
    }
    let plan = plan.with_context(|| {
        format!(
            "no usable plan after {} model calls: {last_error}",
            opts.plan_attempts
        )
    })?;

    let mut report = InvReport {
        contract: contract.display().to_string(),
        test_file: test_rel_str.clone(),
        model: model.name(),
        handler: vec![],
        exit_checks: vec![],
        skipped: vec![],
        hints: rules.map(|_| "ERC-4626".to_string()).into_iter().collect(),
        notes: plan.notes.clone(),
        proposed: plan.invariants.len(),
        rejected: vec![],
        replacements: 0,
        replace_calls: 0,
        kept: vec![],
        dropped: vec![],
        repairs: 0,
        repairs_refused: 0,
        passed_on_clean: vec![],
        flagged: vec![],
        calls: None,
        reverts: None,
        top_reverts: vec![],
        mutation: None,
    };

    // Stage 2b: refuse invariants that can never fail, and ask for others.
    let to_compile = if opts.reject_never_failing {
        screen(
            plan.invariants.clone(),
            &prompt,
            &abi,
            model,
            opts,
            &mut report,
        )?
    } else {
        plan.invariants.clone()
    };

    // Stages 3 and 4: scaffold, compile, repair one invariant at a time.
    let import_path = format!("../../{}", contract.display());
    let mut harness = Harness::new(&target.name, &import_path, &abi, &plan.ctor);
    harness.exit_checks = opts.exit_checks && scaffold::supports_exit_checks(&abi);
    if harness.exit_checks {
        report.exit_checks = scaffold::EXIT_CHECKS
            .iter()
            .map(|s| s.to_string())
            .collect();
    }
    report.handler = harness.calls.clone();
    report.skipped = harness.skipped.clone();
    let names = Names {
        contract: &target.name,
        tokens: harness.tokens.clone(),
        sums: harness.sums.clone(),
        abi: &abi,
    };
    // Each active invariant with the repairs it has used, and why its last
    // repair was refused, if it was.
    let mut active: Vec<(Invariant, usize, Option<String>)> =
        to_compile.into_iter().map(|i| (i, 0, None)).collect();
    loop {
        let invs: Vec<Invariant> = active.iter().map(|(i, _, _)| i.clone()).collect();
        let sc = harness.render(&invs);
        fs::write(&test_abs, &sc.source)?;
        let b = forge.build_json(repo)?;
        if b.ok {
            break;
        }
        let mut failing: Vec<(String, String)> = Vec::new();
        let mut other = Vec::new();
        for e in &b.errors {
            let at = e.offset_in(&sc.source);
            match span_at(&sc.spans, at).filter(|_| same_file(&e.file, &test_rel_str)) {
                Some(sp) if !failing.iter().any(|(id, _)| id == &sp.id) => {
                    failing.push((sp.id.clone(), e.message.clone()))
                }
                Some(_) => {}
                None => other.push(e),
            }
        }
        if !other.is_empty() || failing.is_empty() {
            // The harness itself does not compile: nothing the model can fix.
            fs::rename(&test_abs, test_abs.with_extension("sol.failed"))?;
            bail!(
                "the generated harness does not compile (a ausweg limitation, not the model's); kept as {}.failed:\n{}",
                test_rel_str,
                describe_errors(&b)
            );
        }
        for (id, message) in failing {
            let idx = active
                .iter()
                .position(|(i, _, _)| i.id == id)
                .expect("failing invariant is active");
            if active[idx].1 >= opts.max_repairs {
                let (inv, _, _) = active.remove(idx);
                eprintln!("  dropped {}: {message}", inv.id);
                report.dropped.push(Dropped {
                    id: inv.id,
                    assert: inv.assert,
                    error: message,
                });
                continue;
            }
            active[idx].1 += 1;
            report.repairs += 1;
            let error = match &active[idx].2 {
                Some(refused) => format!("{message}\n{refused}"),
                None => message.clone(),
            };
            let answer =
                model.complete_json(&plan::repair_prompt(&active[idx].0, &error, &names))?;
            // An unusable answer keeps the old line, which fails again and uses up a repair.
            if let Ok(fixed) = plan::parse_repair(&answer) {
                let refused = opts
                    .reject_never_failing
                    .then(|| vacuous::never_fails(&fixed, &abi))
                    .flatten();
                match refused {
                    Some(reason) => {
                        eprintln!("  repair of {id} refused: {fixed} can never fail ({reason})");
                        report.repairs_refused += 1;
                        active[idx].2 = Some(format!(
                            "Your last fix, {fixed}, was refused: it can never fail ({reason}). \
                             Fix the error without making the assertion always true."
                        ));
                    }
                    None => {
                        active[idx].0.assert = fixed;
                        active[idx].2 = None;
                    }
                }
            }
        }
    }
    report.kept = active.into_iter().map(|(i, _, _)| i).collect();
    // With exit checks there is still something to run.
    if report.kept.is_empty() && report.exit_checks.is_empty() {
        return Ok(report);
    }

    // Stage 5: run on clean code.
    let clean = forge.test(repo, &test_rel_str)?;
    if !clean.ran {
        let tail: String = clean
            .output
            .chars()
            .rev()
            .take(2000)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        bail!("the invariant tests compiled but did not run:\n{tail}");
    }
    report.flagged = clean.failed_names();
    report.passed_on_clean = clean.passed.clone();
    report.calls = clean.calls;
    report.reverts = clean.reverts;
    let mut by_reverts = clean.selectors.clone();
    by_reverts.sort_by_key(|s| std::cmp::Reverse(s.reverts));
    report.top_reverts = by_reverts
        .into_iter()
        .filter(|s| s.reverts > 0)
        .take(3)
        .map(|s| (s.selector, s.reverts, s.calls))
        .collect();

    // Stage 6: mutation score, with the same scorer as milestone 1.
    if opts.base.mutation && !report.passed_on_clean.is_empty() {
        report.mutation = Some(baseline::score(
            repo,
            &target,
            &test_rel_str,
            &report.passed_on_clean,
            forge,
            &opts.base,
        )?);
    }
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::OZ_VAULT_ABI;
    use crate::forge::{BuildResult, CompileError, Failure, TestResult};
    use crate::model::Scripted;
    use std::cell::RefCell;

    const SOURCE: &str = "pragma solidity ^0.8.0;\ncontract OZVault is ERC4626 {\n    function f(uint a) public pure returns (bool) { return a > 10; }\n}\n";

    /// A fake forge for the whole pipeline: the artifact comes from the OZVault
    /// ABI fixture; an assertion containing `nope` does not compile; the
    /// invariant `wrong` fails on clean code; under the `>` mutant `solvency`
    /// fails an assertion.
    struct FakeForge {
        contract: PathBuf,
        test_file: PathBuf,
        builds: RefCell<usize>,
    }

    impl Forge for FakeForge {
        fn build(&self, _: &Path) -> Result<BuildResult> {
            unreachable!("the invariant pipeline uses build_json")
        }
        fn build_json(&self, repo: &Path) -> Result<BuildJson> {
            *self.builds.borrow_mut() += 1;
            let art = repo.join("out/OZVault.sol");
            fs::create_dir_all(&art)?;
            fs::write(art.join("OZVault.json"), OZ_VAULT_ABI)?;
            let src = fs::read_to_string(&self.test_file).unwrap_or_default();
            // Like forge 1.9 with dynamic test linking: byte offsets are shifted
            // by the rewrite of `new OZVault(...)`; line and column are right.
            let errors: Vec<CompileError> = src
                .match_indices("target.nope()")
                .map(|(i, _)| {
                    let before = &src[..i];
                    let line = before.matches('\n').count() + 1;
                    let col = i - before.rfind('\n').map_or(0, |n| n + 1) + 1;
                    CompileError {
                        file: "test/generated/OZVault.inv.t.sol".into(),
                        start: i + 368,
                        end: i + 381,
                        line: Some(line),
                        col: Some(col),
                        message: "Member \"nope\" not found".into(),
                    }
                })
                .collect();
            Ok(BuildJson {
                ok: errors.is_empty(),
                errors,
                output: String::new(),
            })
        }
        fn test(&self, repo: &Path, test_file: &str) -> Result<TestResult> {
            // Mutants run in a copy of the project; the contract itself never changes.
            assert_eq!(fs::read_to_string(&self.contract)?, SOURCE);
            let src = fs::read_to_string(repo.join("src/OZVault.sol"))?;
            let tests = fs::read_to_string(repo.join(test_file))?;
            let mut r = TestResult {
                ran: true,
                calls: Some(2048),
                reverts: Some(512),
                ..Default::default()
            };
            for name in ["solvency", "wrong", "fixed"] {
                let f = format!("invariant_{name}");
                if !tests.contains(&format!("function {f}()")) {
                    continue;
                }
                let fails = name == "wrong" || (name == "solvency" && !src.contains("a > 10"));
                if fails {
                    r.failed.push(Failure {
                        name: f,
                        reason: "assertion failed: 1 > 0".into(),
                    });
                } else {
                    r.passed.push(f);
                }
            }
            Ok(r)
        }
    }

    fn setup() -> (tempfile::TempDir, FakeForge) {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir_all(dir.path().join("src")).unwrap();
        fs::write(dir.path().join("src/OZVault.sol"), SOURCE).unwrap();
        let forge = FakeForge {
            contract: dir.path().join("src/OZVault.sol"),
            test_file: dir.path().join("test/generated/OZVault.inv.t.sol"),
            builds: RefCell::new(0),
        };
        (dir, forge)
    }

    fn opts() -> InvOptions {
        InvOptions {
            base: Options {
                max_tries: 0,
                max_mutants: 50,
                mutation: true,
            },
            max_repairs: 2,
            max_source_chars: 12_000,
            plan_attempts: 2,
            max_invariants: plan::MAX_INVARIANTS,
            reject_never_failing: true,
            replace_rounds: 2,
            hints: true,
            exit_checks: true,
        }
    }

    const PLAN: &str = r#"{"constructor": [{"param": "asset_", "value": "mock_token"}],
        "invariants": [
          {"id": "solvency", "statement": "pays out", "assert": "assertLe(target.convertToAssets(target.totalSupply()), target.totalAssets());"},
          {"id": "wrong", "statement": "always zero", "assert": "assertEq(target.totalSupply(), 0);"},
          {"id": "fixed", "statement": "needs a repair", "assert": "assertEq(target.nope(), 0);"},
          {"id": "hopeless", "statement": "never compiles", "assert": "assertEq(target.nope(), 1);"}
        ]}"#;

    #[test]
    fn plans_repairs_drops_runs_and_scores() {
        let (dir, forge) = setup();
        let model = Scripted::new(&[
            "not json at all",
            PLAN,
            // Repairs, one round at a time: both broken invariants fail together.
            r#"{"assert": "assertLe(target.totalSupply(), handler.sumBalanceOf())"}"#,
            // A fix that can never fail is refused and costs the repair.
            r#"{"assert": "assertGe(target.totalSupply(), 0)"}"#,
            r#"{"assert": "assertEq(target.nope(), 3)"}"#,
        ]);

        let r = run(
            dir.path(),
            Path::new("src/OZVault.sol"),
            &model,
            &forge,
            &opts(),
        )
        .unwrap();

        // The first answer was not JSON, so the plan took two calls.
        assert!(model.prompts.borrow()[1].contains("previous answer was rejected"));
        assert_eq!(r.proposed, 4);
        let kept: Vec<_> = r.kept.iter().map(|i| i.id.as_str()).collect();
        assert_eq!(kept, ["solvency", "wrong", "fixed"]);
        assert_eq!(r.dropped.len(), 1);
        assert_eq!(r.dropped[0].id, "hopeless");
        assert_eq!(r.repairs, 3);
        assert_eq!(r.repairs_refused, 1);
        // The fixture is not a whole ERC-4626 interface, so no rules or exit
        // checks were added.
        assert!(r.hints.is_empty());
        assert!(r.exit_checks.is_empty());
        assert!(!model.prompts.borrow()[0].contains("Rules from the standard"));
        assert!(r.rejected.is_empty());
        // The repair prompt carried the compiler error and the available names.
        let repair = &model.prompts.borrow()[2];
        assert!(repair.contains("Member \"nope\" not found"));
        assert!(repair.contains("handler: sumBalanceOf()"));
        assert!(repair.contains("- alice, bob, carol: the three users' addresses"));
        // The next repair of `hopeless` was told why its last fix was refused.
        let again = &model.prompts.borrow()[4];
        assert!(again.contains("was refused: it can never fail"));
        assert!(again.contains("`target.totalSupply()` is unsigned"));
        // Clean run: `wrong` fails on the unchanged contract.
        assert_eq!(r.flagged, ["invariant_wrong"]);
        assert_eq!(r.passed_on_clean, ["invariant_solvency", "invariant_fixed"]);
        assert_eq!((r.calls, r.reverts), (Some(2048), Some(512)));
        // Mutation: the `>` mutant breaks `solvency`, an assertion kill.
        let m = r.mutation.unwrap();
        assert_eq!(m.caught_by_assertion, 1);
        // The contract is restored and the final test file holds the kept invariants.
        assert_eq!(
            fs::read_to_string(dir.path().join("src/OZVault.sol")).unwrap(),
            SOURCE
        );
        let tests =
            fs::read_to_string(dir.path().join("test/generated/OZVault.inv.t.sol")).unwrap();
        assert!(tests.contains("assertLe(target.totalSupply(), handler.sumBalanceOf()); // model"));
        assert!(!tests.contains("assertGe(target.totalSupply(), 0)"));
        assert!(!tests.contains("nope"));
        assert!(dir.path().join("test/generated/AuswegToken.sol").exists());
    }

    /// The shape of the first qwen2.5-coder:14b run: most of the plan can never fail.
    const NEVER_FAILING_PLAN: &str = r#"{"constructor": [{"param": "asset_", "value": "mock_token"}],
        "invariants": [
          {"id": "nonneg", "statement": "assets are never negative", "assert": "assertGe(target.totalAssets(), 0);"},
          {"id": "selfeq", "statement": "supply equals itself", "assert": "assertEq(target.totalSupply(), target.totalSupply());"},
          {"id": "solvency", "statement": "pays out", "assert": "assertLe(target.convertToAssets(target.totalSupply()), target.totalAssets());"}
        ]}"#;

    #[test]
    fn refuses_what_can_never_fail_and_asks_for_others() {
        let (dir, forge) = setup();
        let model = Scripted::new(&[
            NEVER_FAILING_PLAN,
            // Round 1: one repeat, one good, one that can never fail again.
            r#"{"invariants": [
              {"id": "solvency", "statement": "again", "assert": "assertLe(target.convertToAssets(target.totalSupply()), target.totalAssets())"},
              {"id": "fixed", "statement": "supply is backed", "assert": "assertLe(target.totalSupply(), handler.sumBalanceOf())"},
              {"id": "still", "statement": "still never fails", "assert": "assertTrue(target.totalSupply() >= 0)"}]}"#,
            // Round 2: asked for one.
            r#"{"invariants": [{"id": "wrong", "statement": "always zero", "assert": "assertEq(target.totalSupply(), 0)"}]}"#,
        ]);
        let r = run(
            dir.path(),
            Path::new("src/OZVault.sol"),
            &model,
            &forge,
            &opts(),
        )
        .unwrap();

        let rejected: Vec<_> = r.rejected.iter().map(|x| x.id.as_str()).collect();
        assert_eq!(rejected, ["nonneg", "selfeq", "still"]);
        assert_eq!(r.replace_calls, 2);
        assert_eq!(r.replacements, 3);
        let kept: Vec<_> = r.kept.iter().map(|i| i.id.as_str()).collect();
        assert_eq!(kept, ["solvency", "fixed", "wrong"]);
        assert!(r.notes.iter().any(|n| n.contains("repeats `solvency`")));
        // Round 1 was asked for two, with both refusals and the kept invariant named.
        let first = &model.prompts.borrow()[1];
        assert!(first.contains("Propose up to 2 different invariants"));
        assert!(first.contains("- nonneg: assertGe(target.totalAssets(), 0);"));
        assert!(first.contains("- solvency: assertLe("));
        assert!(model.prompts.borrow()[2].contains("Propose up to 1 different"));
        assert_eq!(r.flagged, ["invariant_wrong"]);
        assert_eq!(r.passed_on_clean, ["invariant_solvency", "invariant_fixed"]);

        // Switched off, the same plan is used as it is, as in version 0.2.0.
        let (dir, forge) = setup();
        let model = Scripted::new(&[NEVER_FAILING_PLAN]);
        let off = InvOptions {
            reject_never_failing: false,
            ..opts()
        };
        let r = run(
            dir.path(),
            Path::new("src/OZVault.sol"),
            &model,
            &forge,
            &off,
        )
        .unwrap();
        assert!(r.rejected.is_empty());
        assert_eq!(r.kept.len(), 3);
        assert_eq!(model.prompts.borrow().len(), 1);
    }

    #[test]
    fn a_harness_error_is_reported_as_ausweg_s_not_the_model_s() {
        let (dir, _) = setup();
        struct Broken;
        impl Forge for Broken {
            fn build(&self, _: &Path) -> Result<BuildResult> {
                unreachable!()
            }
            fn build_json(&self, repo: &Path) -> Result<BuildJson> {
                let art = repo.join("out/OZVault.sol");
                fs::create_dir_all(&art)?;
                fs::write(art.join("OZVault.json"), OZ_VAULT_ABI)?;
                let generated = repo.join("test/generated/OZVault.inv.t.sol").exists();
                Ok(BuildJson {
                    ok: !generated,
                    errors: if generated {
                        vec![CompileError {
                            file: "test/generated/OZVault.inv.t.sol".into(),
                            start: 5,
                            end: 6,
                            line: Some(1),
                            col: Some(6),
                            message: "harness bug".into(),
                        }]
                    } else {
                        vec![]
                    },
                    output: String::new(),
                })
            }
            fn test(&self, _: &Path, _: &str) -> Result<TestResult> {
                unreachable!()
            }
        }
        let model = Scripted::new(&[PLAN]);
        let err = run(
            dir.path(),
            Path::new("src/OZVault.sol"),
            &model,
            &Broken,
            &opts(),
        )
        .unwrap_err();
        assert!(err.to_string().contains("a ausweg limitation"));
        assert!(
            dir.path()
                .join("test/generated/OZVault.inv.t.sol.failed")
                .exists()
        );
    }

    #[test]
    fn finds_the_declaration_line() {
        assert_eq!(
            declaration(SOURCE, "OZVault"),
            "contract OZVault is ERC4626"
        );
        assert_eq!(
            declaration("abstract contract X is Y {", "X"),
            "abstract contract X is Y"
        );
        assert_eq!(declaration("", "Z"), "contract Z");
    }
}
