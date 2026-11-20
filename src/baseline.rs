//! Milestone 1, design A: one prompt per contract, compile-repair loop, run on
//! clean code, then score with mutants. Its numbers are the baseline every
//! later milestone is measured against. `score_existing` runs the same checks
//! on a test file already on disk, without calling the model.

use crate::forge::{FailKind, Failure, Forge};
use crate::model::Model;
use crate::mutate;
use crate::prompt;
use anyhow::{Context, Result, bail};
use serde::Serialize;
use std::fs;
use std::path::{Path, PathBuf};

pub struct Options {
    pub max_tries: usize,
    pub max_mutants: usize,
    pub mutation: bool,
}

#[derive(Debug, Serialize)]
pub struct Report {
    pub contract: String,
    pub test_file: String,
    /// Model that wrote the tests; None when scoring an existing file.
    pub model: Option<String>,
    /// Model calls until the file compiled (1 = first try). None = never compiled.
    /// Some(0) for an existing file.
    pub compiled_after: Option<usize>,
    pub passed_on_clean: Vec<String>,
    /// Fail on unchanged code: a real bug or a wrong property; a person decides.
    pub flagged: Vec<String>,
    pub mutation: Option<MutationScore>,
}

#[derive(Debug, Serialize)]
pub struct MutationScore {
    pub mutants: usize,
    /// A test that passes on clean code failed an assertion: the property caught the bug.
    pub caught_by_assertion: usize,
    /// Tests failed only because the code reverted. Calling the code was enough;
    /// a test with no assertions would have caught these too.
    pub caught_by_revert_only: usize,
    pub survived: usize,
    /// The mutant did not compile; excluded from both rates.
    pub invalid: usize,
    /// caught_by_assertion / valid mutants: what the properties themselves check.
    pub assertion_kill_rate: Option<f64>,
    /// (caught_by_assertion + caught_by_revert_only) / valid mutants.
    pub kill_rate: Option<f64>,
    pub detail: Vec<MutantOutcome>,
}

#[derive(Debug, Serialize)]
pub struct MutantOutcome {
    pub line: usize,
    pub change: String,
    pub outcome: Outcome,
    /// Clean-passing tests that failed an assertion on this mutant.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub assertion_kills: Vec<String>,
    /// Clean-passing tests that only reverted on this mutant.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub revert_kills: Vec<String>,
}

#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Outcome {
    Assertion,
    RevertOnly,
    Survived,
    Invalid,
}

/// Where ausweg before 0.6.4 kept the original contract while it wrote mutants
/// over it, e.g. `src/Bank.sol.ausweg-backup`. A run killed mid-mutation left
/// both behind. Mutants now go to a [`Sandbox`], so only an older run leaves one.
pub(crate) fn backup_path(contract_abs: &Path) -> PathBuf {
    let mut p = contract_abs.as_os_str().to_owned();
    p.push(".ausweg-backup");
    PathBuf::from(p)
}

/// A copy of the Foundry project in the system temp directory, where mutants
/// are written, so the project itself is never edited. Dependency folders are
/// linked, not copied; `.git`, `out` and `cache` stay behind, and forge builds
/// the copy afresh. Removed when dropped; a crash leaves it in the temp
/// directory, never in the project.
pub(crate) struct Sandbox {
    pub(crate) root: PathBuf,
}

/// Folders the sandbox links to instead of copying.
const LINKED: &[&str] = &["lib", "node_modules", "dependencies"];
/// Folders the sandbox leaves out.
const LEFT_OUT: &[&str] = &[".git", "out", "cache"];

impl Sandbox {
    pub(crate) fn new(repo: &Path) -> Result<Self> {
        let repo = fs::canonicalize(repo).with_context(|| format!("reading {}", repo.display()))?;
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let root =
            std::env::temp_dir().join(format!("ausweg-mutants-{}-{stamp}", std::process::id()));
        fs::create_dir_all(&root)?;
        // From here on, Drop removes the copy if anything fails.
        let sandbox = Self { root };
        for entry in fs::read_dir(&repo)? {
            let entry = entry?;
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if LEFT_OUT.contains(&name.as_ref()) {
                continue;
            }
            let to = sandbox.root.join(entry.file_name());
            if LINKED.contains(&name.as_ref()) {
                link(&fs::canonicalize(entry.path())?, &to)?;
            } else {
                copy_tree(&entry.path(), &to)?;
            }
        }
        Ok(sandbox)
    }
}

impl Drop for Sandbox {
    fn drop(&mut self) {
        // remove_dir_all removes a symbolic link, never what it points to: the
        // linked dependencies stay.
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[cfg(unix)]
fn link(target: &Path, at: &Path) -> Result<()> {
    std::os::unix::fs::symlink(target, at)
        .with_context(|| format!("linking {} to {}", at.display(), target.display()))
}

#[cfg(not(unix))]
fn link(target: &Path, at: &Path) -> Result<()> {
    copy_tree(target, at)
}

fn copy_tree(from: &Path, to: &Path) -> Result<()> {
    let meta = fs::symlink_metadata(from)?;
    if meta.file_type().is_symlink() {
        // Point at the same place from the copy: absolute when it resolves.
        let target = fs::canonicalize(from).or_else(|_| fs::read_link(from))?;
        link(&target, to)
    } else if meta.is_dir() {
        fs::create_dir_all(to)?;
        for e in fs::read_dir(from)? {
            let e = e?;
            copy_tree(&e.path(), &to.join(e.file_name()))?;
        }
        Ok(())
    } else {
        fs::copy(from, to).with_context(|| format!("copying {}", from.display()))?;
        Ok(())
    }
}

/// The contract under test, read after undoing an older version's interrupted run.
#[derive(Debug)]
pub(crate) struct Target {
    /// The path as given, relative to the project: the same in a [`Sandbox`].
    pub(crate) rel: PathBuf,
    pub(crate) source: String,
    pub(crate) name: String,
}

impl Target {
    pub(crate) fn open(repo: &Path, contract: &Path) -> Result<Self> {
        let abs = repo.join(contract);
        let backup = backup_path(&abs);
        if backup.exists() {
            let original = fs::read_to_string(&backup)
                .with_context(|| format!("reading {}", backup.display()))?;
            let current =
                fs::read_to_string(&abs).with_context(|| format!("reading {}", abs.display()))?;
            // Put the original back only over the original or one of its mutants:
            // anything else is an edit made since, and stays.
            let untouched = current == original
                || mutate::mutants(&original, usize::MAX)
                    .iter()
                    .any(|m| m.source == current);
            if !untouched {
                bail!(
                    "{} has a backup from an interrupted run of an older ausweg, {}, and the \
                     file has changed since that run: compare the two, keep the one you want, \
                     and delete the backup",
                    contract.display(),
                    backup.display()
                );
            }
            fs::rename(&backup, &abs).with_context(|| {
                format!("restoring {} from {}", abs.display(), backup.display())
            })?;
            eprintln!("  restored {} after an interrupted run", contract.display());
        }
        let source =
            fs::read_to_string(&abs).with_context(|| format!("reading {}", abs.display()))?;
        let name = contract
            .file_stem()
            .and_then(|s| s.to_str())
            .context("contract path has no file name")?
            .to_string();
        Ok(Self {
            rel: contract.to_path_buf(),
            source,
            name,
        })
    }
}

/// Design A: generate tests with the model, repair until they compile, then evaluate.
pub fn run(
    repo: &Path,
    contract: &Path,
    model: &dyn Model,
    forge: &dyn Forge,
    opts: &Options,
) -> Result<Report> {
    let target = Target::open(repo, contract)?;

    // test/generated/Vault.base.t.sol imports ../../src/Vault.sol
    let test_rel = PathBuf::from("test/generated").join(format!("{}.base.t.sol", target.name));
    let import_path = format!("../../{}", contract.display());
    fs::create_dir_all(repo.join("test/generated"))?;
    let test_abs = repo.join(&test_rel);
    let test_rel_str = test_rel.display().to_string();

    let mut report = Report {
        contract: contract.display().to_string(),
        test_file: test_rel_str.clone(),
        model: Some(model.name()),
        compiled_after: None,
        passed_on_clean: vec![],
        flagged: vec![],
        mutation: None,
    };

    // Generate, then compile-and-repair.
    let mut test_src = prompt::extract_solidity(&model.complete(&prompt::baseline(
        &target.name,
        &import_path,
        &target.source,
    ))?);
    for attempt in 1..=opts.max_tries {
        fs::write(&test_abs, &test_src)?;
        let build = forge.build(repo)?;
        if build.ok {
            report.compiled_after = Some(attempt);
            break;
        }
        eprintln!("  attempt {attempt}/{}: does not compile", opts.max_tries);
        if attempt < opts.max_tries {
            test_src = prompt::extract_solidity(
                &model.complete(&prompt::repair(&test_src, &build.output))?,
            );
        }
    }
    if report.compiled_after.is_none() {
        // Leave the last attempt on disk for debugging, but out of the build.
        fs::rename(&test_abs, test_abs.with_extension("sol.failed"))?;
        return Ok(report);
    }

    evaluate(repo, &target, &test_rel_str, forge, opts, &mut report)?;
    Ok(report)
}

/// Evaluate a test file already on disk: no model, same clean run and mutants.
pub fn score_existing(
    repo: &Path,
    contract: &Path,
    test_file: &Path,
    forge: &dyn Forge,
    opts: &Options,
) -> Result<Report> {
    let target = Target::open(repo, contract)?;
    if !repo.join(test_file).is_file() {
        bail!("test file {} not found", repo.join(test_file).display());
    }
    let build = forge.build(repo)?;
    if !build.ok {
        bail!("the project does not compile:\n{}", build.output);
    }
    let test_rel_str = test_file.display().to_string();
    let mut report = Report {
        contract: contract.display().to_string(),
        test_file: test_rel_str.clone(),
        model: None,
        compiled_after: Some(0),
        passed_on_clean: vec![],
        flagged: vec![],
        mutation: None,
    };
    evaluate(repo, &target, &test_rel_str, forge, opts, &mut report)?;
    Ok(report)
}

/// Run the tests on clean code, then score them against mutants of the contract.
fn evaluate(
    repo: &Path,
    target: &Target,
    test_file: &str,
    forge: &dyn Forge,
    opts: &Options,
    report: &mut Report,
) -> Result<()> {
    let clean = forge.test(repo, test_file)?;
    if !clean.ran {
        bail!("tests compiled but did not run:\n{}", clean.output);
    }
    report.flagged = clean.failed_names();
    report.passed_on_clean = clean.passed;

    if opts.mutation && !report.passed_on_clean.is_empty() {
        report.mutation = Some(score(
            repo,
            target,
            test_file,
            &report.passed_on_clean,
            forge,
            opts,
        )?);
    }
    Ok(())
}

pub(crate) fn score(
    repo: &Path,
    target: &Target,
    test_file: &str,
    clean_passing: &[String],
    forge: &dyn Forge,
    opts: &Options,
) -> Result<MutationScore> {
    let ms = mutate::mutants(&target.source, opts.max_mutants);
    // Mutants go to a copy of the project: the contract itself is never edited.
    let sandbox = Sandbox::new(repo)?;
    let file = sandbox.root.join(&target.rel);
    // `assertTrue(x, "msg")` fails with just `msg`: the test's own messages say
    // which failures are assertions.
    let test_src = fs::read_to_string(repo.join(test_file)).unwrap_or_default();
    let messages = crate::forge::assertion_messages(&test_src, &target.source);

    let mut detail = Vec::with_capacity(ms.len());
    for m in &ms {
        fs::write(&file, &m.source)?;
        let r = forge.test(&sandbox.root, test_file)?;
        // Only tests that passed on clean code count. A test that already failed
        // would otherwise "catch" every mutant.
        let caught: Vec<_> = r
            .failed
            .iter()
            .filter(|f| clean_passing.contains(&f.name))
            .collect();
        let outcome = if !r.ran {
            Outcome::Invalid
        } else if caught.is_empty() {
            Outcome::Survived
        } else if caught
            .iter()
            .any(|f| f.kind_with(&messages) == FailKind::Assertion)
        {
            Outcome::Assertion
        } else {
            Outcome::RevertOnly
        };
        let (by_assertion, by_revert): (Vec<&Failure>, Vec<&Failure>) = caught
            .iter()
            .partition(|f| f.kind_with(&messages) == FailKind::Assertion);
        detail.push(MutantOutcome {
            line: m.line,
            change: m.change.clone(),
            outcome,
            assertion_kills: by_assertion.iter().map(|f| f.name.clone()).collect(),
            revert_kills: by_revert.iter().map(|f| f.name.clone()).collect(),
        });
    }

    let count = |o: Outcome| detail.iter().filter(|d| d.outcome == o).count();
    let (assertion, revert_only) = (count(Outcome::Assertion), count(Outcome::RevertOnly));
    let (survived, invalid) = (count(Outcome::Survived), count(Outcome::Invalid));
    let valid = assertion + revert_only + survived;
    let rate = |n: usize| (valid > 0).then(|| n as f64 / valid as f64);
    Ok(MutationScore {
        mutants: ms.len(),
        caught_by_assertion: assertion,
        caught_by_revert_only: revert_only,
        survived,
        invalid,
        assertion_kill_rate: rate(assertion),
        kill_rate: rate(assertion + revert_only),
        detail,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::forge::{BuildResult, Failure, TestResult};
    use crate::model::Scripted;
    use std::cell::Cell;

    const VAULT: &str = "pragma solidity ^0.8.0;\ncontract Vault {\n    uint public total;\n    function deposit(uint a) public { total += a; }\n    function cap(uint a) public pure returns (bool) { return a > 10; }\n}\n";

    /// Fake forge with three tests, modelled on the real Bank run:
    /// - testFuzz_deposit reverts (underflow panic) under the `+=` -> `-=` mutant;
    /// - testFuzz_cap fails an assertion under the `>` -> `>=` mutant;
    /// - testFuzz_broken fails an assertion on clean code, so it must never count.
    struct FakeForge {
        fail_builds: Cell<usize>,
        /// The user's own copy of the contract: no test run may see it changed.
        contract: PathBuf,
        /// Test runs in a project other than the user's: the sandbox.
        elsewhere: Cell<usize>,
    }
    impl Forge for FakeForge {
        fn build(&self, _: &Path) -> Result<BuildResult> {
            let left = self.fail_builds.get();
            if left > 0 {
                self.fail_builds.set(left - 1);
                return Ok(BuildResult {
                    ok: false,
                    output: "Error (7576): Undeclared identifier `vault`.".into(),
                });
            }
            Ok(BuildResult {
                ok: true,
                output: String::new(),
            })
        }
        fn test(&self, repo: &Path, _: &str) -> Result<TestResult> {
            // The user's file is never a mutant, whichever project the tests run in.
            assert_eq!(fs::read_to_string(&self.contract)?, VAULT);
            let user_repo = self.contract.parent().unwrap().parent().unwrap();
            if fs::canonicalize(repo)? != fs::canonicalize(user_repo)? {
                self.elsewhere.set(self.elsewhere.get() + 1);
            }
            let src = fs::read_to_string(repo.join("src/Vault.sol"))?;
            let mut r = TestResult {
                ran: true,
                ..Default::default()
            };
            let mut fail = |name: &str, reason: &str| {
                r.failed.push(Failure {
                    name: name.into(),
                    reason: reason.into(),
                })
            };
            fail("testFuzz_broken", "assertion failed: 0 != 1");
            let deposit_ok = src.contains("total += a");
            let cap_ok = src.contains("a > 10");
            if !deposit_ok {
                fail(
                    "testFuzz_deposit",
                    "panic: arithmetic underflow or overflow (0x11)",
                );
            }
            if !cap_ok {
                fail("testFuzz_cap", "assertion failed: true != false");
            }
            if deposit_ok {
                r.passed.push("testFuzz_deposit".into());
            }
            if cap_ok {
                r.passed.push("testFuzz_cap".into());
            }
            Ok(r)
        }
    }

    fn setup() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir_all(dir.path().join("src")).unwrap();
        fs::write(dir.path().join("src/Vault.sol"), VAULT).unwrap();
        dir
    }

    fn opts() -> Options {
        Options {
            max_tries: 3,
            max_mutants: 50,
            mutation: true,
        }
    }

    fn forge(dir: &tempfile::TempDir, fail_builds: usize) -> FakeForge {
        FakeForge {
            fail_builds: Cell::new(fail_builds),
            contract: dir.path().join("src/Vault.sol"),
            elsewhere: Cell::new(0),
        }
    }

    #[test]
    fn mutants_run_in_a_copy_and_the_contract_is_never_edited() {
        let dir = setup();
        fs::create_dir_all(dir.path().join("test")).unwrap();
        fs::write(dir.path().join("test/Mine.t.sol"), "contract Mine {}").unwrap();
        let f = forge(&dir, 0);
        let r = score_existing(
            dir.path(),
            Path::new("src/Vault.sol"),
            Path::new("test/Mine.t.sol"),
            &f,
            &opts(),
        )
        .unwrap();
        // The clean run is in the project; both mutants ran in the copy, and
        // the fake checked before each run that the contract was untouched.
        assert_eq!(r.mutation.unwrap().mutants, 2);
        assert_eq!(f.elsewhere.get(), 2);
        assert!(!dir.path().join("src/Vault.sol.ausweg-backup").exists());
    }

    #[test]
    fn the_copy_links_dependencies_and_removing_it_keeps_them() {
        let dir = setup();
        let p = dir.path();
        fs::create_dir_all(p.join("lib/dep/src")).unwrap();
        fs::write(p.join("lib/dep/src/D.sol"), "contract D {}").unwrap();
        fs::create_dir_all(p.join("test/generated")).unwrap();
        fs::write(p.join("test/generated/V.proof.t.sol"), "contract P {}").unwrap();
        fs::write(p.join("foundry.toml"), "[profile.default]\n").unwrap();
        for d in [".git", "out", "cache"] {
            fs::create_dir_all(p.join(d)).unwrap();
            fs::write(p.join(d).join("x"), "x").unwrap();
        }
        let root = {
            let s = Sandbox::new(p).unwrap();
            let root = s.root.clone();
            assert_eq!(
                fs::read_to_string(root.join("src/Vault.sol")).unwrap(),
                VAULT
            );
            assert!(root.join("test/generated/V.proof.t.sol").is_file());
            assert!(root.join("foundry.toml").is_file());
            assert!(
                fs::symlink_metadata(root.join("lib"))
                    .unwrap()
                    .file_type()
                    .is_symlink()
            );
            assert!(root.join("lib/dep/src/D.sol").is_file());
            for d in [".git", "out", "cache"] {
                assert!(!root.join(d).exists(), "{d} copied");
            }
            // A mutant in the copy leaves the project alone.
            fs::write(root.join("src/Vault.sol"), "mutant").unwrap();
            assert_eq!(fs::read_to_string(p.join("src/Vault.sol")).unwrap(), VAULT);
            root
        };
        assert!(!root.exists(), "copy not removed");
        assert_eq!(
            fs::read_to_string(p.join("lib/dep/src/D.sol")).unwrap(),
            "contract D {}"
        );
    }

    #[test]
    fn an_old_backup_never_overwrites_an_edited_contract() {
        let dir = setup();
        let contract = dir.path().join("src/Vault.sol");
        let backup = dir.path().join("src/Vault.sol.ausweg-backup");
        // An older ausweg was interrupted, and then the user edited the contract.
        let edited = VAULT.replace(
            "uint public total;",
            "uint public total;\n    uint public fee;",
        );
        fs::write(&contract, &edited).unwrap();
        fs::write(&backup, VAULT).unwrap();
        let err = Target::open(dir.path(), Path::new("src/Vault.sol")).unwrap_err();
        assert!(err.to_string().contains("changed since that run"), "{err}");
        assert_eq!(fs::read_to_string(&contract).unwrap(), edited);
        assert!(backup.exists());
    }

    #[test]
    fn repairs_then_scores_and_restores_contract() {
        let dir = setup();
        let model = Scripted::new(&[
            "```solidity\ncontract Broken {}\n```",
            "```solidity\ncontract Fixed {}\n```",
        ]);

        let r = run(
            dir.path(),
            Path::new("src/Vault.sol"),
            &model,
            &forge(&dir, 1),
            &opts(),
        )
        .unwrap();

        assert_eq!(r.compiled_after, Some(2));
        // The repair prompt carried the compiler error back to the model.
        assert!(model.prompts.borrow()[1].contains("Undeclared identifier"));
        assert_eq!(
            fs::read_to_string(dir.path().join("test/generated/Vault.base.t.sol")).unwrap(),
            "contract Fixed {}\n"
        );
        assert_eq!(r.flagged, vec!["testFuzz_broken"]);
        // Contract is back to the original after scoring, and the backup is gone.
        assert_eq!(
            fs::read_to_string(dir.path().join("src/Vault.sol")).unwrap(),
            VAULT
        );
        assert!(!dir.path().join("src/Vault.sol.ausweg-backup").exists());
    }

    #[test]
    fn splits_kills_by_assertion_and_by_revert() {
        let dir = setup();
        let model = Scripted::new(&["contract T {}"]);

        let r = run(
            dir.path(),
            Path::new("src/Vault.sol"),
            &model,
            &forge(&dir, 0),
            &opts(),
        )
        .unwrap();

        let m = r.mutation.unwrap();
        let outcomes: Vec<_> = m.detail.iter().map(|d| (d.line, d.outcome)).collect();
        // Line 4 (`+=` -> `-=`): only a revert, even though testFuzz_broken failed
        // an assertion, because it was already failing on clean code.
        // Line 5 (`>` -> `>=`): a real assertion caught it.
        assert_eq!(
            outcomes,
            vec![(4, Outcome::RevertOnly), (5, Outcome::Assertion)]
        );
        assert_eq!((m.caught_by_assertion, m.caught_by_revert_only), (1, 1));
        // Each mutant names the tests that caught it, by kind; the test that
        // already failed on clean code is not among them.
        assert_eq!(m.detail[0].revert_kills, ["testFuzz_deposit"]);
        assert!(m.detail[0].assertion_kills.is_empty());
        assert_eq!(m.detail[1].assertion_kills, ["testFuzz_cap"]);
        assert_eq!(m.assertion_kill_rate, Some(0.5));
        assert_eq!(m.kill_rate, Some(1.0));
    }

    #[test]
    fn scores_an_existing_test_file_without_the_model() {
        let dir = setup();
        fs::create_dir_all(dir.path().join("test")).unwrap();
        fs::write(dir.path().join("test/Mine.t.sol"), "contract Mine {}").unwrap();

        let r = score_existing(
            dir.path(),
            Path::new("src/Vault.sol"),
            Path::new("test/Mine.t.sol"),
            &forge(&dir, 0),
            &opts(),
        )
        .unwrap();

        assert_eq!(r.model, None);
        assert_eq!(r.test_file, "test/Mine.t.sol");
        assert_eq!(r.flagged, vec!["testFuzz_broken"]);
        assert_eq!(r.mutation.unwrap().caught_by_assertion, 1);
        assert_eq!(
            fs::read_to_string(dir.path().join("src/Vault.sol")).unwrap(),
            VAULT
        );
    }

    #[test]
    fn score_existing_rejects_a_missing_test_file() {
        let dir = setup();
        let err = score_existing(
            dir.path(),
            Path::new("src/Vault.sol"),
            Path::new("test/Nope.t.sol"),
            &forge(&dir, 0),
            &opts(),
        )
        .unwrap_err();
        assert!(err.to_string().contains("not found"));
    }

    #[test]
    fn restores_contract_left_mutated_by_an_interrupted_run() {
        let dir = setup();
        let contract = dir.path().join("src/Vault.sol");
        // What a killed run leaves behind: a mutant in place, the original in the backup.
        fs::write(&contract, VAULT.replace("+=", "-=")).unwrap();
        fs::write(dir.path().join("src/Vault.sol.ausweg-backup"), VAULT).unwrap();
        let model = Scripted::new(&["contract T {}"]);

        let r = run(
            dir.path(),
            Path::new("src/Vault.sol"),
            &model,
            &forge(&dir, 0),
            &opts(),
        )
        .unwrap();

        // The model was shown the original, not the mutant.
        assert!(model.prompts.borrow()[0].contains("total += a"));
        assert_eq!(fs::read_to_string(&contract).unwrap(), VAULT);
        assert!(!dir.path().join("src/Vault.sol.ausweg-backup").exists());
        assert_eq!(r.mutation.unwrap().mutants, 2);
    }

    #[test]
    fn gives_up_after_max_tries_and_moves_file_aside() {
        let dir = setup();
        let model = Scripted::new(&["contract A {}", "contract B {}", "contract C {}"]);

        let r = run(
            dir.path(),
            Path::new("src/Vault.sol"),
            &model,
            &forge(&dir, 99),
            &opts(),
        )
        .unwrap();

        assert_eq!(r.compiled_after, None);
        assert_eq!(model.prompts.borrow().len(), 3);
        assert!(!dir.path().join("test/generated/Vault.base.t.sol").exists());
        assert!(
            dir.path()
                .join("test/generated/Vault.base.t.sol.failed")
                .exists()
        );
    }
}
