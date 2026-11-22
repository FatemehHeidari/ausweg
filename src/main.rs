//! ausweg — property test generator for Solidity/Foundry.
//! Milestone 1: the design-A baseline (`ausweg baseline`) and the scorer it uses
//! (`ausweg score`). Milestone 2: invariants over a generated handler
//! (`ausweg invariants`).

mod abi;
mod asyncproof;
mod baseline;
mod forge;
mod invariants;
mod model;
mod mutate;
mod plan;
mod prompt;
mod prove;
mod scaffold;
mod smt;
mod vacuous;

use anyhow::Result;
use baseline::{MutationScore, Outcome, Report};
use clap::{Args, Parser, Subcommand};
use std::path::{Path, PathBuf};
use std::time::Duration;

#[derive(Parser)]
#[command(
    version,
    about = "Proves every user can always get out of an ERC-4626 or ERC-7540 vault; also writes Foundry property tests with an LLM"
)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Design A baseline: one prompt per contract, compile-repair, run, mutation score.
    Baseline {
        /// Foundry project root.
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        /// Contract file, relative to the repo, e.g. src/Vault.sol. Repeatable.
        #[arg(long = "contract", required = true)]
        contracts: Vec<PathBuf>,
        /// Ollama model tag.
        #[arg(long, default_value = "qwen2.5-coder:7b")]
        model: String,
        #[arg(long, default_value = "http://localhost:11434")]
        ollama_url: String,
        /// Model context window in tokens. Ollama drops the start of longer
        /// prompts, so raise this for large contracts (uses more memory).
        #[arg(long, default_value_t = 8192)]
        num_ctx: u32,
        /// Per-call timeout in seconds; local models on CPU are slow.
        #[arg(long, default_value_t = 600)]
        timeout: u64,
        /// Model calls allowed to get a compiling file (first try included).
        #[arg(long, default_value_t = 3)]
        max_tries: usize,
        #[command(flatten)]
        check: CheckArgs,
    },
    /// Milestone 2: the tool writes the setup and a handler; the model writes invariants.
    Invariants {
        /// Foundry project root.
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        /// Contract file, relative to the repo, e.g. src/OZVault.sol. Repeatable.
        /// The contract must be named after its file.
        #[arg(long = "contract", required = true)]
        contracts: Vec<PathBuf>,
        /// Ollama model tag.
        #[arg(long, default_value = "qwen2.5-coder:14b")]
        model: String,
        #[arg(long, default_value = "http://localhost:11434")]
        ollama_url: String,
        /// Model context window in tokens.
        #[arg(long, default_value_t = 16384)]
        num_ctx: u32,
        /// Per-call timeout in seconds; local models on CPU are slow.
        #[arg(long, default_value_t = 600)]
        timeout: u64,
        /// Model repair calls allowed per invariant before it is dropped.
        #[arg(long, default_value_t = 3)]
        max_repairs: usize,
        /// Sources longer than this go to the model as their function list only.
        #[arg(long, default_value_t = 30_000)]
        max_source_chars: usize,
        /// Invariants kept from the model's plan.
        #[arg(long, default_value_t = plan::MAX_INVARIANTS)]
        max_invariants: usize,
        /// Keep assertions that can never fail, such as `assertGe(x, 0)` on a
        /// uint256, instead of asking the model for others (as in 0.2.0).
        #[arg(long)]
        allow_never_failing: bool,
        /// Model calls allowed for replacing invariants that can never fail.
        #[arg(long, default_value_t = 2)]
        replace_rounds: usize,
        /// Leave the rules of standards the contract implements (ERC-4626) out of
        /// the prompt (as in 0.2.1).
        #[arg(long)]
        no_hints: bool,
        /// Leave out the tool's exit checks for ERC-4626 vaults (as in 0.2.3).
        #[arg(long)]
        no_exit_checks: bool,
        /// Invariant campaign runs, for the clean run and every mutant.
        #[arg(long, default_value_t = 32)]
        invariant_runs: u32,
        /// Calls per invariant run.
        #[arg(long, default_value_t = 64)]
        invariant_depth: u32,
        #[command(flatten)]
        check: CheckArgs,
    },
    /// Step 13: prove that every user can always get out of an ERC-4626 vault.
    /// Needs Halmos, and z3 for the integer back end.
    Prove {
        /// Foundry project root.
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        /// Contract file, relative to the repo, e.g. src/OZVault.sol. Repeatable.
        /// The contract must be named after its file.
        #[arg(long = "contract", required = true)]
        contracts: Vec<PathBuf>,
        #[arg(long, default_value = "halmos")]
        halmos: String,
        /// Seconds the solver may spend on one query.
        #[arg(long, default_value_t = 60)]
        solver_timeout: u64,
        /// Leave "share price >= 1" out of the invariant.
        #[arg(long)]
        no_price: bool,
        /// Limit every amount argument to 2^128. Larger amounts exceed any
        /// balance under the 2^96 supply cap; leaving them out keeps the solver
        /// away from mulDiv's 512-bit branch.
        #[arg(long)]
        bound_amounts: bool,
        /// `halmos --loop`: how far loops are unrolled (Halmos's default is 2).
        /// A check whose paths were cut at the bound is reported as incomplete,
        /// not proved.
        #[arg(long = "loop")]
        loop_bound: Option<u32>,
        /// Check the integer rewrite's answers against the original bit-vector
        /// query: `sample` (every model, and the unsat answers a seeded hash
        /// picks), `all` (every model and every unsat), or `off`. A model the
        /// checks cannot confirm becomes unknown; so does an unsat with `all`.
        #[arg(long, value_parser = ["sample", "all", "off"], default_value = "sample")]
        check_rewrite: String,
        /// With `--check-rewrite sample`: check one unsat answer in this many.
        #[arg(long, default_value_t = 16)]
        check_every: u64,
        /// With `--check-rewrite sample`: the seed that picks them.
        #[arg(long, default_value_t = 0)]
        check_seed: u64,
        /// Seconds all the checks of one answer may take together, within the
        /// query's own time; a check that runs out is inconclusive.
        #[arg(long, default_value_t = 10)]
        check_timeout: u64,
        /// Upper bound on mutants per contract, taken in source order.
        #[arg(long, default_value_t = 100)]
        max_mutants: usize,
        /// Skip mutation scoring.
        #[arg(long)]
        no_mutation: bool,
        #[arg(long, default_value = "forge")]
        forge_bin: String,
        /// Also write the JSON report here.
        #[arg(long)]
        json: Option<PathBuf>,
    },
    /// Compare solvers: run the same Halmos checks once with each one.
    Bench {
        /// Foundry project root.
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        /// Vault file, relative to the repo: benchmark its liquidity proof.
        /// Repeatable.
        #[arg(long = "contract", required_unless_present = "suites")]
        contracts: Vec<PathBuf>,
        /// Halmos tests already in the repo, as <test file>:<contract>, e.g.
        /// test/OZVault.a16z.t.sol:OZVaultA16z. Repeatable.
        #[arg(long = "suite")]
        suites: Vec<String>,
        /// Solvers to compare: `ausweg` (the integer back end) or any name
        /// `halmos --solver` accepts (yices, bitwuzla, z3, cvc5).
        #[arg(long, value_delimiter = ',', default_value = "yices,bitwuzla,ausweg")]
        solvers: Vec<String>,
        /// Run the checks whose name starts with this [default: check_exit
        /// for --contract, test for --suite].
        #[arg(long)]
        checks: Option<String>,
        /// `halmos --loop`: loop unrolling bound (a16z's suite needs 4).
        #[arg(long = "loop")]
        loop_bound: Option<u32>,
        /// Seconds per solver query, the same for every solver.
        #[arg(long, default_value_t = 60)]
        solver_timeout: u64,
        /// Wall-clock seconds one check may take with one solver.
        #[arg(long, default_value_t = 600)]
        cap: u64,
        /// Limit every amount argument to 2^128, as `ausweg prove --bound-amounts`.
        #[arg(long)]
        bound_amounts: bool,
        #[arg(long, default_value = "halmos")]
        halmos: String,
        #[arg(long, default_value = "forge")]
        forge_bin: String,
        /// Also write the JSON report here.
        #[arg(long)]
        json: Option<PathBuf>,
    },
    /// Integer back end for Halmos: answers one query file. `ausweg prove` passes
    /// it to Halmos as the solver.
    #[command(hide = true)]
    Smt {
        /// The query Halmos wrote.
        file: PathBuf,
    },
    /// Score a test file you already have: run it on clean code, then on mutants.
    Score {
        /// Foundry project root.
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        /// Contract the tests target, relative to the repo, e.g. src/Bank.sol.
        #[arg(long)]
        contract: PathBuf,
        /// Test file, relative to the repo, e.g. test/generated/Bank.base.t.sol.
        #[arg(long)]
        test: PathBuf,
        #[command(flatten)]
        check: CheckArgs,
    },
}

/// Options shared by both commands: how tests are run and scored.
#[derive(Args)]
struct CheckArgs {
    /// Upper bound on mutants per contract, taken in source order.
    #[arg(long, default_value_t = 100)]
    max_mutants: usize,
    /// Skip mutation scoring.
    #[arg(long)]
    no_mutation: bool,
    #[arg(long, default_value = "forge")]
    forge_bin: String,
    /// Fuzz seed passed to every `forge test`, so runs are reproducible.
    #[arg(long, default_value = "1")]
    fuzz_seed: String,
    /// Also write the JSON report here.
    #[arg(long)]
    json: Option<PathBuf>,
}

impl CheckArgs {
    fn setup(&self, max_tries: usize) -> (forge::ForgeCli, baseline::Options) {
        self.setup_with_env(max_tries, Vec::new())
    }

    fn setup_with_env(
        &self,
        max_tries: usize,
        env: Vec<(String, String)>,
    ) -> (forge::ForgeCli, baseline::Options) {
        (
            forge::ForgeCli {
                bin: self.forge_bin.clone(),
                fuzz_seed: Some(self.fuzz_seed.clone()),
                env,
            },
            baseline::Options {
                max_tries,
                max_mutants: self.max_mutants,
                mutation: !self.no_mutation,
            },
        )
    }
}

fn main() -> Result<()> {
    match Cli::parse().cmd {
        Cmd::Baseline {
            repo,
            contracts,
            model,
            ollama_url,
            num_ctx,
            timeout,
            max_tries,
            check,
        } => {
            let model =
                model::Ollama::new(&ollama_url, &model, num_ctx, Duration::from_secs(timeout));
            let (forge, opts) = check.setup(max_tries);
            let mut reports = Vec::new();
            for c in &contracts {
                eprintln!("{}:", c.display());
                let r = baseline::run(&repo, c, &model, &forge, &opts)?;
                print_summary(&r);
                reports.push(r);
            }
            write_json(check.json.as_deref(), &reports)?;
        }
        Cmd::Invariants {
            repo,
            contracts,
            model,
            ollama_url,
            num_ctx,
            timeout,
            max_repairs,
            max_source_chars,
            max_invariants,
            allow_never_failing,
            replace_rounds,
            no_hints,
            no_exit_checks,
            invariant_runs,
            invariant_depth,
            check,
        } => {
            let model =
                model::Ollama::new(&ollama_url, &model, num_ctx, Duration::from_secs(timeout));
            let env = vec![
                (
                    "FOUNDRY_INVARIANT_RUNS".to_string(),
                    invariant_runs.to_string(),
                ),
                (
                    "FOUNDRY_INVARIANT_DEPTH".to_string(),
                    invariant_depth.to_string(),
                ),
                (
                    "FOUNDRY_INVARIANT_FAIL_ON_REVERT".to_string(),
                    "false".to_string(),
                ),
            ];
            let (forge, base) = check.setup_with_env(0, env);
            let opts = invariants::InvOptions {
                base,
                max_repairs,
                max_source_chars,
                plan_attempts: 3,
                max_invariants,
                reject_never_failing: !allow_never_failing,
                replace_rounds,
                hints: !no_hints,
                exit_checks: !no_exit_checks,
            };
            let mut reports = Vec::new();
            let mut failed = Vec::new();
            for c in &contracts {
                eprintln!("{}:", c.display());
                match invariants::run(&repo, c, &model, &forge, &opts) {
                    Ok(r) => {
                        print_invariant_summary(&r);
                        reports.push(r);
                    }
                    Err(e) => {
                        // One contract failing should not cost the others' results.
                        println!("## {}: failed\n- {e:#}", c.display());
                        failed.push(serde_json::json!({
                            "contract": c.display().to_string(),
                            "error": format!("{e:#}"),
                        }));
                    }
                }
            }
            if let Some(path) = check.json.as_deref() {
                let all = serde_json::json!({ "reports": reports, "failed": failed });
                std::fs::write(path, serde_json::to_string_pretty(&all)?)?;
                eprintln!("report written to {}", path.display());
            }
            if !failed.is_empty() {
                anyhow::bail!("{} of {} contract(s) failed", failed.len(), contracts.len());
            }
        }
        Cmd::Smt { file } => smt::main(&file)?,
        Cmd::Bench {
            repo,
            contracts,
            suites,
            solvers,
            checks,
            loop_bound,
            solver_timeout,
            cap,
            bound_amounts,
            halmos,
            forge_bin,
            json,
        } => {
            let forge = forge::ForgeCli {
                bin: forge_bin.clone(),
                fuzz_seed: None,
                env: Vec::new(),
            };
            let mut targets: Vec<prove::BenchTarget> = contracts
                .into_iter()
                .map(prove::BenchTarget::Proof)
                .collect();
            for s in &suites {
                targets.push(prove::BenchTarget::suite(s)?);
            }
            let mut opts = prove::BenchOptions {
                halmos,
                forge_bin,
                solver_timeout,
                cap,
                price: true,
                bound_amounts,
                solvers,
                checks: String::new(),
                loop_bound,
            };
            let mut reports = Vec::new();
            for t in &targets {
                opts.checks = checks.clone().unwrap_or_else(|| match t {
                    prove::BenchTarget::Proof(_) => "check_exit".into(),
                    prove::BenchTarget::Suite { .. } => "test".into(),
                });
                let r = prove::bench(&repo, t, &forge, &opts)?;
                print_bench(&r);
                reports.push(r);
            }
            if let Some(path) = json.as_deref() {
                std::fs::write(path, serde_json::to_string_pretty(&reports)?)?;
                eprintln!("report written to {}", path.display());
            }
        }
        Cmd::Prove {
            repo,
            contracts,
            halmos,
            solver_timeout,
            no_price,
            bound_amounts,
            loop_bound,
            check_rewrite,
            check_every,
            check_seed,
            check_timeout,
            max_mutants,
            no_mutation,
            forge_bin,
            json,
        } => {
            let check = match check_rewrite.as_str() {
                "off" => smt::CheckMode::Off,
                "all" => smt::CheckMode::All,
                _ => smt::CheckMode::Sample {
                    every: check_every.max(1),
                    seed: check_seed,
                },
            };
            let forge = forge::ForgeCli {
                bin: forge_bin.clone(),
                fuzz_seed: None,
                env: Vec::new(),
            };
            let opts = prove::ProveOptions {
                halmos,
                forge_bin,
                solver_timeout,
                price: !no_price,
                bound_amounts,
                mutation: !no_mutation,
                max_mutants,
                loop_bound,
                check,
                check_timeout,
            };
            let mut reports = Vec::new();
            let mut failed = Vec::new();
            for c in &contracts {
                eprintln!("{}:", c.display());
                match prove::run(&repo, c, &forge, &opts) {
                    Ok(r) => {
                        print_proof_summary(&r);
                        reports.push(r);
                    }
                    Err(e) => {
                        println!("## {}: failed\n- {e:#}", c.display());
                        failed.push(serde_json::json!({
                            "contract": c.display().to_string(),
                            "error": format!("{e:#}"),
                        }));
                    }
                }
            }
            if let Some(path) = json.as_deref() {
                let all = serde_json::json!({ "reports": reports, "failed": failed });
                std::fs::write(path, serde_json::to_string_pretty(&all)?)?;
                eprintln!("report written to {}", path.display());
            }
            if !failed.is_empty() {
                anyhow::bail!("{} of {} contract(s) failed", failed.len(), contracts.len());
            }
        }
        Cmd::Score {
            repo,
            contract,
            test,
            check,
        } => {
            let (forge, opts) = check.setup(0);
            eprintln!("{}:", contract.display());
            let r = baseline::score_existing(&repo, &contract, &test, &forge, &opts)?;
            print_summary(&r);
            write_json(check.json.as_deref(), std::slice::from_ref(&r))?;
        }
    }
    Ok(())
}

/// Step 17's line: how many of the rewrite's answers were checked, and what
/// the checks found.
fn print_rewrite_check(c: &smt::RewriteCheck) {
    let mode = smt::CheckMode::from_env_value(&c.mode)
        .map(|m| m.describe())
        .unwrap_or_else(|| c.mode.clone());
    let unchecked = c.rewrite_unsat - c.checked;
    println!(
        "- rewrite check ({mode}): {} unsat answers came from the integer rewrite; {} checked against the original query: {} confirmed, {} inconclusive, {} contradicted; {} rest on the rewrite alone. {} sat models checked: {} invalid, {} inconclusive; {} left to Halmos's own refinement. {} answers came from a bit-vector solver directly",
        c.rewrite_unsat,
        c.checked,
        c.confirmed,
        c.inconclusive,
        c.contradicted,
        unchecked,
        c.models_checked,
        c.models_invalid,
        c.models_inconclusive,
        c.models_discarded,
        c.bit_vector,
    );
    if c.made_unknown > 0 {
        println!(
            "- {} answers became unknown: the checks could not confirm them, or found them wrong with nothing confirmed to replace them",
            c.made_unknown
        );
    }
    if c.disagreements() > 0 {
        println!(
            "- {} ANSWERS DISAGREED with the original query and were not passed on. Saved: {}",
            c.disagreements(),
            c.saved.join(", ")
        );
    }
}

fn print_proof_summary(r: &prove::ProveReport) {
    use prove::{ProofOutcome, Verdict, label};
    println!("## {} (prove)", r.contract);
    let mut holders = vec!["alice, bob, carol".to_string()];
    holders.extend(r.other_holders.iter().cloned());
    if r.exit.is_some() {
        holders.push("the vault (for requests)".to_string());
    }
    println!(
        "- invariant: {} hold every share and asset token; asset supply <= 2^96{}",
        holders.join(" + "),
        if r.price_at_least_one {
            "; share price >= 1"
        } else {
            ""
        }
    );
    if let Some(e) = &r.exit {
        let how = match e.progress {
            asyncproof::Progress::Owner => "the owner fulfils",
            asyncproof::Progress::Time => "a delay passes",
        };
        println!(
            "- exit: request, then {how}, then claim; {}",
            e.style.describe(e.progress)
        );
        if !e.learned.totals.is_empty() {
            let list: Vec<String> = e
                .learned
                .totals
                .iter()
                .map(|t| format!("{} = {}", t.label, t.counts.describe()))
                .collect();
            println!("- totals: {}", list.join("; "));
        }
        println!("- price: {}", e.learned.price.describe());
    }
    // What the checks are about: who calls, how the vault is deployed, what
    // the asset does.
    let callers = if r.exit.is_some() {
        "alice, bob, carol and the owner (the deploying contract)"
    } else {
        "alice, bob and carol"
    };
    println!(
        "- model: {callers} call every state-changing vault function with any arguments{}; the vault is deployed with a fresh plain ERC-20 asset, then its storage and the asset's are made symbolic; the asset moves only by transfer, approval and minting, up to 2^96 in all",
        if r.amounts_bounded {
            ", amounts up to 2^128"
        } else {
            ""
        }
    );
    if let Some(e) = &r.exit {
        println!(
            "- requests: read at id 0, one per controller; {}",
            match e.progress {
                asyncproof::Progress::Owner =>
                    "the owner fulfils them with fulfillRedeem(controller, shares)",
                asyncproof::Progress::Time => "they become claimable once a delay passes",
            }
        );
        println!(
            "- interference: the stable and fair checks protect bob from alice and the owner, assuming neither has an allowance or operator rights over bob's shares; the fair checks start from any state with the shares accounted for"
        );
    }
    let n = |v: Verdict| r.checks.iter().filter(|c| c.verdict == v).count();
    println!(
        "- checks: {} -> {} proved, {} counterexample, {} timeout, {} vacuous, {} incomplete, {} error -> {}",
        r.checks.len(),
        n(Verdict::Proved),
        n(Verdict::Counterexample),
        n(Verdict::Timeout),
        n(Verdict::Vacuous),
        n(Verdict::Incomplete),
        n(Verdict::Error),
        r.test_file
    );
    for c in &r.checks {
        let v = match c.verdict {
            Verdict::Proved => "proved".to_string(),
            Verdict::Counterexample => "COUNTEREXAMPLE".to_string(),
            Verdict::Timeout => "timeout".to_string(),
            Verdict::Vacuous => "vacuous (every path cut)".to_string(),
            Verdict::Incomplete => format!(
                "INCOMPLETE ({})",
                c.incomplete.as_deref().unwrap_or("not every path explored")
            ),
            Verdict::Error => "error".to_string(),
        };
        let mut line = format!(
            "  - {v}: {} ({:.1}s, {} paths)",
            label(&c.name),
            c.seconds,
            c.paths
        );
        if !c.counterexample.is_empty() {
            let vals: Vec<String> = c
                .counterexample
                .iter()
                .map(|(k, v)| format!("{k} = {v}"))
                .collect();
            line.push_str(&format!(": {}", vals.join(", ")));
        }
        if let Some(w) = &c.witness {
            line.push_str(&format!(" [from {w}]"));
        }
        println!("{line}");
    }
    let keeps: Vec<String> = r
        .checks
        .iter()
        .filter_map(|c| c.name.strip_prefix("check_keeps_"))
        .map(|f| match f.strip_prefix("asset_") {
            Some(a) => format!("asset.{a}"),
            None => f.to_string(),
        })
        .collect();
    println!("- keeps checks for: {}", keeps.join(", "));
    if let Some(c) = &r.rewrite_check {
        print_rewrite_check(c);
    }
    if !r.left_out.is_empty() {
        println!("- left out by the model: {}", r.left_out.join(", "));
    }
    for u in &r.unchecked {
        println!("- no keeps check: {}: {}", u.function, u.reason);
    }
    for q in &r.properties {
        let status = if q.proved {
            "proved".to_string()
        } else {
            match q.verdict {
                Some(Verdict::Proved) => {
                    "its check passed, but the induction behind it is not established".to_string()
                }
                Some(Verdict::Counterexample) => "counterexample".to_string(),
                Some(Verdict::Timeout) => "timeout".to_string(),
                Some(Verdict::Vacuous) => "vacuous".to_string(),
                Some(Verdict::Incomplete) => "incomplete".to_string(),
                Some(Verdict::Error) => "error".to_string(),
                None => "no result".to_string(),
            }
        };
        println!("- {}: {status}", q.property);
    }
    match &r.exit {
        None => {
            if r.full_exit_proved == Some(true) {
                println!(
                    "- full-exit verdict: proved: from every reachable state of the three-user world, every user who holds shares can redeem all of them in one call, and is paid at least what previewRedeem quoted"
                );
            } else {
                println!(
                    "- full-exit verdict: withheld: {}",
                    r.full_exit_withheld.join("; ")
                );
            }
            println!(
                "- not checked: whether payouts are fair; a payout is only compared with the vault's own previewRedeem quote"
            );
        }
        Some(e) => {
            let (fulfil, needs) = match e.progress {
                asyncproof::Progress::Owner => (
                    "the owner can make a whole pending request claimable",
                    "the owner to fulfil",
                ),
                asyncproof::Progress::Time => (
                    "a whole request is claimable once the delay is over",
                    "the delay to pass",
                ),
            };
            if r.liquidity_proved {
                println!(
                    "- stages: proved, each on its own, for every user from every state that satisfies the invariant: a user can request all their shares; {fulfil}; a user can claim everything claimable; and no call by alice or the owner shrinks bob's request or lowers the share price. That the stages compose into one exit is argued, not checked: it needs {needs}"
                );
            } else {
                println!("- stages: withheld: {}", r.withheld.join("; "));
            }
        }
    }
    if let Some(m) = &r.mutation {
        println!(
            "- mutants: {} -> {} caught by the proof, {} unknown (timeout), {} survived, {} invalid",
            m.mutants, m.caught, m.unknown, m.survived, m.invalid
        );
        println!("- kill rate: {}", pct(m.kill_rate));
        let mut by: Vec<(String, usize)> = Vec::new();
        for name in m.detail.iter().flat_map(|d| d.caught_by.iter()) {
            match by.iter_mut().find(|(n, _)| n == name) {
                Some((_, k)) => *k += 1,
                None => by.push((name.clone(), 1)),
            }
        }
        if !by.is_empty() {
            by.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
            let list: Vec<String> = by
                .iter()
                .map(|(n, k)| format!("{} {k}", label(n)))
                .collect();
            println!("- caught by check: {}", list.join(", "));
        }
        for d in &m.detail {
            let what = match d.outcome {
                ProofOutcome::Survived => "survived",
                ProofOutcome::Unknown => "unknown",
                ProofOutcome::Invalid => "invalid",
                ProofOutcome::Caught => continue,
            };
            println!("  - {what}: line {}: {}", d.line, d.change);
        }
    }
    println!("- time: {:.0}s", r.seconds);
}

fn print_bench(r: &prove::BenchReport) {
    use prove::label;
    println!(
        "## {} (bench: {} s per query, {} s per check)",
        r.contract, r.solver_timeout, r.cap
    );
    let Some(first) = r.rows.first() else {
        return;
    };
    let solvers: Vec<&str> = first.cells.iter().map(|c| c.solver.as_str()).collect();
    println!("| check | {} |", solvers.join(" | "));
    println!("|---|{}", "---|".repeat(solvers.len()));
    for row in &r.rows {
        let cells: Vec<String> = row.cells.iter().map(|c| c.text()).collect();
        println!("| {} | {} |", label(&row.check), cells.join(" | "));
    }
}

fn write_json(path: Option<&Path>, reports: &[Report]) -> Result<()> {
    if let Some(path) = path {
        std::fs::write(path, serde_json::to_string_pretty(reports)?)?;
        eprintln!("report written to {}", path.display());
    }
    Ok(())
}

fn pct(rate: Option<f64>) -> String {
    rate.map_or("n/a".into(), |k| format!("{:.0}%", k * 100.0))
}

fn print_mutation(m: &MutationScore) {
    println!(
        "- mutants: {} -> {} caught by an assertion, {} only by a revert, {} survived, {} invalid",
        m.mutants, m.caught_by_assertion, m.caught_by_revert_only, m.survived, m.invalid
    );
    println!(
        "- kill rate: {} by assertion, {} counting reverts",
        pct(m.assertion_kill_rate),
        pct(m.kill_rate)
    );
    // Which tests did the catching. A mutant counts once for each test that caught it.
    let mut by_test: Vec<(String, usize)> = Vec::new();
    for name in m.detail.iter().flat_map(|d| d.assertion_kills.iter()) {
        match by_test.iter_mut().find(|(n, _)| n == name) {
            Some((_, k)) => *k += 1,
            None => by_test.push((name.clone(), 1)),
        }
    }
    if !by_test.is_empty() {
        by_test.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        let list: Vec<String> = by_test.iter().map(|(n, k)| format!("{n} {k}")).collect();
        println!("- assertion kills by test: {}", list.join(", "));
    }
    for d in &m.detail {
        let label = match d.outcome {
            Outcome::Survived => "survived",
            Outcome::RevertOnly => "revert only",
            Outcome::Assertion | Outcome::Invalid => continue,
        };
        println!("  - {label}: line {}: {}", d.line, d.change);
    }
}

fn print_invariant_summary(r: &invariants::InvReport) {
    println!("## {} ({}, invariants)", r.contract, r.model);
    println!(
        "- harness: {} handler functions ({}){}",
        r.handler.len(),
        r.handler.join(", "),
        if r.skipped.is_empty() {
            String::new()
        } else {
            format!("; skipped: {}", r.skipped.join(", "))
        }
    );
    if !r.hints.is_empty() {
        println!("- hints: {} rules from the standard", r.hints.join(", "));
    }
    for n in &r.notes {
        println!("  - note: {n}");
    }
    let replaced = if r.replace_calls > 0 {
        format!(
            " + {} replacement(s) ({} extra call(s))",
            r.replacements, r.replace_calls
        )
    } else {
        String::new()
    };
    let rejected = if r.rejected.is_empty() {
        String::new()
    } else {
        format!(", {} rejected as never failing", r.rejected.len())
    };
    let refused = if r.repairs_refused > 0 {
        format!(", {} refused as never failing", r.repairs_refused)
    } else {
        String::new()
    };
    println!(
        "- invariants: {} proposed{replaced}{rejected}, {} compile ({} repair call(s){refused}), {} dropped -> {}",
        r.proposed,
        r.kept.len(),
        r.repairs,
        r.dropped.len(),
        r.test_file
    );
    for i in &r.kept {
        println!("  - {}: {}", i.id, i.statement);
    }
    for x in &r.rejected {
        println!("  - rejected {}: {} ({})", x.id, x.assert, x.reason);
    }
    for d in &r.dropped {
        println!("  - dropped {}: {}", d.id, d.error);
    }
    if !r.exit_checks.is_empty() {
        let status: Vec<String> = r
            .exit_checks
            .iter()
            .map(|c| {
                let state = if r.flagged.contains(c) {
                    "fails on clean code"
                } else if r.passed_on_clean.contains(c) {
                    "passes"
                } else {
                    "not run"
                };
                format!("{c} ({state})")
            })
            .collect();
        println!("- exit checks (ausweg): {}", status.join(", "));
    }
    if r.kept.is_empty() && r.exit_checks.is_empty() {
        return;
    }
    println!("- pass on clean code: {}", r.passed_on_clean.len());
    println!(
        "- flagged (fail on clean code): {} {:?}",
        r.flagged.len(),
        r.flagged
    );
    if let (Some(c), Some(v)) = (r.calls, r.reverts) {
        let share = if c > 0 {
            v as f64 / c as f64 * 100.0
        } else {
            0.0
        };
        let top: Vec<String> = r
            .top_reverts
            .iter()
            .map(|(s, v, c)| format!("{s} {v}/{c}"))
            .collect();
        println!(
            "- handler calls that reverted: {share:.0}% ({v} of {c}){}",
            if top.is_empty() {
                String::new()
            } else {
                format!("; most: {}", top.join(", "))
            }
        );
    }
    if let Some(m) = &r.mutation {
        print_mutation(m);
    }
}

fn print_summary(r: &Report) {
    match &r.model {
        Some(m) => println!("## {} ({m})", r.contract),
        None => println!("## {} (existing tests: {})", r.contract, r.test_file),
    }
    if r.model.is_some() {
        match r.compiled_after {
            None => {
                println!(
                    "- compiles: no (gave up; last attempt kept as {}.failed)",
                    r.test_file
                );
                return;
            }
            Some(n) => println!(
                "- compiles: yes, after {n} model call(s) -> {}",
                r.test_file
            ),
        }
    }
    println!("- pass on clean code: {}", r.passed_on_clean.len());
    println!(
        "- flagged (fail on clean code): {} {:?}",
        r.flagged.len(),
        r.flagged
    );
    if let Some(m) = &r.mutation {
        print_mutation(m);
    }
}
