# ausweg

Give `ausweg` an ERC-4626 or ERC-7540 vault, and it proves that every user can always get out, or reports a counterexample, or says which checks it could not decide. The specification is built in, so there is none to write per vault: `ausweg` writes the proof for [Halmos](https://github.com/a16z/halmos) from the vault's ABI and one concrete run of the vault.

The proof is about a model of the vault's world: three users and the owner, and a plain ERC-20 asset (no fees, blocklists or pauses) with a supply of at most 2^96. In it, from every reachable state, each user can redeem every share they hold in one call. In an ERC-7540 vault, each user can get out in three steps (request, fulfilment or a delay, claim) if the owner eventually fulfils requests, and no other user, nor the owner, can shrink a request or lower the share price on the way. Ownership changes and calls that need a signature are left out.

So far: a vault built on Solmate's ERC-4626, 14 of 14 checks proved; OpenZeppelin Community Contracts' ERC-7540 with admin-fulfilled redemptions, unchanged under a 30-line wrapper, 48 of 48.

## Try it on a vault

`examples/` has two vaults: `SolmateVault`, the smallest concrete vault on Solmate's ERC4626, and `SolmateVaultBug`, the same vault with one planted bug: `convertToAssets` rounds up, where Solmate rounds down. You need Rust, Foundry, Halmos and z3, and no model. In an empty folder:

```sh
git clone https://github.com/FatemehHeidari/ausweg
cargo install --path ausweg
forge init --empty ausweg-vault-demo && cd ausweg-vault-demo
forge install transmissions11/solmate@89365b880c4f3c786bdd453d4b8e8fe410344a69
cp ../ausweg/examples/SolmateVault.sol ../ausweg/examples/SolmateVaultBug.sol src/
ausweg prove --contract src/SolmateVault.sol --no-mutation
ausweg prove --contract src/SolmateVaultBug.sol --no-mutation
```

Each proof takes a few minutes; `--no-mutation` skips mutation scoring, which reruns the proof on every mutant. The first vault is proved:

```
- checks: 14 -> 14 proved, 0 counterexample, 0 timeout, 0 vacuous, 0 error -> test/generated/SolmateVault.proof.t.sol
- liquidity: proved: from every reachable state of the three-user world, every user can redeem every share they hold, and withdraw what maxWithdraw quotes
```

The second is not:

```
- checks: 14 -> 13 proved, 1 counterexample, 0 timeout, 0 vacuous, 0 error -> test/generated/SolmateVaultBug.proof.t.sol
  - COUNTEREXAMPLE: exit withdraw (2.3s, 33 paths): i = carol, totalAssets = 4, totalSupply = 3, userShares = 1
- liquidity: not proved (see the checks above)
```

In this run, carol holds 1 of 3 shares, and the vault holds 4 assets. `maxWithdraw` rounds 4/3 up and promises her 2 assets. Withdrawing 2 assets costs 2·3/4 = 1.5 shares, rounded up to 2, and she has 1, so her withdraw reverts.

What this does not prove: that what the vault pays is fair. In the bug vault, `redeem` still lets everyone out, so that check is proved, yet it pays carol 2 assets for a share worth 4/3, and alice and bob lose the difference. The ERC-4626 proof checks that every user can get out with what the vault promises, not that the promise is fair.

## Overview

It started as a property-test generator, and still is one: `ausweg` uses a local LLM to write Foundry property tests for Solidity contracts. It then checks the tests: they must compile, pass on the unchanged code, and fail when bugs are injected into the contract.

Two commands generate tests:

- `ausweg baseline` (milestone 1, design A): one prompt per contract, a compile-repair loop, and a mutation score. Its numbers are what later milestones are measured against.
- `ausweg invariants` (milestone 2, design C): `ausweg` writes the setup and a handler that drives the contract through random call sequences, including donations and yield that move the share price. The model writes only the invariant assertions, as JSON.

One command proves, with no model:

- `ausweg prove` (Step 13): for an ERC-4626 vault, a [Halmos](https://github.com/a16z/halmos) proof that every user can always get out: from every reachable state, each user can redeem every share they hold, in one call, and withdraw what `maxWithdraw` quotes. Halmos runs with ausweg's own solver back end (`ausweg smt`), which rewrites its bit-vector queries into integer arithmetic. The rewrite is exact except for a few operations with no simple integer form, such as a bitwise and of two unknown words: those become uninterpreted functions, so an `unsat` answer still holds, and a `sat` answer goes to a bit-vector solver on the original query.

`ausweg bench` (Step 14) compares `ausweg smt` with Halmos's own solvers on the same checks.

For an ERC-7540 vault, whose exits take three calls (request, fulfil or wait, claim), `ausweg prove` (Step 15) proves that every user can get out in those three steps, if the owner eventually fulfils requests or time passes, and that no other user, nor the owner, can shrink a user's request or lower the share price on the way.

Step 16 runs that proof on [OpenZeppelin's ERC-7540](https://docs.openzeppelin.com/community-contracts/erc7540), whose accounting depends on private running totals and a virtual-share price. The probe now reads both, `ausweg smt` reads Halmos's form of a checked subtraction, and the invariant counts a view that reverts after a call as broken.

## Requirements

- [Foundry](https://getfoundry.sh) (`forge` on `PATH`)
- [Ollama](https://ollama.com) with a coding model pulled, e.g. `ollama pull qwen2.5-coder:14b`
- Rust 1.85+ (edition 2024) to build
- For `ausweg prove` only: Halmos (`halmos` on `PATH`) and z3 (`z3` on `PATH`). `pipx install --include-deps halmos` puts both on `PATH`; so does `pip install halmos`, since Halmos depends on z3.

## Usage

Generate tests with the model, then score them:

```sh
cargo install --path .
cd my-foundry-project
ausweg baseline --contract src/Vault.sol --json ausweg-report.json
```

Generate invariants over a generated handler, then score them:

```sh
ausweg invariants --contract src/Vault.sol --json ausweg-inv.json
```

Score a test file you already have, without the model:

```sh
ausweg score --contract src/Vault.sol --test test/Vault.t.sol
```

Prove that every user can always get out of a vault:

```sh
ausweg prove --contract src/SolmateVault.sol --json ausweg-proof.json
```

Compare solvers on that proof:

```sh
ausweg bench --contract src/SolmateVault.sol --json ausweg-bench.json
```

Example output:

```
## src/Vault.sol (ollama:qwen2.5-coder:7b)
- compiles: yes, after 2 model call(s) -> test/generated/Vault.base.t.sol
- pass on clean code: 4
- flagged (fail on clean code): 1 ["testFuzz_withdrawAll"]
- mutants: 14 -> 6 caught by an assertion, 5 only by a revert, 1 survived, 2 invalid
- kill rate: 50% by assertion, 92% counting reverts
  - revert only: line 30: `+=` → `-=`
  - survived: line 41: `<=` → `<`
```

The numbers above illustrate the format only; they are not a measured result.

| Number | Meaning |
| --- | --- |
| compiles after N | Model calls until the file built (max `--max-tries`, default 3). A file that never builds is kept as `*.failed`. |
| pass on clean code | Tests that hold on the unchanged contract. |
| flagged | Tests that fail on the unchanged contract: a real bug or a wrong property. A person decides. |
| caught by an assertion | A clean-passing test failed an assertion or expectation: the property itself caught the bug. |
| only by a revert | The tests failed only because the mutated code reverted or panicked. A test with no assertions at all would have caught it too. |
| kill rate by assertion | Caught by an assertion, over mutants that compiled. The number that measures the properties. |
| kill rate counting reverts | All caught mutants, over mutants that compiled. An upper bound. |

Why two rates: in Solidity 0.8 most `+=`/`-=` swaps underflow or overflow, so the call reverts and every test that calls the function fails, whatever it checks. On the demo contract, a test with no assertions catches 5 of the 6 operator swaps.

The kind is read from forge's `[FAIL: <reason>]` line. Reasons starting with `assertion failed`, comparisons like `0 != 9533`, and failed `expectRevert` checks count as assertions; panics, revert strings and custom errors count as reverts. A fuzz test stops at its first failing input, so a mutant that both overflows on huge inputs and breaks an assertion on small ones may be counted as a revert. `assertTrue(x, "message")` failures read as reverts too. The assertion rate is therefore a lower bound.

Every `forge test` gets the same `--fuzz-seed` (default `1`) so runs are reproducible; pass `--fuzz-seed` to vary the inputs.

### `ausweg invariants` output

From a run on the ausweg-bench OZVault with a scripted stand-in for the model (`tools/fake_ollama.py`), so the invariants are hand-written:

```
## src/OZVault.sol (ollama:qwen2.5-coder:14b, invariants)
- harness: 9 handler functions (call_approve, call_deposit, call_mint, call_redeem, call_transfer, call_transferFrom, call_withdraw, donate_asset, yield_asset)
- invariants: 8 proposed, 8 compile (1 repair call(s)), 0 dropped -> test/generated/OZVault.inv.t.sol
  - solvency: The vault can always pay out every share it has issued
  - ...
- pass on clean code: 8
- flagged (fail on clean code): 0 []
- handler calls that reverted: 35% (718 of 2048); most: call_transferFrom 180/196, call_transfer 169/244, call_redeem 149/214
- mutants: 18 -> 3 caught by an assertion, 4 only by a revert, 11 survived, 0 invalid
- kill rate: 17% by assertion, 39% counting reverts
```

| Number | Meaning |
| --- | --- |
| harness | Handler functions the campaign calls: one per state-changing function, plus `donate_<token>` and `yield_<token>`. Functions it cannot call (such as `permit`, which needs a signature) are listed as skipped. |
| proposed, compile, dropped | Invariants in the model's plan; those that compile, after at most `--max-repairs` (default 3) repair calls each; those dropped with their compiler error. |
| rejected as never failing, replacements | Invariants refused before compiling because nothing the contract does can make them fail, such as `assertGe(target.totalAssets(), 0)` on a uint256; the invariants the model sent in their place. |
| handler calls that reverted | Share of handler calls that reverted on clean code. Reverts are allowed (`fail_on_revert = false`) but are wasted calls. |

Each invariant runs `--invariant-runs` (default 32) sequences of `--invariant-depth` (default 64) calls, on clean code and on every mutant. A broken handler or setup is reported as ausweg's failure, not the model's, and kept as `*.inv.t.sol.failed`.

### `ausweg prove` output

From a run on `examples/SolmateVault.sol`, mutation scoring left out (`--no-mutation`):

```
## src/SolmateVault.sol (prove)
- invariant: alice, bob, carol hold every share and asset token; asset supply <= 2^96; share price >= 1
- checks: 14 -> 14 proved, 0 counterexample, 0 timeout, 0 vacuous, 0 error -> test/generated/SolmateVault.proof.t.sol
  - proved: exit redeem (1.3s, 30 paths)
  - proved: exit withdraw (1.8s, 33 paths)
  - proved: init (0.1s, 1 paths)
  - proved: keeps deposit (16.9s, 446 paths)
  - ...
  - proved: keeps withdraw (49.0s, 1025 paths)
- liquidity: proved: from every reachable state of the three-user world, every user can redeem every share they hold, and withdraw what maxWithdraw quotes
- time: 169s
```

| Check | What it proves |
| --- | --- |
| `init` | A fresh deployment satisfies the invariant. |
| `keeps <f>` | From any state that satisfies the invariant, `<f>` keeps it, for any of the three users as caller and any arguments. One per state-changing function of the vault, plus the asset's `transfer`, `transferFrom`, `approve` and `mint` (yield or new funds, up to the supply cap). |
| `exit redeem` | From any state that satisfies the invariant, each user who holds shares redeems all of them in one call: no revert, at least what `previewRedeem` promised, and no shares left. |
| `exit withdraw` | Each user withdraws what `maxWithdraw` quotes, without a revert, burning at most what `previewWithdraw` says. |
| liquidity proved | Every check proved: by induction, every reachable state satisfies the invariant, and from each one every user can get out. |
| counterexample | A state, with its numbers named (`totalSupply`, `totalAssets`, `userShares`, the user), where the check fails. |
| timeout, vacuous | The solver ran out of `--solver-timeout` (default 60 s per query); or every path was cut by an assumption, so nothing was checked. |

Since 0.6.1, `exit redeem` takes the user's whole balance rather than what `maxRedeem` quotes, and a preview or max view that reverts fails the check: Halmos drops a path that reverts, so the state would otherwise go unchecked. `examples/HalfExitVault.sol` lets a user take out at most half their shares at a time, rounded down, so a last share is stuck. 0.6.0 proved it; 0.6.1 reports `COUNTEREXAMPLE: exit redeem: i = carol, totalAssets = 2, totalSupply = 2, userShares = 2`.

The invariant: alice, bob and carol, plus any address the constructor takes (a fee treasury), hold every share and every asset token, the vault holding its own assets; the asset's supply is at most 2^96; and the share price is at least 1, `totalAssets() >= totalSupply()`. `--no-price` leaves the last part out: on Solmate the exit check then fails, because a share worth less than one asset unit redeems to 0 and Solmate's `redeem` reverts with `ZERO_ASSETS`.

`--bound-amounts` limits every amount argument to 2^128. No balance can exceed the 2^96 supply cap, so larger amounts can only revert; leaving them out keeps the solver away from OpenZeppelin's and Solady's 512-bit `mulDiv` branch, where a product needs more than 256 bits. On the bench, OZVault's `keeps mint` times out without it and is proved with it.

A constructor address that is not the asset (OZFeeVault's treasury) gets a fixed address in the proof. Halmos models `makeAddr` as an unknown function, so with it the solver can make the treasury equal to a user, and the fee then lands in the user's own balance.

Mutation scoring reruns the whole proof on every mutant. A mutant is caught when a check that was proved on clean code has a counterexample; unknown when such a check times out instead. A mutant's run stops at its first counterexample, but a surviving mutant reruns every check, so scoring takes a while; `--max-mutants` limits it.

### ERC-7540 vaults

A vault with `requestRedeem`, `pendingRedeemRequest` and `claimableRedeemRequest` gets a different proof. Its exit takes three calls: bob requests, the owner fulfils (`fulfillRedeem`) or a delay passes, and bob claims with `redeem` or `withdraw`. A vault without `fulfillRedeem` is taken to be time-based.

| Check | What it proves |
| --- | --- |
| `request` | Bob can turn all his shares into a request, keeping the one he had. |
| `fulfil` or `mature` | The owner can make bob's whole request claimable; or, once the delay is over, it is claimable. |
| `claim redeem`, `claim withdraw` | Bob can claim everything claimable and is paid every claimable asset. |
| `stable <f>` | Called by alice or by the owner, `<f>` does not shrink bob's request, or, with a delay, push back what he can claim. |
| `fair <f>` | Called by alice or by the owner, `<f>` does not lower the share price. Checked from any state with the shares accounted for. |
| `init`, `keeps <f>` | The invariant, as in Step 13, plus the vault's accounting for requests; callers include the owner. |

All proved means: from every reachable state, every user can get out in three steps, if the owner eventually fulfils requests (or as time passes), and no other user, nor the owner, can shrink a request or lower the share price on the way. Alice stands for any other user: the users are interchangeable, so checking one of them covers the others. The owner is the test contract that deployed the vault; changes of owner (`transferOwnership`) and calls that need a signature (`permit`, `authorizeOperator`) are left out.

Vaults keep a request's shares and assets in different places. Before writing the invariant, ausweg runs one request through the vault in a forge test, `test/generated/<Name>.style.t.sol`: a deposit, a request of 400 of 1000 shares, then the fulfilment or ten years. Which of its tests pass tells ausweg whether the vault burns the shares, and sets the assets aside, at the request or at the fulfilment. The invariant then says the vault holds exactly the shares, and sets aside exactly the assets, of the requests it keeps. The report's `exit:` line says what the probe saw.

The probe also reads two things the views may not show (Step 16). First, the vault's running totals: every uint256 state variable named `total...`, private ones included, read from storage before the request, after it, after the fulfilment and after the claim (owner-fulfilled vaults only). Yield first moves the price off 1, so shares and assets differ. A total that reads 0, 400, 400, 0 sums the shares of pending and claimable requests; the invariant pins it to that sum over the users. A total that matches no request record, or more than one, stays out, with a note. Second, the price rule: after yield, the vault converts 10^24 assets to shares. That tells an exact price, totalAssets / totalSupply (Solmate), from one with a virtual share and asset, (totalAssets + 1) / (shares + 1) (OpenZeppelin and Solady with no decimals offset); the fair checks use the vault's rule. When requested shares are burned at the request but their assets stay in `totalAssets` until the fulfilment, as in OpenZeppelin's vault, the price counts the pending shares too. The report's `totals:` and `price:` lines say what the probe read.

Two rules for reading a check, in both proofs since 0.6.0. Halmos drops a path that reverts, so a call that left a view reverting (`totalAssets()` underflowing, say) would go unnoticed: the `keeps` checks read the invariant through an external call and count a revert as breaking it. And each check makes its call in a `try`, checking only a call that succeeds: a call that reverts changes nothing. A check is then vacuous only when its assumptions leave no state at all. On a vault with synchronous deposits, `requestDeposit` always reverts, and its checks prove.

From a run on ausweg-oz-bench, OpenZeppelin's ERC-7540 (Community Contracts' `ERC7540SyncDeposit` and `ERC7540AdminRedeem`, unchanged, under a wrapper that adds an owner and fulfils at the vault's own price), with `--bound-amounts --no-mutation`:

```
## src/OZAdminVault.sol (prove)
- invariant: alice, bob, carol + the vault (for requests) hold every share and asset token; asset supply <= 2^96; share price >= 1
- exit: request, then the owner fulfils, then claim; requested shares burned at the request; their assets set aside at the fulfilment
- totals: _totalPendingDepositAssets = stays 0; _totalPendingRedeemShares = shares of pending and claimable requests; _totalClaimableAssets = assets owed to claimable requests; _totalClaimableShares = shares of claimable requests
- price: (totalAssets + 1) / (shares + 1)
- checks: 48 -> 48 proved, 0 counterexample, 0 timeout, 0 vacuous, 0 error -> test/generated/OZAdminVault.proof.t.sol
  - proved: claim redeem (2.0s, 58 paths)
  - ...
  - proved: fair deposit (53.2s, 1205 paths)
  - ...
  - proved: keeps withdraw (173.9s, 2779 paths)
  - ...
- liquidity: proved: from every reachable state of the three-user world, every user can get out in three steps, if the owner fulfils requests eventually; no other user, and not the owner, can shrink a request or lower the share price
- time: 1376s
```

### `ausweg bench`

`ausweg bench` runs the same Halmos checks once per solver. Halmos builds the same queries each time; only the solver answering them changes.

```sh
ausweg bench --contract src/SolmateVault.sol
ausweg bench --suite test/SolmateVault.a16zb.t.sol:SolmateVaultA16zBounded --loop 4 --checks test_RT
```

`--contract` benchmarks a vault's liquidity proof: the two exit checks, or every check with `--checks check_`. `--suite <file>:<contract>` benchmarks Halmos tests already in the project, such as [a16z's ERC-4626 suite](https://github.com/a16z/erc4626-tests). `--solvers` (default `yices,bitwuzla,ausweg`) takes `ausweg` or any name `halmos --solver` accepts. `--solver-timeout` (default 60 s) applies to every query, for every solver; `--cap` (default 600 s) stops a check still running. Each cell reads `proved`, `counterexample`, `timeout` (a query ran out of time, so Halmos could not decide), `error` (Halmos logged a solver error, or stopped on something it does not support, such as a missing cheat code), or `unfinished` (stopped at the cap). Stopping a check also stops every solver it started, so one cell never slows down the next.

From a run on the ausweg-bench SolmateVault with `--cap 300`:

```
## src/SolmateVault.sol (bench: 60 s per query, 300 s per check)
| check | yices | bitwuzla | ausweg |
|---|---|---|---|
| exit redeem | timeout 150s | timeout 125s | proved 3s |
| exit withdraw | timeout 183s | timeout 183s | proved 4s |
```

## Try it on the demo contract

`examples/Bank.sol` is an 18-line bank with no imports. The mutator makes ten mutants of it: six operator swaps (the two `+=` in `deposit`, the `require` and its `>=` in `withdraw`, the two `-=`) and four deletions of a `+=`/`-=` line.

```sh
forge init ausweg-demo && cd ausweg-demo
cp ../ausweg/examples/Bank.sol src/
git add -A && git commit -m "add Bank"
ausweg baseline --contract src/Bank.sol --json report.json
git status
```

`git status` should list only `test/generated/` and `report.json` as new; `src/` is untouched. (The blocks here carry no `#` comments on purpose: zsh, the macOS default, passes them to the command as arguments when pasted.)

Large contracts: Ollama drops the start of a prompt longer than its context window, and the instructions sit at the start. Raise `--num-ctx` (default 8192 tokens) for big files.

## How it works

`ausweg baseline`:

1. Prompt the model with the contract and two example properties.
2. Write `test/generated/<Name>.base.t.sol` and run `forge build`. If it fails, send the errors back and retry.
3. Run `forge test --match-path` on the unchanged contract.
4. Mutate the contract one spot at a time, rerun the tests, then restore the original. While mutating, the original is also kept in `<Name>.sol.ausweg-backup`. If a run is killed, the next run restores the contract from it.

`ausweg invariants`:

1. Build the project and read the contract's ABI from `out/`.
2. Ask the model for a plan: a value for each constructor parameter and up to `--max-invariants` (default 8) invariants, each one assertion line. The prompt has the ABI and, up to `--max-source-chars` (default 30000), the source. For a contract with ERC-4626's conversion and preview functions, it also has the standard's rounding, fee and limit rules, paraphrased from [EIP-4626](https://eips.ethereum.org/EIPS/eip-4626); `--no-hints` leaves them out, as in 0.2.1.
3. Refuse invariants that can never fail and ask the model for others, in at most `--replace-rounds` (default 2) extra calls. A repair whose fix can never fail is refused too. `--allow-never-failing` turns this off, as in 0.2.0.
4. Write `test/generated/<Name>.inv.t.sol`: a mock token (`AuswegToken`), three funded users that assertions can name as `alice`, `bob` and `carol`, a handler, and one `invariant_<id>` function per assertion. The contract must be named after its file.
5. Build. An error inside an invariant goes back to the model for that invariant only; an invariant still failing after `--max-repairs` is dropped.
6. Run the invariants on clean code, then score them with the same mutants as `ausweg baseline`.

`ausweg prove`:

1. Build the project, read the ABI, and check that the contract has the ERC-4626 functions the proof calls.
2. Write `test/generated/<Name>.proof.t.sol`: the vault and a mock asset deployed with every storage slot symbolic (`svm.enableSymbolicStorage`), the invariant `_inv()`, and the `check_*` functions above.
3. Run `halmos --solver-command "ausweg smt"` with dynamic test linking off (Halmos cannot follow `vm.deployCode`).
4. Read Halmos's JSON results; then, unless `--no-mutation`, rerun on every mutant.

`ausweg smt <query.smt2>` is the solver Halmos calls. Bit-blasting solvers time out on a vault's 256-bit `mulDiv` arithmetic, even with small numbers. `ausweg smt` writes each n-bit value as an integer in [0, 2^n) and keeps each operation's modular meaning; where the bounds asserted in the query show a sum or product cannot wrap, it drops the `mod`. Halmos writes `a - b` as `a + (2^256 - 1) * b`; since 0.6.0 such a sum becomes a plain difference when the query shows it cannot wrap: solc's checked subtraction asserts `a - b <= a`, and a solvency check asserts that one sum is at most another. z3 solves the result, in three stages within the time limit: its general solver for 2 s, then its `qfnia` tactic for half of what is left, then the general solver again. Each stage answers queries the other stalls on; since 0.5.0 this settles queries that timed out before, such as the fee vault's `exit redeem`. Operations with no simple integer form, such as a bitwise and of two unknown words, become uninterpreted functions: an `unsat` answer still holds, and a `sat` answer goes to a bit-vector solver (yices or bitwuzla) for a real model. `AUSWEG_SMT_SOLVER` and `AUSWEG_SMT_FALLBACK` override the solvers; the integer query is kept next to Halmos's as `<n>.int.smt2`.

For an ERC-4626 vault, ausweg also writes two exit checks of its own, `invariant_ausweg_exit_redeem` and `invariant_ausweg_exit_withdraw`. From every state the fuzzer reaches, alice, bob and carol each redeem every share they hold, one after another, as in a bank run; in the second check, each withdraws what `maxWithdraw` quotes. A reverted exit, shares left after a full redeem, a payout below `previewRedeem`, more shares burned than `previewWithdraw`, or a transfer that differs from the reported amount fails the check. Each check runs in a snapshot that is rolled back, so the campaign continues from the state it reached. They need no model; `--no-exit-checks` leaves them out, as in 0.2.3.

The mutation summary names the tests that caught mutants by assertion, for example `- assertion kills by test: invariant_ausweg_exit_withdraw 3, invariant_ausweg_exit_redeem 3`.

"Can never fail" is read from the assertion's text: `x >= 0` or `0 <= x` with `x` unsigned, `x <= type(uint256).max`, the same expression on both sides, or a constant. An expression counts as unsigned unless it casts to a signed type, starts with a minus, or calls a target function that returns one. In the first run with qwen2.5-coder:14b, 17 of the 24 invariants it proposed were of this kind.

With dynamic test linking (on by default in forge 1.9), forge rewrites `new Contract(...)` in test files before compiling, so solc's byte offsets do not match the file on disk. `ausweg` locates errors by line and column instead.

Three kinds of mutant:

- Operator swaps: `+=`→`-=`, `>`→`>=`, `==`→`!=`, `require(` switched off, and so on.
- Statement deletions: a whole `+=`/`-=` line removed, such as `totalDeposits += amount;`. These never revert, so only an assertion that checks state catches them.
- Rounding flips: `mulDivDown`↔`mulDivUp`, `fullMulDiv`↔`fullMulDivUp`, `Rounding.Floor`↔`Rounding.Ceil`. Also non-reverting, and the usual way ERC-4626 vaults go wrong.

At most `--max-mutants` (default 100) are tried per contract, in source order.

The built-in mutator skips comments, strings, `pragma` and `import` lines, and never deletes a line containing braces. It is a stand-in until milestone 3 replaces it with SuMo or Gambit.

## Layout

| File | Role (Step 4 architecture) |
| --- | --- |
| `src/model.rs` | Model interface; `Ollama` is tier 1 |
| `src/forge.rs` | Foundry adapter; reads pass/fail and the failure reason |
| `src/mutate.rs` | Mutation adapter (built-in stand-in) |
| `src/prompt.rs` | Baseline and repair prompts |
| `src/baseline.rs` | The milestone-1 runner and the scorer |
| `src/abi.rs` | Reads the contract's ABI from forge's artifacts |
| `src/plan.rs` | Milestone-2 plan prompt and parser: constructor values and assertions |
| `src/scaffold.rs` | Writes the setup, the handler and the invariant functions |
| `src/invariants.rs` | The milestone-2 runner |
| `src/vacuous.rs` | Finds assertions that can never fail |
| `src/prove.rs` | Step 13: writes and runs the Halmos liquidity proof; Step 14: `ausweg bench` |
| `src/smt.rs` | Step 13: the integer solver back end for Halmos |
| `src/asyncproof.rs` | Step 15: the probe and the proof for ERC-7540 vaults; Step 16: running totals and the price rule |
| `tools/fake_ollama.py` | A stand-in for Ollama that returns hand-written plans, to test the harness with real forge |

`cargo test` runs the unit tests with a scripted model and a fake `forge`, so it needs neither installed.

To test the harness with real forge but no model, run the stand-in in one terminal and point `ausweg` at it from another:

```sh
python3 tools/fake_ollama.py 18440 /tmp/fake.log strong
```

```sh
ausweg invariants --contract src/OZVault.sol --ollama-url http://127.0.0.1:18440 --max-invariants 16
```

## License

Licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE) or the [MIT license](LICENSE-MIT), at your option.
