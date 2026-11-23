# ausweg

[![CI](https://github.com/FatemehHeidari/ausweg/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/FatemehHeidari/ausweg/actions/workflows/ci.yml)

`ausweg` writes Foundry property tests for Solidity contracts with a local LLM, and scores them against injected bugs. It also proves built-in exit properties of supported ERC-4626 and ERC-7540 vaults with [Halmos](https://github.com/a16z/halmos), using its own integer-arithmetic solver back end; the proofs involve no LLM. A proof holds for the model and assumptions stated below. Neither part takes a specification from you: the exit properties are built in, and the LLM writes its own tests.

For a supported ERC-4626 vault, `ausweg prove` proves that every user can always get out, or reports a counterexample, or withholds the verdict and says why; for an ERC-7540 vault, it proves each stage of the exit on its own. It writes the proof from the vault's ABI and one concrete run of the vault.

The proof is about a model of the vault's world: three users and the owner, and a plain ERC-20 asset (no fees, blocklists or pauses) with a supply of at most 2^96. In it, from every reachable state, each user can redeem every share they hold in one call, for at least what `previewRedeem` quoted; whether that quote is fair is not checked. In an ERC-7540 vault, each of the three steps (request, fulfilment or a delay, claim) is proved on its own, and so is that no other user, nor the owner, can shrink a request or lower the share price, unless the user gave them an allowance or operator rights. That the steps add up to one exit, if the owner eventually fulfils requests, is argued from them, not checked. Ownership changes and calls that need a signature are left out.

A vault is supported when the proof can deploy it and drive it in that world:

- It has the ERC-4626 functions the proof calls, and an ERC-7540 vault the request functions too. A vault missing one is refused, with the names.
- One constructor parameter takes the asset. Each other one gets a fixed value: 1 for a number, `false`, `"AUSWEG"`, or a fixed address with no code. The proof covers the vault deployed with those values; a parameter of another type is refused.
- It calls no contract but its asset. The proof deploys only the vault and a mock asset, so a strategy or an oracle would be an address with no code: such a vault is outside the model.
- An ERC-7540 vault keeps one request per controller, at id 0, made claimable by `fulfillRedeem(address controller, uint256 shares)` or by time. Refused: a vault that numbers its requests, fulfils them another way (a wrapper can add `fulfillRedeem`), takes a constructor address besides the asset, or sets assets aside at the request but needs the owner to fulfil it.

So far, with 0.7.0: a vault built on Solmate's ERC-4626, 15 of 15 checks proved, and with them the full-exit verdict; OpenZeppelin Community Contracts' ERC-7540 with admin-fulfilled redemptions, unchanged under a 30-line wrapper, 48 of 48, each step proved on its own.

## Try it on a vault

Start with two of the vaults in `examples/`: `SolmateVault`, the smallest concrete vault on Solmate's ERC4626, and `SolmateVaultBug`, the same vault with one planted bug: `convertToAssets` rounds up, where Solmate rounds down. You need Rust, Foundry, Halmos and z3, and no model. In an empty folder:

```sh
git clone https://github.com/FatemehHeidari/ausweg
cargo install --path ausweg
forge init --empty ausweg-vault-demo && cd ausweg-vault-demo
forge install transmissions11/solmate@89365b880c4f3c786bdd453d4b8e8fe410344a69
cp ../ausweg/examples/SolmateVault.sol ../ausweg/examples/SolmateVaultBug.sol src/
ausweg prove --contract src/SolmateVault.sol --no-mutation
ausweg prove --contract src/SolmateVaultBug.sol --no-mutation
```

Each proof takes a few minutes; `--no-mutation` skips mutation scoring, which reruns the proof on every mutant. For the first vault, each exit property is proved, and so is the full-exit verdict:

```
- checks: 15 -> 15 proved, 0 counterexample, 0 timeout, 0 vacuous, 0 incomplete, 0 error -> test/generated/SolmateVault.proof.t.sol
- full redemption (the whole balance, in one call): proved
- redemption at a positive maxRedeem quote: proved
- withdrawal at a positive maxWithdraw quote: proved
- full-exit verdict: proved: from every reachable state of the three-user world, every user who holds shares can redeem all of them in one call, and is paid at least what previewRedeem quoted
```

The second vault still lets every user redeem everything, so the full-exit verdict holds, but its `maxWithdraw` quote is wrong:

```
- checks: 15 -> 14 proved, 1 counterexample, 0 timeout, 0 vacuous, 0 incomplete, 0 error -> test/generated/SolmateVaultBug.proof.t.sol
  - COUNTEREXAMPLE: exit withdraw (3.4s, 33 paths): i = carol, totalAssets = 4, totalSupply = 3, userShares = 1 [from a state that satisfies the invariant; not shown reachable from deployment]
- full redemption (the whole balance, in one call): proved
- redemption at a positive maxRedeem quote: proved
- withdrawal at a positive maxWithdraw quote: counterexample
- full-exit verdict: proved: from every reachable state of the three-user world, every user who holds shares can redeem all of them in one call, and is paid at least what previewRedeem quoted
```

In this run, carol holds 1 of 3 shares, and the vault holds 4 assets. `maxWithdraw` rounds 4/3 up and promises her 2 assets. Withdrawing 2 assets costs 2·3/4 = 1.5 shares, rounded up to 2, and she has 1, so her withdraw reverts. The state is one the solver picked among those that satisfy the invariant; this one is reachable (deposit 3, then send the vault 1 asset), but ausweg does not show that.

What this does not prove: that what the vault pays is fair. A payout is only compared with the vault's own `previewRedeem` quote for the same shares, which ERC-4626 requires it to honor. In the bug vault, `redeem` lets everyone out, so full redemption is proved, yet it pays carol 2 assets for a share worth 4/3, and alice and bob lose the difference. A vault whose quotes were all 1 wei would pass the payout check just as well.

## Overview

It started as a property-test generator, and still is one: `ausweg` uses a local LLM to write Foundry property tests for Solidity contracts. It then checks the tests: they must compile, pass on the unchanged code, and fail when bugs are injected into the contract.

Two commands generate tests:

- `ausweg baseline` (milestone 1, design A): one prompt per contract, a compile-repair loop, and a mutation score. Its numbers are what later milestones are measured against.
- `ausweg invariants` (milestone 2, design C): `ausweg` writes the setup and a handler that drives the contract through random call sequences, including donations and yield that move the share price. The model writes only the invariant assertions, as JSON.

One command proves, with no model:

- `ausweg prove` (Step 13): for an ERC-4626 vault, a [Halmos](https://github.com/a16z/halmos) proof that every user can always get out: from every reachable state, each user can redeem every share they hold, in one call. Redeeming what `maxRedeem` quotes and withdrawing what `maxWithdraw` quotes are checked too, each reported on its own. Halmos runs with ausweg's own solver back end (`ausweg smt`), which rewrites its bit-vector queries into integer arithmetic. The rewrite is meant to preserve `unsat`: if the integer query is unsatisfiable, so is Halmos's, with its arithmetic refined as Halmos refines it. That direction is argued from the code (Step 20), not mechanically proved, and the converse is not claimed: a `sat` answer is a candidate, whose model is checked against Halmos's query before Halmos gets it, unless the checks are off. A few operations with no simple integer form, such as a bitwise and of two unknown words, become uninterpreted functions: an `unsat` answer still holds, and a `sat` answer goes to a bit-vector solver on the original query.

`ausweg bench` (Step 14) compares `ausweg smt` with Halmos's own solvers on the same checks.

For an ERC-7540 vault, whose exits take three calls (request, fulfil or wait, claim), `ausweg prove` (Step 15) proves each step on its own, and that no other user, nor the owner, can shrink a user's request or lower the share price. That the steps add up to one exit, if the owner eventually fulfils requests or time passes, is argued from them, not checked.

Step 16 runs that proof on [OpenZeppelin's ERC-7540](https://docs.openzeppelin.com/community-contracts/erc7540), whose accounting depends on private running totals and a virtual-share price. The probe now reads both, `ausweg smt` reads Halmos's form of a checked subtraction, and the invariant counts a view that reverts after a call as broken.

## Requirements

- [Foundry](https://getfoundry.sh) (`forge` on `PATH`)
- For `ausweg baseline` and `ausweg invariants` only: [Ollama](https://ollama.com) with a coding model pulled, e.g. `ollama pull qwen2.5-coder:14b`
- Rust 1.88+ (edition 2024) to build: the code uses let chains, stable since 1.88
- For `ausweg prove` only: Halmos (`halmos` on `PATH`) and z3 (`z3` on `PATH`). `pipx install --include-deps halmos` puts both on `PATH`; so does `pip install halmos`, since Halmos depends on z3.

## Development checks

GitHub Actions checks formatting and Clippy, and runs the Rust tests on Rust
1.88.0 and current stable, with default features and with `--all-features`
(including fault injection). Every Cargo build uses the committed lockfile.
The test jobs install Halmos 0.3.3, z3 4.12.6 and yices 2.6.4; missing yices
or a skipped comparison with Halmos's real model parser fails CI.

The suite uses stand-ins for Foundry and the LLM, and real solvers for the SMT
regressions. Full vault proofs and benchmarks are separate from these checks.

To run the same checks locally, with the solver tools installed:

```sh
cargo +1.88.0 fmt --all -- --check
cargo +1.88.0 clippy --locked --all-targets -- -D warnings
cargo +1.88.0 clippy --locked --all-targets --all-features -- -D warnings
CI=true cargo test --locked --all-targets -- --test-threads=1
CI=true cargo test --locked --all-targets --all-features -- --test-threads=1
```

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

Check the built-in exit properties of a supported vault:

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

The kind is read from forge's `[FAIL: <reason>]` line. Reasons starting with `assertion failed`, comparisons like `0 != 9533`, and failed `expectRevert` checks count as assertions; panics, revert strings and custom errors count as reverts. A fuzz test stops at its first failing input, so a mutant that both overflows on huge inputs and breaks an assertion on small ones may be counted as a revert. Since 0.6.6 a reason that is one of the test file's own assertion messages, such as `supply mismatch` from `assertTrue(x, "supply mismatch")`, counts as an assertion too, unless the contract uses the same string (a revert reason would then read the same). The assertion rate is still a lower bound.

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

From a 0.7.0 run on `examples/SolmateVault.sol`, mutation scoring left out (`--no-mutation`):

```
## src/SolmateVault.sol (prove)
- invariant: alice, bob, carol hold every share and asset token; asset supply <= 2^96; share price >= 1
- model: alice, bob and carol call every state-changing vault function with any arguments; the vault is deployed with a fresh plain ERC-20 asset, then its storage and the asset's are made symbolic; the asset moves only by transfer, approval and minting, up to 2^96 in all
- checks: 15 -> 15 proved, 0 counterexample, 0 timeout, 0 vacuous, 0 incomplete, 0 error -> test/generated/SolmateVault.proof.t.sol
  - proved: exit max_redeem (1.6s, 30 paths)
  - proved: exit redeem (1.7s, 30 paths)
  - proved: exit withdraw (2.5s, 33 paths)
  - proved: init (0.1s, 1 paths)
  - proved: keeps deposit (64.6s, 452 paths)
  - ...
  - proved: keeps withdraw (70.9s, 1031 paths)
- keeps checks for: approve, asset.approve, asset.mint, asset.transfer, asset.transferFrom, deposit, mint, redeem, transfer, transferFrom, withdraw
- left out by the model: permit (needs a signature)
- full redemption (the whole balance, in one call): proved
- redemption at a positive maxRedeem quote: proved
- withdrawal at a positive maxWithdraw quote: proved
- full-exit verdict: proved: from every reachable state of the three-user world, every user who holds shares can redeem all of them in one call, and is paid at least what previewRedeem quoted
- not checked: whether payouts are fair; a payout is only compared with the vault's own previewRedeem quote
- time: 288s
```

| Check | What it proves |
| --- | --- |
| `init` | A fresh deployment satisfies the invariant. |
| `keeps <f>` | From any state that satisfies the invariant, `<f>` keeps it, for any of the three users as caller and any arguments. One per state-changing function of the vault, plus the asset's `transfer`, `transferFrom`, `approve` and `mint` (yield or new funds, up to the supply cap). |
| `exit redeem` | Full redemption. From any state that satisfies the invariant, each user who holds shares redeems all of them in one call: no revert, a payout of at least what `previewRedeem` quoted for that balance, and no shares left. A balance whose quote rounds to 0 is still in scope: it must redeem and clear. A user with no shares has nothing to redeem and is skipped. |
| `exit max_redeem` | Redemption at the advertised limit. When `maxRedeem` quotes a positive amount, redeeming exactly that succeeds, pays at least `previewRedeem`, and burns exactly those shares. A quote of 0 promises nothing and is skipped. |
| `exit withdraw` | Withdrawal at the advertised limit. When `maxWithdraw` quotes a positive amount, withdrawing it succeeds, burns at most what `previewWithdraw` says, and transfers exactly that amount. |
| left out by the model | A state-changing function the model excludes on purpose, with why: `permit` needs a signature. |
| no keeps check | A state-changing entry point the proof cannot call: one with an argument it cannot fill in (an array, a struct, `bytes`, a `string`), a payable function (its check sends no ether), or a fallback or receive function. Any one of them withholds the verdict. |
| full-exit verdict | `init`, every `keeps` check and `exit redeem` proved, every obligation with a result, and every state-changing entry point with its keeps check: by induction, every reachable state satisfies the invariant, and from each one every user can redeem their whole balance in one call. The two advertised-limit checks are reported on their own lines and are not part of it. Otherwise the line says `withheld` and lists why. |
| counterexample | A state, with its numbers named (`totalSupply`, `totalAssets`, `userShares`, the user), where the check fails. Only `init`'s starts at deployment; every other one is a state the solver picked among those that satisfy the invariant, and the line says it is not shown reachable from deployment. |
| timeout, vacuous | The solver ran out of `--solver-timeout` (default 60 s per query); or every path was cut by an assumption, so nothing was checked. |
| incomplete | Halmos passed the check without exploring every path: its loop bound (`--loop`, 2 by default) cut some paths short, or its result did not say how many it cut. Not a proof; `ausweg prove --loop N` raises the bound. |
| rewrite check | Since 0.8.0: how many of the integer rewrite's `unsat` answers were checked against the original query (one in 16 by default), and how many of those were confirmed, inconclusive or contradicted; how many `sat` models were checked, and how many were invalid or inconclusive. A contradicted answer or an invalid model never reaches Halmos: it gets a bit-vector solver's answer once that model checks out, or `unknown`, and the case is saved. A model the checks cannot confirm becomes `unknown` whenever the checks are on, and so does an unconfirmed `unsat` with `--check-rewrite all`; a line counts those. |

Since 0.6.1, `exit redeem` takes the user's whole balance rather than what `maxRedeem` quotes, and a preview or max view that reverts fails the check: Halmos drops a path that reverts, so the state would otherwise go unchecked. `examples/HalfExitVault.sol` lets a user take out at most half their shares at a time, rounded down, so a last share is stuck. 0.6.0 proved it; 0.6.1 reports `COUNTEREXAMPLE: exit redeem: i = carol, totalAssets = 2, totalSupply = 2, userShares = 2`.

Since 0.6.2, a state-changing function with no keeps check withholds the verdict, since the induction then misses a transition. `examples/SweepVault.sol` lets anyone send all of the vault's assets away with `sweep(address[])`, which the proof cannot call. 0.6.0 proved it; 0.6.2 reports `no keeps check: sweep(address[]): takes address[], which the proof cannot fill in` and `liquidity: not proved`; 0.7.0, `full-exit verdict: withheld: sweep(address[]): no keeps check`.

Since 0.7.0, the three exit properties are reported on their own, and the full-exit verdict rests on full redemption: `init`, every keeps check, every entry point covered, and `exit redeem`. ERC-4626 lets a vault cap what one call takes, if `maxRedeem` and `maxWithdraw` say so. `examples/CapRedeemVault.sol` takes at most 100 shares per call. It honors what it advertises, so both limit checks are proved, but full redemption is not: `COUNTEREXAMPLE: exit redeem: i = carol, totalAssets = 129, totalSupply = 128, userShares = 128`. Carol holds all 128 shares and the vault 129 assets. `maxWithdraw` quotes `convertToAssets(100)` = ⌊100·129/128⌋ = 100 assets, and withdrawing them burns ⌈100·128/129⌉ = 100 shares, within the cap. `redeem(128)` asks for more than `maxRedeem` = 100 and reverts. She can get out in two calls, 100 shares and then 28, but the verdict is about one call, so it is withheld.

In the JSON report, `full_exit_proved` carries the full-exit verdict, with `full_exit_withheld` saying why not. `liquidity_proved` means every check proved, as in 0.6 (an incomplete one counts as not proved), with `withheld` saying why not. So for SolmateVaultBug, `liquidity_proved` is false and `full_exit_proved` is true. 0.7.0 had made `liquidity_proved` the full-exit verdict, true for SolmateVaultBug; since 0.7.1 it has its 0.6 meaning again, so a gate built on it is as strict as before. `properties` has each exit property on its own. An ERC-7540 report has no `full_exit_proved`: its verdict is `liquidity_proved`.

Since 0.7.0, a check that Halmos passes without exploring every path is incomplete, and withholds the verdict. Halmos stops following a loop after `--loop` iterations (2 by default) and still prints `[PASS]`, with exit code 0; it warns, and its JSON result counts the cut paths in `num_bounded_loops`. `examples/LoopVault.sol` adds a `ping(n)` whose loop runs up to 3 times. 0.6.0 proved it; 0.7.0 reports `INCOMPLETE (Halmos's loop bound cut 3 paths short; rerun with a higher --loop): keeps ping`, and with `--loop 4` the check is proved. A result with no `num_bounded_loops`, or one that is not a count, is incomplete too. `ausweg bench` prints `incomplete`, and mutation scoring counts an incomplete check as unknown, like a timeout.

The invariant: alice, bob and carol, plus any address the constructor takes (a fee treasury), hold every share and every asset token, the vault holding its own assets; the asset's supply is at most 2^96; and the share price is at least 1, `totalAssets() >= totalSupply()`. `--no-price` leaves the last part out: on Solmate the exit check then fails, because a share worth less than one asset unit redeems to 0 and Solmate's `redeem` reverts with `ZERO_ASSETS`.

`--bound-amounts` limits every unsigned integer argument to 2^128, amounts and others alike. No balance can exceed the 2^96 supply cap, so larger amounts can only revert, except in `approve`; there the bound narrows only `keeps approve`, since storage is symbolic and every other check starts from any allowance. Leaving them out keeps the solver away from OpenZeppelin's and Solady's 512-bit `mulDiv` branch, where a product needs more than 256 bits. On the bench, OZVault's `keeps mint` times out without it and is proved with it.

A constructor address that is not the asset (OZFeeVault's treasury) gets a fixed address in the proof. Halmos models `makeAddr` as an unknown function, so with it the solver can make the treasury equal to a user, and the fee then lands in the user's own balance.

Mutation scoring reruns the whole proof on every mutant. A mutant is caught when a check that was proved on clean code has a counterexample; unknown when such a check times out instead. A mutant's run stops at its first counterexample, but a surviving mutant reruns every check, so scoring takes a while; `--max-mutants` limits it.

### ERC-7540 vaults

A vault with `requestRedeem`, `pendingRedeemRequest` and `claimableRedeemRequest` gets a different proof. Its exit takes three calls: bob requests, the owner fulfils (`fulfillRedeem`) or a delay passes, and bob claims with `redeem` or `withdraw`. A vault without `fulfillRedeem` is taken to be time-based.

| Check | What it proves |
| --- | --- |
| `request` | Each user can turn all their shares into a request, keeping the one they had. |
| `fulfil` or `mature` | The owner can make a user's whole request claimable; or, once the delay is over, it is claimable. |
| `claim redeem`, `claim withdraw` | Each user can claim everything claimable and is paid every claimable asset. |
| `stable <f>` | Called by alice or by the owner, `<f>` does not shrink bob's request, or, with a delay, push back what he can claim. |
| `fair <f>` | Called by alice or by the owner, `<f>` does not lower the share price. Checked from any state with the shares accounted for. |
| `init`, `keeps <f>` | The invariant, as in Step 13, plus the vault's accounting for requests; callers include the owner. |

All proved means: by induction, every reachable state satisfies the invariant, and from each one every user can request all their shares; the owner can make a whole request claimable (or, with a delay, it becomes claimable once the delay is over); every user can claim everything claimable; and no call by another user or the owner shrinks a request or lowers the share price. Each step is checked on its own. That they add up to one exit, if the owner fulfils or the delay passes, is argued from them, not checked; since 0.7.0 the report's `stages:` line says so, and its `requests:` and `interference:` lines state the request scope and the no-delegation assumption below. The verdict also needs every obligation with a result, no check incomplete, and every state-changing entry point checked, as for ERC-4626. Requests are read at id 0, one per controller, as in ERC-7540's controller-only requests, and fulfilled with `fulfillRedeem(address controller, uint256 shares)`. Since 0.6.6 a vault that gives its requests other ids, or fulfils them with another function, is refused with a message saying so; before, it failed the probe as if its requests never became claimable. Since 0.6.5 the three exit steps are checked for each of alice, bob and carol. The stable and fair checks still protect bob against alice and the owner: that covers every pair of users because they are interchangeable, which holds unless the vault's code singles out an address, since all of its storage is symbolic. They also assume no delegation: the other caller has no allowance or operator rights over bob's shares, because a user who delegates lets the delegate act for them. The owner is the test contract that deployed the vault; changes of owner (`transferOwnership`) and calls that need a signature (`permit`, `authorizeOperator`) are left out.

Vaults keep a request's shares and assets in different places. Before writing the invariant, ausweg runs one request through the vault in a forge test, `test/generated/<Name>.style.t.sol`: a deposit, a request of 400 of 1000 shares, then the fulfilment or ten years. Which of its tests pass tells ausweg whether the vault burns the shares, and sets the assets aside, at the request or at the fulfilment. The invariant then says the vault holds exactly the shares, and sets aside exactly the assets, of the requests it keeps. The report's `exit:` line says what the probe saw.

The probe also reads two things the views may not show (Step 16). First, the vault's running totals: every uint256 state variable named `total...`, private ones included, read from storage before the request, after it, after the fulfilment and after the claim (owner-fulfilled vaults only). Yield first moves the price off 1, so shares and assets differ. A total that reads 0, 400, 400, 0 sums the shares of pending and claimable requests; the invariant pins it to that sum over the users. A total that matches no request record, or more than one, stays out, with a note. So, since 0.6.6, does a total that stays 0 through the walk but whose name is not about requests (pending, claimable, request, queue), such as a `totalFees` the walk never touches: pinned to 0, it would fail a keeps check as soon as a call raised it. A deposit-side total of a vault with synchronous deposits, such as `_totalPendingDepositAssets`, is still pinned to 0. Second, the price rule: after yield, the vault converts 10^24 assets to shares. That tells an exact price, totalAssets / totalSupply (Solmate), from one with a virtual share and asset, (totalAssets + 1) / (shares + 1) (OpenZeppelin and Solady with no decimals offset); the fair checks use the vault's rule. When requested shares are burned at the request but their assets stay in `totalAssets` until the fulfilment, as in OpenZeppelin's vault, the price counts the pending shares too. The report's `totals:` and `price:` lines say what the probe read.

Two rules for reading a check, in both proofs since 0.6.0. Halmos drops a path that reverts, so a call that left a view reverting (`totalAssets()` underflowing, say) would go unnoticed: the `keeps` checks read the invariant through an external call and count a revert as breaking it. And each check makes its call in a `try`, checking only a call that succeeds: a call that reverts changes nothing. A check is then vacuous only when its assumptions leave no state at all. On a vault with synchronous deposits, `requestDeposit` always reverts, and its checks prove.

From a 0.7.0 run on ausweg-oz-bench, OpenZeppelin's ERC-7540 (Community Contracts' `ERC7540SyncDeposit` and `ERC7540AdminRedeem`, unchanged, under a wrapper that adds an owner and fulfils at the vault's own price), with `--bound-amounts --no-mutation`:

```
## src/OZAdminVault.sol (prove)
- invariant: alice, bob, carol + the vault (for requests) hold every share and asset token; asset supply <= 2^96; share price >= 1
- exit: request, then the owner fulfils, then claim; requested shares burned at the request; their assets set aside at the fulfilment
- totals: _totalPendingDepositAssets = stays 0; _totalPendingRedeemShares = shares of pending and claimable requests; _totalClaimableAssets = assets owed to claimable requests; _totalClaimableShares = shares of claimable requests
- price: (totalAssets + 1) / (shares + 1)
- model: alice, bob, carol and the owner (the deploying contract) call every state-changing vault function with any arguments, amounts up to 2^128; the vault is deployed with a fresh plain ERC-20 asset, then its storage and the asset's are made symbolic; the asset moves only by transfer, approval and minting, up to 2^96 in all
- requests: read at id 0, one per controller; the owner fulfils them with fulfillRedeem(controller, shares)
- interference: the stable and fair checks protect bob from alice and the owner, assuming neither has an allowance or operator rights over bob's shares; the fair checks start from any state with the shares accounted for
- checks: 48 -> 48 proved, 0 counterexample, 0 timeout, 0 vacuous, 0 incomplete, 0 error -> test/generated/OZAdminVault.proof.t.sol
  - proved: claim redeem (6.9s, 174 paths)
  - ...
  - proved: fair deposit (78.6s, 1204 paths)
  - ...
  - proved: keeps withdraw (1883.1s, 2779 paths)
  - ...
- keeps checks for: approve, asset.approve, asset.mint, asset.transfer, asset.transferFrom, deposit, deposit_2, fulfillRedeem, mint, mint_2, redeem, requestDeposit, requestRedeem, setOperator, transfer, transferFrom, withdraw
- left out by the model: renounceOwnership (changes the owner), transferOwnership (changes the owner)
- stages: proved, each on its own, for every user from every state that satisfies the invariant: a user can request all their shares; the owner can make a whole pending request claimable; a user can claim everything claimable; and no call by alice or the owner shrinks bob's request or lowers the share price. That the stages compose into one exit is argued, not checked: it needs the owner to fulfil
- time: 4059s
```

That run shared two cores with other proofs. Its `keeps withdraw` explored the same 2779 paths as under 0.6.0, and took 259 s when run alone.

### `ausweg bench`

`ausweg bench` runs the same Halmos checks once per solver. Halmos builds the same queries each time; only the solver answering them changes.

```sh
ausweg bench --contract src/SolmateVault.sol
ausweg bench --suite test/SolmateVault.a16zb.t.sol:SolmateVaultA16zBounded --loop 4 --checks test_RT
```

`--contract` benchmarks a vault's liquidity proof: the exit checks (three since 0.7.0), or every check with `--checks check_`. `--suite <file>:<contract>` benchmarks Halmos tests already in the project, such as [a16z's ERC-4626 suite](https://github.com/a16z/erc4626-tests). `--solvers` (default `yices,bitwuzla,ausweg`) takes `ausweg` or any name `halmos --solver` accepts. `--solver-timeout` (default 60 s) applies to every query, for every solver; `--cap` (default 600 s) stops a check still running. Each cell reads `proved`, `counterexample`, `timeout` (a query ran out of time, so Halmos could not decide), `incomplete` (passed with paths cut at the loop bound), `error` (Halmos logged a solver error, or stopped on something it does not support, such as a missing cheat code), or `unfinished` (stopped at the cap). Stopping a check also stops every solver it started, so one cell never slows down the next.

From a run on the ausweg-bench SolmateVault with `--cap 300`, before 0.7.0 added `exit max_redeem`:

```
## src/SolmateVault.sol (bench: 60 s per query, 300 s per check)
| check | yices | bitwuzla | ausweg |
|---|---|---|---|
| exit redeem | timeout 150s | timeout 125s | proved 3s |
| exit withdraw | timeout 183s | timeout 183s | proved 4s |
```

Turning bit-vector queries into integer arithmetic is not new. It is int-blasting ([Zohar et al., VMCAI 2022](https://link.springer.com/chapter/10.1007/978-3-030-94583-1_24)), implemented in cvc5 and already evaluated on smart-contract verification conditions; adding the modulo operations only where a result depends on them has been studied too ([Barth, Heizmann and Hoenicke, 2026](https://link.springer.com/article/10.1007/s00236-026-00529-y)). Halmos ships cvc5's version as the `cvc5-int` solver: cvc5 1.2.1 with `--solve-bv-as-int=iand --iand-mode=bitwise`. `ausweg smt` is an integer-arithmetic backend specialized for Halmos's queries: its checked arithmetic, and the `mulDiv` arithmetic of vaults. Two preliminary comparisons follow, both from 0.8.0 on SolmateVault, on a 2-core machine.

End to end, through Halmos (`ausweg bench`, 60 s per query, 300 s per check). The last column is a second run with z3 hidden from `ausweg smt`, so its integer solver was cvc5:

| check | cvc5-int | ausweg, with z3 | ausweg, with cvc5 |
|---|---|---|---|
| exit redeem | unfinished at 300 s | proved 4 s | proved 10 s |
| exit max_redeem | unfinished at 300 s | proved 4 s | proved 3 s |
| exit withdraw | unfinished at 300 s | proved 4 s | proved 4 s |

A rerun of the last column took 6 s, 3 s and 4 s, and ausweg's log showed all 39 queries answered `unsat` by cvc5 on ausweg's translation, none by the bit-vector fallback. A check's time covers Halmos's exploration, ausweg's translation, process start-up and file I/O, as well as solving.

The solver step alone: the 39 queries of the three exit checks were saved from one run, each as Halmos's bit-vector query and ausweg's integer translation of it, and each translation was run three times per solver, with a 60 s limit:

| solver, on ausweg's 39 translations | answers | time |
|---|---|---|
| cvc5 1.2.1 | 39 `unsat` | 1.37 s (runs: 1.43, 1.43, 1.43 s) |
| z3, plain `check-sat` | 39 `unsat` | 1.36 s (runs: 1.28, 1.45, 1.34 s) |
| z3 with ausweg's tactic schedule | 39 `unsat` | 1.19 s (runs: 1.11, 1.24, 1.25 s) |

The time is the sum of the 39 per-query medians over the three runs; each run's own sum is in parentheses. All 39 captured queries returned `unsat` under cvc5, plain z3 and staged z3, in about 1.2 to 1.4 s in all: neither a particular arithmetic engine nor z3's staged tactics was necessary to solve this query set quickly. Staged z3 was faster than plain z3 in each of the three runs, by 0.09 to 0.21 s over all 39 queries.

Both comparisons cover one vault. `cvc5-int` was measured only through Halmos; replaying it on the saved bit-vector queries, with the same EVM refinement Halmos applies, would isolate the translation's effect further. More vaults, cvc5's other int-blasting modes, and which of ausweg's rewrites make the difference are still to be measured.

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
4. Mutate the contract one spot at a time and rerun the tests. Since 0.6.4 the mutants go to a copy of the project in the system temp directory, with `lib/` linked rather than copied, so your contract is never edited: a run stopped with Ctrl-C leaves its copy in the temp directory, not a mutant in `src/`. Before, ausweg wrote each mutant over the contract and kept the original in `<Name>.sol.ausweg-backup`. If it finds such a backup, it puts the original back only when the file on disk is the original or one of its mutants; if you have edited the file since, it stops and leaves both for you to compare.

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

`ausweg smt <query.smt2>` is the solver Halmos calls. Bit-blasting solvers time out on a vault's 256-bit `mulDiv` arithmetic, even with small numbers. `ausweg smt` writes each n-bit value as an integer in [0, 2^n) and keeps each operation's modular meaning; where the bounds asserted in the query show a sum or product cannot wrap, it drops the `mod`. Halmos writes `a - b` as `a + (2^256 - 1) * b`; since 0.6.0 such a sum becomes a plain difference when the query shows it cannot wrap: solc's checked subtraction asserts `a - b <= a`, and a solvency check asserts that one sum is at most another. z3 solves the result, in three stages within the time limit: its general solver for 2 s, then its `qfnia` tactic for half of what is left, then the general solver again. Each stage answers queries the other stalls on; since 0.5.0 this settles queries that timed out before, such as the fee vault's `exit redeem`. Operations with no simple integer form, such as a bitwise and of two unknown words, become uninterpreted functions: an `unsat` answer still holds, and a `sat` answer goes to a bit-vector solver (yices or bitwuzla) for a real model; with neither installed, the answer is `unknown`, which Halmos does not count as a pass. Since 0.7.0 yices runs with `--smt2-model-format --bvconst-in-decimal`, as when Halmos calls it itself. Without them yices prints its model as `(= p_a #b…)`, which Halmos does not read, so a counterexample found this way came back with no values. Since 0.6.3, a query with assertion scopes (`push`, `pop`) or more than one `check-sat` is not translated: it goes to the bit-vector solver unchanged, yices in incremental mode. Before, ausweg read past `push` and `pop`, kept the popped assertion, and could answer `unsat` for a satisfiable query, which would count as a proof. None of the Halmos queries saved during development has either. Since 0.8.1 (Step 20), a query with a constant array whose value is not zero also goes to the bit-vector solver unchanged, and a macro (a `define-fun` with parameters) reads its arguments where it is called but every other name in its body by its global meaning, even where a `let` at the call site binds the same name. Before, each could make ausweg answer `unsat` for a satisfiable query. Halmos 0.3.3 writes neither, and the 39 SolmateVault queries saved for the solver comparison above translate exactly as before. `AUSWEG_SMT_SOLVER` and `AUSWEG_SMT_FALLBACK` override the solvers; the integer query is kept next to Halmos's as `<n>.int.smt2`.

Since 0.8.0 (Step 17), `ausweg smt` checks its answers against Halmos's original query, because the rewrite's soundness is a claim about ausweg's own code. Every `sat` model is read by Halmos's own rule, names in `|quotes|` included (a test compares the reader with Halmos 0.3.3's parser), and its values are plugged into the query as Halmos refines it; a value for a variable the query does not declare makes the model wrong. If the values do not satisfy the query, a bit-vector solver answers instead and its model is checked the same way; if that one is wrong too, Halmos gets `unknown`. Halmos gets only a model that checks out: one the check cannot settle in time becomes `unknown` as well. That holds whenever the checks are on, sampled or not, since every model is checked; `--check-rewrite off` passes every answer on unchecked. A model that mentions `f_evm_` is passed on unchecked as well: Halmos discards such a model and refines the query itself.

A sample of the rewrite's `unsat` answers goes to yices (else bitwuzla, else z3): one in 16 by default, picked by a hash of the query and a seed (`--check-every`, `--check-seed`); Halmos's random per-run symbol ids are left out of the hash, so the same seed checks the same queries on every run. yices gets Halmos's query as written first, where multiplications and divisions of unknown words are uninterpreted `f_evm_` functions; if that is not `unsat`, it gets the query refined the way Halmos refines it, which is the query the rewrite answered. If yices finds a model, and the model checks out, Halmos gets it: a real counterexample the rewrite missed. The checks of one answer share `--check-timeout` (10 s by default) and never run past the query's own time: once it is spent no check starts, and a running checker is stopped, with every process it started, whatever its own time limit. A wrong answer's replacement may use the rest of the query's time. A check that runs out is inconclusive. When sampling, an inconclusive `unsat` stands, like the answers the sample skips; `--check-rewrite all` checks every `unsat`, and turns one the checks cannot confirm into `unknown`. `--check-rewrite off` skips the checks. Every disagreement is saved under `test/generated/rewrite-checks/<hash>/`: the original and translated queries, the rejected answer, each check's query and the checker's answer to it, any replacement and its check, and `about.json`, with every solver run's actual command, budget and time, whether ausweg stopped each check, the versions, the settings and what Halmos got. The report's `rewrite check:` line, and `rewrite_check` in the JSON, count what was checked and what the checks found. The verdict fields keep their meaning: an answer that disagreed never reaches Halmos. Unchecked `unsat` answers still rest on the rewrite, and the line says how many there were. The checks cost time: on SolmateVaultBug, the default took the proof from 146 s to 259 s in one session (earlier runs: 139 s to 189 s and 234 s), most of it in checks that ran out of `--check-timeout`; runs differ because Halmos explores slightly differently each time, and the sample changes with it. `ausweg bench` runs `ausweg smt` with the checks off, so its times compare with other solvers'.

Example: `assert(x + y >= x)` in an `unchecked` block fails only when the sum wraps. A rewrite that dropped the wraparound would answer `unsat`, and Halmos would pass the check. Built with `--features fault-injection`, ausweg plants exactly that bug when `AUSWEG_SMT_INJECT=wraparound`: with the checks off, Halmos prints `[PASS]`; with `--check-rewrite all`, yices finds a model and Halmos prints `[FAIL]` with it. `bad-model` and `bad-fallback-model` plant wrong models instead. Unchecked, Halmos reported `x = 0` as a counterexample to `assert(x + 1 != 0)`, which it is not; checked, it reports `x = 2^256 - 1`, or a timeout when the replacement model is wrong as well or cannot be confirmed.

For an ERC-4626 vault, ausweg also writes two exit checks of its own, `invariant_ausweg_exit_redeem` and `invariant_ausweg_exit_withdraw`. From every state the fuzzer reaches, alice, bob and carol each redeem every share they hold, one after another, as in a bank run; in the second check, each withdraws what `maxWithdraw` quotes. A reverted exit, shares left after a full redeem, a payout below `previewRedeem`, more shares burned than `previewWithdraw`, or a transfer that differs from the reported amount fails the check. Each check runs in a snapshot that is rolled back, so the campaign continues from the state it reached. They need no model; `--no-exit-checks` leaves them out, as in 0.2.3.

The mutation summary names the tests that caught mutants by assertion, for example `- assertion kills by test: invariant_ausweg_exit_withdraw 3, invariant_ausweg_exit_redeem 3`.

"Can never fail" is read from the assertion's text: `x >= 0` or `0 <= x` with `x` unsigned, `x <= type(uint256).max`, the same expression on both sides, or a constant. An expression counts as unsigned unless it casts to a signed type, starts with a minus, or calls a target function that returns one. In the first run with qwen2.5-coder:14b, 17 of the 24 invariants it proposed were of this kind.

With dynamic test linking (on by default in forge 1.9), forge rewrites `new Contract(...)` in test files before compiling, so solc's byte offsets do not match the file on disk. `ausweg` locates errors by line and column instead.

Three kinds of mutant:

- Operator swaps: `+=`→`-=`, `>`→`>=`, `==`→`!=`, `require(` switched off, and so on.
- Statement deletions: a whole `+=`/`-=` line removed, such as `totalDeposits += amount;`. They insert no revert, so they can expose accounting errors that only an assertion on state catches. They can still cause one later: without `totalDeposits += amount;`, a later `totalDeposits -= amount;` underflows.
- Rounding flips: `mulDivDown`↔`mulDivUp`, `fullMulDiv`↔`fullMulDivUp`, `Rounding.Floor`↔`Rounding.Ceil`, the usual way ERC-4626 vaults go wrong. They insert no revert either, but a changed result can make a later call revert: in `SolmateVaultBug`, `convertToAssets` rounded up makes a withdrawal at the `maxWithdraw` quote revert.

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
