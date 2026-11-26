"""Replay from deployment: confirm an exit failure with a concrete call sequence.

The search runs forge's invariant fuzzer on a handler that drives the vault
from a fresh deployment, with the three exit properties as invariants
(templates/Erc4626Replay.sol). It is written apart from ausweg's proof. A
failure it finds is persisted by forge as a call sequence; the runner turns
that sequence into a plain forge test, which replays the same calls from
deployment and then checks the same property. A counterexample counts as
confirmed only when such a replay fails on the target. A mutant counts as
killed only when the same replay passes on the original and fails on the
mutant.
"""

import json
import os
import re
import shutil
import time

import files
import proc

HERE = os.path.dirname(os.path.abspath(__file__))
REPLAY_DIR = "test/eval-replay"
SEARCH_CONTRACT = "AuswegEvalSearch"
# ausweg's exit checks and the search's invariants, property by property.
PROPERTIES = {
    "check_exit_redeem": ("invariant_exit_redeem", "exitRedeem"),
    "check_exit_max_redeem": ("invariant_exit_max_redeem", "exitMaxRedeem"),
    "check_exit_withdraw": ("invariant_exit_withdraw", "exitWithdraw"),
}
# ausweg's ERC-7540 exit checks: the steps of an exit, and that no one else
# shrinks a request or lowers the share price. They have no replay yet.
ERC7540_EXITS = ("check_request", "check_fulfil", "check_mature", "check_claim_redeem", "check_claim_withdraw")
ERC7540_OTHERS = ("check_stable_", "check_fair_")
NO_ERC7540_REPLAY = "No ERC-7540 replay implemented; counterexample remains unconfirmed."


def erc7540_exit(check):
    return check in ERC7540_EXITS or check.startswith(ERC7540_OTHERS)


def ctor_args(abi):
    """The constructor arguments of the replay's deployment, by ausweg's rule
    for its proof: the asset parameter gets the token; another number gets 1,
    a bool false, a string "AUSWEG", another address a fixed address with no
    code. Returns (expression, None) or (None, why not)."""
    ctor = next((x for x in abi if x.get("type") == "constructor"), {"inputs": []})
    args, tokens, k = [], 0, 0
    for i, p in enumerate(ctor["inputs"]):
        ty, name = p["type"], p.get("name", "").lower()
        internal = p.get("internalType", "")
        if ty == "address":
            contract_type = internal[len("contract "):] if internal.startswith("contract ") else None
            tokenish = any(w in name for w in ("asset", "token", "underlying"))
            if tokenish or (i == 0 and contract_type):
                tokens += 1
                args.append(f"{contract_type}(address(token))" if contract_type else "address(token)")
            else:
                addr = f"address(uint160(0x7EA50 + {k}))"
                k += 1
                args.append(f"{contract_type}({addr})" if contract_type else addr)
        elif ty.startswith("uint") or ty.startswith("int"):
            args.append("1")
        elif ty == "bool":
            args.append("false")
        elif ty == "string":
            args.append('"AUSWEG"')
        else:
            return None, f"constructor parameter {p.get('name')} ({ty}) has no default"
    if tokens != 1:
        return None, f"{tokens} constructor parameters take the asset; the replay needs one"
    return ", ".join(args), None


def install(project, target_path, contract, abi):
    """Write the search into the project. Returns None, or why it cannot."""
    args, why = ctor_args(abi)
    if why:
        return why
    d = os.path.join(project, REPLAY_DIR)
    os.makedirs(d, exist_ok=True)
    shutil.copy(os.path.join(HERE, "templates", "ReplayToken.sol"), d)
    src = files.read_text(os.path.join(HERE, "templates", "Erc4626Replay.sol"))
    src = src.replace("{{IMPORT}}", target_path).replace("{{TARGET}}", contract).replace("{{CTOR_ARGS}}", args)
    with open(os.path.join(d, f"{SEARCH_CONTRACT}.t.sol"), "w") as f:
        f.write(src)
    return None


def _forge_env(env, settings):
    e = dict(env)
    e["FOUNDRY_INVARIANT_RUNS"] = str(settings["campaign_runs"])
    e["FOUNDRY_INVARIANT_DEPTH"] = str(settings["campaign_depth"])
    e["FOUNDRY_INVARIANT_WORKERS"] = "1"
    e["FOUNDRY_INVARIANT_FAIL_ON_REVERT"] = "false"
    e["FOUNDRY_DYNAMIC_TEST_LINKING"] = "false"
    return e


def _results(stdout_path):
    """forge test --json: {test name: (status, reason)}, with each invariant
    under its own name."""
    text = files.read_text(stdout_path, errors="replace")
    start = text.find("{")
    out = {}
    if start < 0:
        return out
    try:
        data = json.loads(text[start:])
    except ValueError:
        return out
    for suite in data.values():
        for name, r in (suite.get("test_results") or {}).items():
            preds = r.get("invariant_predicate_results")
            if preds:
                # forge 1.9 runs a contract's invariants as one test, named
                # after the first, and gives each invariant's outcome here.
                why = {x.get("name"): x.get("reason") for x in r.get("invariant_failures") or []}
                for p in preds:
                    out[p["name"]] = (p.get("status"), p.get("reason") or why.get(p["name"]))
                continue
            reason = r.get("reason")
            if not reason:
                # An invariant test keeps its reason with each broken invariant.
                fails = r.get("invariant_failures") or []
                reason = next((x.get("reason") for x in fails if x.get("reason")), None)
            out[name.split("(")[0]] = (r.get("status"), reason)
    return out


def search(project, checks, deadline, settings, forge, env, logdir, record, seed0, first=False):
    """Look for a failure of each exit property behind `checks` until each is
    found or the monotonic `deadline` passes; with `first`, only until a
    campaign finds one. Each campaign has its own seed: seed0, seed0 + 1, ...
    Returns (failures, campaigns): failures maps a check to {invariant,
    reason, seed, sequence}."""
    wanted = {PROPERTIES[c][0]: c for c in checks if c in PROPERTIES}
    found, campaigns = {}, []
    seed = seed0
    while wanted and time.monotonic() < deadline:
        persist = os.path.join(project, "cache", "invariant")
        shutil.rmtree(persist, ignore_errors=True)
        # forge matches a test by its signature, such as invariant_exit_redeem().
        pattern = "^(" + "|".join(sorted(wanted)) + ")\\("
        tag = f"search-seed{seed}"
        r = proc.run([forge, "test", "--match-contract", f"^{SEARCH_CONTRACT}$", "--match-test", pattern,
                      "--fuzz-seed", str(seed), "--json"],
                     project, _forge_env(env, settings), deadline,
                     os.path.join(logdir, f"{tag}.stdout"), os.path.join(logdir, f"{tag}.stderr"),
                     record=record, label=f"replay search, seed {seed}")
        res = _results(r["stdout"])
        campaigns.append({"seed": seed, "seconds": r["seconds"], "status": r["status"],
                          "results": {k: v[0] for k, v in res.items()}})
        if r["status"] == "exited" and not res:
            # forge ran no test: a build error or a pattern that matched nothing.
            campaigns[-1]["error"] = "forge ran no test; see its output"
            break
        for inv, check in list(wanted.items()):
            status, reason = res.get(inv, (None, None))
            if status != "Failure":
                continue
            f = os.path.join(persist, "failures", SEARCH_CONTRACT, "invariants", inv)
            try:
                seq = files.read_json(f)["call_sequence"]
            except (OSError, ValueError, KeyError):
                continue
            keep = os.path.join(logdir, f"{inv}.seed{seed}.sequence.json")
            shutil.copy(f, keep)
            found[check] = {"invariant": inv, "reason": reason, "seed": seed, "sequence": seq,
                            "saved": keep}
            del wanted[inv]
        if r["status"] != "exited" or (first and found):
            break
        seed += 1
    return found, campaigns


def write_trace(project, check, failure, name):
    """A plain forge test that makes the failure's calls from deployment, then
    checks the same exit property."""
    lines = []
    for step in failure["sequence"]:
        if step.get("warp"):
            lines.append(f"        vm.warp(block.timestamp + {int(step['warp'], 0) if isinstance(step['warp'], str) else step['warp']});")
        if step.get("roll"):
            lines.append(f"        vm.roll(block.number + {int(step['roll'], 0) if isinstance(step['roll'], str) else step['roll']});")
        calldata = step["calldata"][2:] if step["calldata"].startswith("0x") else step["calldata"]
        lines.append(f"        // {step.get('signature', '')} [{step.get('raw_args', '')}]")
        lines.append(f"        vm.prank({_checksum_free(step['sender'])});")
        lines.append(f"        (ok,) = address(handler).call(hex\"{calldata}\");")
        lines.append("        require(ok, \"a replayed call reverted\");")
    body = "\n".join(lines)
    check_fn = PROPERTIES[check][1]
    src = f"""// SPDX-License-Identifier: MIT
pragma solidity >=0.8.0;

// Written by the ausweg evaluation runner: the call sequence of a failure
// found with fuzz seed {failure['seed']}, replayed from deployment.
import {{AuswegEvalExits}} from "./{SEARCH_CONTRACT}.t.sol";

contract {name} is AuswegEvalExits {{
    function test_trace() public {{
        bool ok;
{body}
        {check_fn}();
    }}
}}
"""
    path = os.path.join(project, REPLAY_DIR, f"{name}.t.sol")
    with open(path, "w") as f:
        f.write(src)
    return path


def _checksum_free(addr):
    """An address solc accepts whatever its checksum: a 40-digit hex literal
    must be checksummed, so the address goes in as a decimal number."""
    return f"address(uint160({int(addr, 16)}))"


def run_trace(project, trace_path, name, forge, env, deadline, logdir, record, label):
    """Replay a trace. Returns {"failed": bool, "reason": ..., "status": ...}."""
    d = os.path.join(project, REPLAY_DIR)
    os.makedirs(d, exist_ok=True)
    dest = os.path.join(d, os.path.basename(trace_path))
    if os.path.abspath(dest) != os.path.abspath(trace_path):
        shutil.copy(trace_path, dest)
    tag = f"{name}.{label.replace(' ', '-')}"
    r = proc.run([forge, "test", "--match-contract", f"^{name}$", "--json"], project,
                 _forge_env(env, {"campaign_runs": 1, "campaign_depth": 1}), deadline,
                 os.path.join(logdir, f"{tag}.stdout"), os.path.join(logdir, f"{tag}.stderr"),
                 record=record, label=f"replay {name} on {label}")
    res = _results(r["stdout"])
    status, reason = res.get("test_trace", (None, None))
    if status is None:
        reason = "the replay did not run: see its output"
    exit_reason = bool(reason and re.match(r"exit (redeem|max_redeem|withdraw):", reason))
    return {"status": status, "reason": reason, "run": r["status"],
            "exit_failed": status == "Failure" and exit_reason,
            "passed": status == "Success"}
