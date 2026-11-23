#!/usr/bin/env -S python3 -I
"""Stands in for `halmos` when the runner calls `ausweg prove --halmos <this>`.

ausweg runs Halmos once for every check of its proof contract. This script
runs Halmos once per check instead, with the same arguments, so that each
check gets its own time limit: the smaller of the per-check cap and what is
left of the target's budget. A check stopped at that limit is recorded as
unfinished, and everything it started is stopped with it. The results are
merged into the one JSON file ausweg asked for, so ausweg reads them as it
would read Halmos's own.

Set by the runner: EVAL_REAL_HALMOS, EVAL_CHECK_CAP (seconds),
EVAL_TARGET_DEADLINE (Unix time), EVAL_CHECK_RECORD (JSON lines),
EVAL_LOG_DIR. EVAL_ONLY_CHECKS (comma-separated names) runs a subset, for the
runner's own tests.
"""

import json
import os
import re
import subprocess
import sys
import threading
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import files  # noqa: E402
import proc  # noqa: E402

# A check stopped at its limit: ausweg reads any exit code it does not know
# as an error, so the check is not counted as proved.
UNFINISHED = 124


def arg_value(args, flag):
    if flag in args:
        i = args.index(flag)
        if i + 1 < len(args):
            return args[i + 1]
    return None


def proof_checks(root, contract):
    """The check functions of `contract`, in source order, and the file."""
    gen = os.path.join(root, "test", "generated")
    for dirpath, _, fnames in os.walk(gen):
        for f in sorted(fnames):
            if not f.endswith(".sol"):
                continue
            path = os.path.join(dirpath, f)
            src = files.read_text(path)
            m = re.search(r"\bcontract\s+" + re.escape(contract) + r"\b", src)
            if not m:
                continue
            body = src[m.start():]
            names = re.findall(r"\bfunction\s+(check_\w+)\s*\(", body)
            return path, list(dict.fromkeys(names))
    return None, []


def pump(stream, sinks):
    for line in iter(stream.readline, b""):
        for s in sinks:
            s.write(line)
            s.flush()


def main():
    args = sys.argv[1:]
    real = os.environ["EVAL_REAL_HALMOS"]
    cap = float(os.environ.get("EVAL_CHECK_CAP", "600"))
    target_deadline = float(os.environ.get("EVAL_TARGET_DEADLINE", str(time.time() + 10**9)))
    record = os.environ.get("EVAL_CHECK_RECORD")
    log_dir = os.environ.get("EVAL_LOG_DIR", ".")
    only = [c for c in os.environ.get("EVAL_ONLY_CHECKS", "").split(",") if c]
    os.makedirs(log_dir, exist_ok=True)
    proc.become_subreaper()

    root = arg_value(args, "--root") or "."
    contract = arg_value(args, "--contract")
    json_out = arg_value(args, "--json-output")
    # A mutant run stops at its first counterexample, as ausweg's own do.
    early_exit = "--early-exit" in args or os.environ.get("EVAL_EARLY_EXIT") == "1"
    path, checks = proof_checks(root, contract)
    if only:
        checks = [c for c in checks if c in only]
    if os.environ.get("EVAL_CHECK_ORDER") == "exits-first":
        # Only the time to the first counterexample changes, not any result.
        checks = ([c for c in checks if c.startswith("check_exit_")]
                  + [c for c in checks if not c.startswith("check_exit_")])
    if not checks:
        # Nothing to split: run Halmos as ausweg asked.
        os.execv(real, [real] + args)

    base = list(args)
    i = base.index("--json-output")
    del base[i:i + 2]
    key = None
    entries = []
    for name in checks:
        jk = os.path.join(log_dir, f"{contract}.{name}.json")
        if os.path.exists(jk):
            os.remove(jk)
        cmd = [real] + base + ["--match-test", f"^{name}\\(", "--json-output", jk]
        limit = min(cap, target_deadline - time.time())
        started = time.time()
        rec = {"check": name, "cmd": cmd, "start": started, "limit_seconds": round(max(limit, 0), 3)}
        if limit <= 0:
            rec.update(outcome="not started: the target's budget was spent", seconds=0)
            entries.append({"name": f"{name}()", "exitcode": UNFINISHED, "num_models": 0, "models": [],
                            "num_paths": [0, 0, 0], "time": [0, 0, 0], "num_bounded_loops": None})
            if record:
                with open(record, "a") as f:
                    f.write(json.dumps(rec) + "\n")
            continue
        out_log = open(os.path.join(log_dir, f"{contract}.{name}.stdout"), "wb")
        err_log = open(os.path.join(log_dir, f"{contract}.{name}.stderr"), "wb")
        p = subprocess.Popen(cmd, cwd=os.getcwd(), stdout=subprocess.PIPE, stderr=err_log,
                             stdin=subprocess.DEVNULL)
        t = threading.Thread(target=pump, args=(p.stdout, [out_log, sys.stdout.buffer]), daemon=True)
        t.start()
        stopped = False
        try:
            p.wait(timeout=limit)
        except subprocess.TimeoutExpired:
            stopped = True
            p.kill()
            p.wait()
        left = proc.stop_descendants(os.getpid())
        if stopped:
            left = ["halmos"] + left
        t.join(timeout=5)
        out_log.close()
        err_log.close()
        seconds = round(time.time() - started, 3)
        rec.update(seconds=seconds, returncode=p.returncode, left_running_and_stopped=left,
                   still_running_after_stop=[n for _, n in proc.descendants(os.getpid())])
        if stopped:
            rec["outcome"] = "unfinished: stopped at its limit"
            entries.append({"name": f"{name}()", "exitcode": UNFINISHED, "num_models": 0, "models": [],
                            "num_paths": [0, 0, 0], "time": [seconds, 0, 0], "num_bounded_loops": None})
        else:
            try:
                data = files.read_json(jk)
            except (OSError, ValueError):
                data = None
            results = (data or {}).get("test_results") or {}
            mine = [(k, v) for k, v in results.items() if k.endswith(":" + contract)]
            if not mine:
                rec["outcome"] = "Halmos wrote no result"
                if record:
                    with open(record, "a") as f:
                        f.write(json.dumps(rec) + "\n")
                # A build error or the like: ausweg reports it as Halmos's.
                sys.exit(p.returncode or 1)
            mine.sort(key=lambda kv: "test/generated/" not in kv[0])
            key = key or mine[0][0]
            got = [e for e in mine[0][1] if e.get("name", "").split("(")[0] == name]
            entries.extend(got)
            rec["outcome"] = "completed"
            rec["halmos_exitcodes"] = [e.get("exitcode") for e in got]
        if record:
            with open(record, "a") as f:
                f.write(json.dumps(rec) + "\n")
        if early_exit and any(e.get("exitcode") == 1 for e in entries):
            break

    if key is None:
        rel = os.path.relpath(path, root) if path else "test/generated/unknown.t.sol"
        key = f"{rel}:{contract}"
    codes = [e.get("exitcode", 0) for e in entries]
    merged = {"exitcode": max(codes) if codes else 0, "test_results": {key: entries}}
    with open(json_out, "w") as f:
        json.dump(merged, f)
    sys.exit(0 if all(c == 0 for c in codes) else 1)


if __name__ == "__main__":
    main()
