#!/usr/bin/env -S python3 -I
"""Read a smoke run's results against what each smoke target must show.

    python3 -I eval/smoke_check.py --targets eval/smoke.toml --out <run dir>

Prints one line per requirement, and exits 1 if any fails.
"""

import argparse
import json
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import files  # noqa: E402

SOLVERS = ("ausweg", "z3", "yices-smt2", "halmos", "python3", "forge")


def through_link(project, rel):
    """Whether the path `rel` inside `project` passes through a symbolic link."""
    parts = rel.split("/")
    return any(os.path.islink(os.path.join(project, *parts[:i])) for i in range(1, len(parts) + 1))


def check_run(r, name):
    """The wrapper's record of check `name` in a target's result, or None."""
    recs = [c for c in (r.get("prove") or {}).get("wrapper_checks") or [] if c.get("check") == name]
    return recs[0] if recs else None


def described(r, name):
    rec = check_run(r, name) or {}
    paths = rec.get("num_paths")
    return (f"{(r.get('checks') or {}).get(name)}, {rec.get('seconds')} s, "
            f"{paths[0] if paths else 'no'} paths")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--targets", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    targets = files.read_toml(a.targets)["target"]
    lines, ok_all = [], True

    def check(tid, what, ok, evidence):
        nonlocal ok_all
        ok_all &= bool(ok)
        lines.append((tid, what, "pass" if ok else "FAIL", evidence))

    for t in targets:
        path = os.path.join(a.out, t["id"], "result.json")
        if not os.path.exists(path):
            check(t["id"], "ran", False, "no result.json")
            continue
        r = files.read_json(path)
        e = t.get("expect", {})
        if "class" in e:
            check(t["id"], f"target class is {e['class']}", r["class"] == e["class"], r["class"])
        for c, want in e.get("checks", {}).items():
            got = (r.get("checks") or {}).get(c)
            check(t["id"], f"{c} is {want}", got == want, got)
        for c in e.get("confirmed", []):
            rp = (r.get("replays") or {}).get(c, {})
            ev = (f"replay {rp.get('trace', '?').split('/')[-1]}: {rp.get('on_target', {}).get('reason')}; "
                  f"search seed {rp.get('search', {}).get('seed')}, {rp.get('search', {}).get('calls')} calls")
            check(t["id"], f"{c} confirmed by replay from deployment", rp.get("confirmed"), ev)
        if e.get("confirmed_kill"):
            mut = r.get("mutation") or {}
            kills = [m for m in mut.get("mutants", []) if m.get("class") == "killed, confirmed"]
            if kills:
                m = kills[0]
                rp = next(v for v in m["replays"].values() if v.get("confirmed"))
                ev = (f"mutant {m['n']}: {m['file']} Gambit {m['gambit_id']} ({m['description']}); "
                      f"replay passes on the original ({rp['on_original']['status']}) and fails on the "
                      f"mutant ({rp['on_target']['reason']})")
            else:
                ev = f"mutants: {mut.get('counts')}"
            check(t["id"], "one Gambit mutant killed and confirmed by the same replay", bool(kills), ev)
        if e.get("linked_dependency_mutated"):
            ran = [m for m in (r.get("mutation") or {}).get("mutants", []) if m.get("run")]
            linked = [m for m in ran if through_link(t["project"], m["file"])]
            check(t["id"], "a mutant of a linked dependency ran, and the original stayed as it was",
                  bool(linked) and r.get("original_unchanged") is True,
                  f"{len(linked)} of the {len(ran)} mutants run are in a linked directory"
                  + (f", such as {linked[0]['file']}" if linked else ""))
        if e.get("repeat"):
            got = (r.get("checks") or {}).get(e["repeat"])
            check(t["id"], f"{e['repeat']} is proved or stopped at a limit, as it may be",
                  got in ("proved", "unfinished", "timeout"), described(r, e["repeat"]))
        if e.get("wrapper_stopped_processes"):
            wc = r["prove"]["wrapper_checks"]
            stopped = [p for c in wc for p in c.get("left_running_and_stopped", [])]
            still = [p for c in wc for p in c.get("still_running_after_stop", [])]
            check(t["id"], "the check's processes were stopped, and none survived",
                  bool(stopped) and not still, f"stopped {stopped}; still running {still}")
        if e.get("runner_stopped_processes"):
            stopped = r["prove"]["left_running_and_stopped"]
            still = r["prove"]["still_running_after_stop"]
            names = {p for p in stopped}
            check(t["id"], "ausweg, Halmos and the solvers were stopped, and none survived",
                  r["prove"]["status"] == "stopped at the deadline" and bool(names & set(SOLVERS)) and not still,
                  f"status {r['prove']['status']}; stopped {sorted(names)}; still running {still}")
        check(t["id"], "the original project is unchanged", r.get("original_unchanged") is True,
              r.get("original_unchanged"))
    # The run's own records.
    mdir = os.path.join(a.out, "manifests")
    man = files.read_json(os.path.join(mdir, sorted(os.listdir(mdir))[-1]))
    check("run", "tool versions match the frozen ones", not man["version_problems"],
          "; ".join(man["version_problems"]) or ", ".join(f"{k} {v.get('reported')}" for k, v in man["tools"].items()))
    ev = [json.loads(x) for x in files.read_lines(os.path.join(a.out, "events.jsonl"))]
    cmds = [x for x in ev if "cmd" in x]
    saved = all(os.path.exists(x["stdout"]) and os.path.exists(x["stderr"]) for x in cmds)
    check("run", "every command saved with its timing and raw output, in order", saved and cmds,
          f"{len(cmds)} commands in events.jsonl")
    allowed = {v["path"] for v in man["tools"].values()}
    used = {p for x in cmds for p in (x.get("executables_used") or {})}
    run_log = os.path.join(a.out, "exec.log")
    if os.path.exists(run_log):
        used |= set(files.read_lines(run_log))
    check("run", "every tool a command ran is a configured one", used and used <= allowed,
          ", ".join(sorted(os.path.basename(p) for p in used)) + (
              f"; not configured: {sorted(used - allowed)}" if used - allowed else ""))
    queries = [x for x in cmds if x.get("label") in ("forge config", "forge remappings")]
    check("run", "forge's queries for Gambit ran under the mutation budget, and were recorded",
          len(queries) >= 2 and all(x["status"] == "exited" and x["returncode"] == 0 for x in queries),
          ", ".join(f"{x['label']} {x['seconds']} s" for x in queries) or "none recorded")
    flag = ["--solver-timeout-branching", f"{man['config']['limits'].get('branch_query_ms')}ms"]
    halmos = []
    for dirpath, _, fnames in os.walk(a.out):
        for f in fnames:
            if f.endswith(".checks.jsonl"):
                halmos += [json.loads(x)["cmd"] for x in files.read_lines(os.path.join(dirpath, f))]
    pinned = [c for c in halmos if any(c[i:i + 2] == flag for i in range(len(c) - 1))]
    check("run", "every Halmos process ran with the configured branch timeout",
          halmos and len(pinned) == len(halmos), f"{len(pinned)} of {len(halmos)} with {' '.join(flag)}")
    seeds = [x for x in cmds if "--fuzz-seed" in x["cmd"]]
    check("run", "every fuzz campaign saved with its seed", bool(seeds),
          f"{len(seeds)} campaigns with --fuzz-seed")
    width = max(len(x[1]) for x in lines)
    for tid, what, res, evidence in lines:
        print(f"{res:4}  {tid:18} {what:{width}}  {evidence}")
    # Every run of each repeated check, the repeats and any other target's.
    for name, contract in dict.fromkeys((t["expect"]["repeat"], t["contract"]) for t in targets
                                        if t.get("expect", {}).get("repeat")):
        print(f"\n{name} on {contract}, every run:")
        for t in targets:
            path = os.path.join(a.out, t["id"], "result.json")
            if t["contract"] == contract and os.path.exists(path):
                r = files.read_json(path)
                if check_run(r, name):
                    print(f"  {t['id']:18} {described(r, name)}")
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()
