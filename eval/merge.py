#!/usr/bin/env -S python3 -I
"""Merge the output directories of a sharded run into one summary.

    python3 -I eval/merge.py --targets <targets.toml> --out <merged dir> <shard dir> ...

Refuses shards whose settings, targets file, runner commit, tool versions or
tool binaries differ; any shard, the first included, with no record or no
sha256 of a tool; and a target that is missing or present twice. Binaries are
compared by sha256: one version built on two machines need not be the same
bytes. The summary lists each shard's.
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import files  # noqa: E402
import run  # noqa: E402


def first_manifest(d):
    m = os.path.join(d, "manifests")
    return files.read_json(os.path.join(m, sorted(os.listdir(m))[0]))


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--targets", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("shards", nargs="+")
    a = ap.parse_args(argv)
    ids = [t["id"] for t in files.read_toml(a.targets)["target"]]
    manifests = {d: first_manifest(d) for d in a.shards}
    ref_dir, ref = next(iter(manifests.items()))
    problems = []
    want = files.sha256(a.targets)
    for d, m in manifests.items():
        if m["targets_sha256"] != want:
            problems.append(f"{d}: ran another targets file than {a.targets}")
        for key in ("config_sha256", "targets_sha256"):
            if m[key] != ref[key]:
                problems.append(f"{d}: {key} differs")
        if m["runner"] != ref["runner"]:
            problems.append(f"{d}: runner commit differs")
        for name in sorted(set(run.TOOLS) | set(m["tools"]) | set(ref["tools"])):
            tool, was = m["tools"].get(name), ref["tools"].get(name) or {}
            if tool is None:
                problems.append(f"{d}: no record of {name}")
                continue
            if not tool.get("sha256"):
                problems.append(f"{d}: {name} has no sha256")
            elif tool["sha256"] != was.get("sha256"):
                problems.append(f"{d}: {name} is not the binary {ref_dir} ran: sha256 "
                                f"{tool['sha256'][:12]}, against {(was.get('sha256') or 'none')[:12]}")
            if tool.get("reported") != was.get("reported"):
                problems.append(f"{d}: {name} reports {tool.get('reported')!r}")
    results, where = {}, {}
    for d in a.shards:
        for tid in ids:
            p = os.path.join(d, tid, "result.json")
            if os.path.exists(p):
                if tid in results:
                    problems.append(f"{tid}: in both {where[tid]} and {d}")
                results[tid] = files.read_json(p)
                where[tid] = d
    missing = [t for t in ids if t not in results]
    if missing:
        problems.append("no result for " + ", ".join(missing))
    if problems:
        sys.exit("\n".join(problems))
    os.makedirs(a.out, exist_ok=True)
    summary = {
        "shards": {d: {"targets": m["targets"], "host": m["host"],
                       "binaries": {n: t.get("sha256") for n, t in m["tools"].items()}}
                   for d, m in manifests.items()},
        "targets": {tid: {"shard": where[tid], "class": r["class"], "checks": r.get("checks"),
                          "mutation": (r.get("mutation") or {}).get("counts"),
                          "kill_rate": (r.get("mutation") or {}).get("kill_rate"),
                          "baselines": run.baseline_summary(r),
                          "original_unchanged": r.get("original_unchanged"),
                          "project_sha256": r.get("project_sha256"), "seconds": r.get("seconds")}
                    for tid, r in results.items()},
        # Every check a solver baseline and `ausweg smt` decided differently,
        # to examine before the results are reported.
        "disagreements": [{"target": tid, **d} for tid, r in results.items()
                          for d in (r.get("baselines") or {}).get("disagreements", [])],
    }
    files.write_json(os.path.join(a.out, "summary.json"), summary)
    print(f"merged {len(results)} targets from {len(a.shards)} shards")
    if summary["disagreements"]:
        print(f"{len(summary['disagreements'])} disagreements between ausweg smt and a solver baseline: "
              "see summary.json")


if __name__ == "__main__":
    main()
