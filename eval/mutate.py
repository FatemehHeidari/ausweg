"""Gambit mutants of the functions an exit calls.

Selection, pinned for the evaluation:
1. Start from the exit entry points that ausweg's exit checks call on the
   target (for ERC-4626: redeem, withdraw, maxRedeem, maxWithdraw,
   previewRedeem, previewWithdraw), each at its most-derived definition.
2. Add every function and modifier that a selected one references, by the
   solc AST, when it is defined in a contract of the target's linearization:
   the target and its base contracts, wherever their files are. A reference
   to a virtual function adds the most-derived override too. Libraries and
   other contracts are not followed, so external calls are not.
3. Gambit mutates each selected function, with every one of its operators,
   in the file that defines it. Mutants are pooled across files, ordered by
   file and Gambit's id, and, beyond the cap, sampled with the seed.
"""

import hashlib
import json
import os
import random
import shutil

import files

OPERATORS = [
    "assignment-mutation",
    "binary-op-mutation",
    "delete-expression-mutation",
    "elim-delegate-mutation",
    "function-call-mutation",
    "if-statement-mutation",
    "require-mutation",
    "swap-arguments-function-mutation",
    "swap-arguments-operator-mutation",
    "unary-operator-mutation",
]

ENTRY_POINTS = {
    "erc4626": ["redeem", "withdraw", "maxRedeem", "maxWithdraw", "previewRedeem", "previewWithdraw"],
}

# Directories that tools write into: never shared between copies.
WRITTEN = {"out", "cache", "broadcast", "test/generated", "test/eval-replay", "gambit_out"}


def _asts(project):
    """absolutePath -> AST, from forge's artifacts (built with --ast)."""
    out = {}
    for dirpath, _, fnames in os.walk(os.path.join(project, "out")):
        for f in fnames:
            if not f.endswith(".json"):
                continue
            try:
                data = files.read_json(os.path.join(dirpath, f))
            except (OSError, ValueError):
                continue
            a = data.get("ast") if isinstance(data, dict) else None
            if a and a.get("absolutePath") not in out:
                out[a["absolutePath"]] = a
    return out


def _walk(node):
    if isinstance(node, dict):
        yield node
        for v in node.values():
            yield from _walk(v)
    elif isinstance(node, list):
        for v in node:
            yield from _walk(v)


def select(project, target_path, contract, kind="erc4626"):
    """The functions an exit calls: a sorted list of (file, contract, name)."""
    asts = _asts(project)
    contracts, functions = {}, {}
    for path, ast in asts.items():
        for n in _walk(ast):
            if n.get("nodeType") == "ContractDefinition":
                contracts[n["id"]] = {"name": n["name"], "file": path, "node": n,
                                      "kind": n.get("contractKind")}
                for m in n.get("nodes", []):
                    if m.get("nodeType") in ("FunctionDefinition", "ModifierDefinition"):
                        functions[m["id"]] = {"name": m.get("name") or m.get("kind"), "contract": n["id"],
                                              "file": path, "node": m,
                                              "params": len(m.get("parameters", {}).get("parameters", []))}
    target = next((c for c in contracts.values() if c["file"] == target_path and c["name"] == contract), None)
    if target is None:
        raise RuntimeError(f"no contract {contract} in {target_path} in forge's ASTs")
    lin = target["node"]["linearizedBaseContracts"]
    in_lin = set(lin)

    def most_derived(name, params):
        for cid in lin:
            for fid, f in functions.items():
                if f["contract"] == cid and f["name"] == name and (params is None or f["params"] == params):
                    return fid
        return None

    todo = []
    for name in ENTRY_POINTS[kind]:
        for cid in lin:
            hits = [fid for fid, f in functions.items() if f["contract"] == cid and f["name"] == name]
            if hits:
                todo.extend(hits)
                break
    seen = set()
    while todo:
        fid = todo.pop()
        if fid in seen:
            continue
        seen.add(fid)
        for n in _walk(functions[fid]["node"]):
            ref = n.get("referencedDeclaration")
            if ref in functions and functions[ref]["contract"] in in_lin:
                todo.append(ref)
                over = most_derived(functions[ref]["name"], functions[ref]["params"])
                if over is not None:
                    todo.append(over)
    picked = set()
    for fid in seen:
        f = functions[fid]
        body = f["node"].get("body")
        if body is None or f["node"].get("nodeType") != "FunctionDefinition":
            continue
        name = f["name"] if f["node"].get("kind") == "function" else f["node"].get("kind")
        picked.add((f["file"], contracts[f["contract"]]["name"], name))
    return sorted(picked)


def generate(project, selected, outdir, gambit, solc, remappings, run_cmd, operators=OPERATORS):
    """Run Gambit once per (file, contract), through run_cmd(argv, cwd, tag,
    label), which bounds it by the mutation budget, as for solc_for. Returns every mutant:
    {file, contract, gambit_id, description, mutant_path, diff}, or an error."""
    groups = {}
    for file, contract, name in selected:
        groups.setdefault((file, contract), []).append(name)
    mutants = []
    for k, ((file, contract), names) in enumerate(sorted(groups.items())):
        out = os.path.join(outdir, f"group{k}")
        shutil.rmtree(out, ignore_errors=True)
        cmd = [gambit, "mutate", "--filename", os.path.join(project, file), "--sourceroot", project,
               "--contract", contract, "--functions", *sorted(set(names)), "--mutations", *operators,
               "--solc", solc, "--outdir", out]
        if remappings:
            cmd += ["--solc_remappings", *remappings]
        r = run_cmd(cmd, project, f"gambit-group{k}", f"gambit on {file}:{contract}")
        results = os.path.join(out, "gambit_results.json")
        if r is None:
            mutants.append({"file": file, "contract": contract,
                            "error": "too little of the mutation budget was left to start Gambit"})
            continue
        if r["status"] != "exited":
            mutants.append({"file": file, "contract": contract, "error": "the mutation budget ended during Gambit"})
            continue
        if r["returncode"] != 0 or not os.path.exists(results):
            mutants.append({"file": file, "contract": contract, "error": f"gambit failed: see {r['stderr']}"})
            continue
        for m in files.read_json(results):
            path = os.path.join(out, m["name"])
            if not mutate_path_ok(out, path):
                mutants.append({"file": file, "contract": contract,
                                "error": f"Gambit named a mutant outside its directory: {m['name']}"})
                continue
            mutants.append({"file": file, "contract": contract, "gambit_id": int(m["id"]),
                            "description": m.get("description"), "diff": m.get("diff"),
                            "mutant_path": path})
    return mutants


def mutate_path_ok(outdir, path):
    return inside(outdir, path) and not os.path.isabs(os.path.relpath(path, outdir))


def sample(mutants, cap, seed):
    """Order by file and Gambit id; beyond the cap, a seeded sample of that order."""
    ok = sorted([m for m in mutants if "error" not in m], key=lambda m: (m["file"], m["gambit_id"]))
    if len(ok) <= cap:
        return ok
    chosen = random.Random(seed).sample(range(len(ok)), cap)
    return [ok[i] for i in sorted(chosen)]


def _link_or_copy(src, dst):
    try:
        os.link(src, dst)
    except OSError:
        shutil.copy2(src, dst)


def copy_project(project, dest):
    """A copy of the project for one run, without the directories tools write
    into. A symlink is followed, so a dependency linked from elsewhere becomes
    a directory of the copy's own and no path in the copy leads back into the
    original. Files are hard links where possible: `apply` removes a file
    before writing its mutant, so the original is never written."""
    def ignore(dirpath, names):
        rel = os.path.relpath(dirpath, project)
        out = []
        for n in names:
            r = os.path.normpath(os.path.join(rel, n))
            if r in WRITTEN or n == ".git":
                out.append(n)
        return out
    shutil.copytree(project, dest, symlinks=False, ignore=ignore, copy_function=_link_or_copy)


def inside(root, path):
    """Whether `path`, symlinks resolved, lies inside `root`."""
    root = os.path.realpath(root)
    return os.path.commonpath([root, os.path.realpath(path)]) == root


def apply(dest, mutant):
    """Write a mutant's file into the copy at `dest`. Refuses a path that
    leaves the copy, by `..`, an absolute path or a symlink."""
    rel = mutant["file"]
    target = os.path.join(dest, rel)
    if os.path.isabs(rel) or not inside(dest, target) or os.path.islink(target):
        raise RuntimeError(f"the mutant's file {rel} is outside the copy {dest}")
    if not os.path.isfile(mutant["mutant_path"]):
        raise RuntimeError(f"no mutant file at {mutant['mutant_path']}")
    os.remove(target)
    shutil.copy(mutant["mutant_path"], target)


def tree_hash(project):
    """A hash of every file the runner may read in a project, by path and
    content, skipping the directories tools write into: to show that runs on
    copies left the original as it was."""
    h = hashlib.sha256()
    for dirpath, dirnames, fnames in os.walk(project, followlinks=True):
        rel = os.path.relpath(dirpath, project)
        dirnames[:] = sorted(d for d in dirnames
                             if os.path.normpath(os.path.join(rel, d)) not in WRITTEN and d != ".git")
        for f in sorted(fnames):
            p = os.path.join(dirpath, f)
            h.update(os.path.normpath(os.path.join(rel, f)).encode() + b"\0")
            try:
                with open(p, "rb") as fh:
                    h.update(hashlib.sha256(fh.read()).digest())
            except OSError:
                h.update(b"unreadable")
    return h.hexdigest()


def solc_for(project, forge, run_cmd):
    """The solc binary forge uses for the project, its version and its
    remappings, asked of forge through run_cmd(argv, cwd, tag, label). That
    runs each command under the caller's budget and returns its record, or
    None when too little of the budget is left to start it. Returns
    {path, version, remappings}, or {error}."""
    answers = {}
    for key, argv in (("config", [forge, "config", "--json"]), ("remappings", [forge, "remappings"])):
        r = run_cmd(argv, project, f"forge-{key}", f"forge {key}")
        if r is None:
            return {"error": f"too little of the mutation budget was left to start forge {key}"}
        if r["status"] != "exited":
            return {"error": f"forge {key} was stopped at the end of the mutation budget"}
        if r["returncode"] != 0:
            return {"error": f"forge {key} failed: see {r['stderr']}"}
        answers[key] = files.read_text(r["stdout"], errors="replace")
    try:
        cfg = json.loads(answers["config"])
    except ValueError:
        return {"error": "forge config --json printed no JSON"}
    version = cfg.get("solc") or cfg.get("solc_version")
    path = None
    if version and os.path.sep in str(version):
        path = version
    elif version:
        cand = os.path.expanduser(f"~/.svm/{version}/solc-{version}")
        path = cand if os.path.exists(cand) else None
    if path is None:
        return {"error": f"forge's solc {version} is not installed"}
    return {"path": path, "version": version, "remappings": answers["remappings"].split()}
