#!/usr/bin/env -S python3 -I
"""Fetch pilot targets' projects as their contest repos pin them (Step 24).

    python3 -I eval/pilot/prepare.py eval/pilot/targets.toml DEST

For each target: the contest repo at the manifest's commit; every git
submodule under the project at the commit the repo records, recursively;
and, if forge's libs include node_modules and the project has a yarn.lock,
its JavaScript packages from that lockfile, with install scripts off, and
then every file the repo commits as it was. Nothing else is changed. A
submodule that cannot be had at its recorded commit is left empty, a
lockfile that does not match package.json installs nothing, and either
setup is reported failed: no other version stands in for what is pinned.
Writes DEST/prepare.json with each target's setup.
"""

import json
import os
import shutil
import subprocess
import sys
import tomllib


def sh(argv, cwd):
    r = subprocess.run(argv, cwd=cwd, capture_output=True, text=True)
    return r.returncode, (r.stdout + r.stderr).strip()


def gitlinks(repo, under):
    """Each submodule path under `under` that this repo records, with its commit."""
    code, out = sh(["git", "ls-files", "-s", "--", under], repo)
    return [(line.split()[3], line.split()[1]) for line in out.splitlines() if line.startswith("160000 ")]


def submodules(repo, under, problems, depth=0):
    """Check out each submodule at its recorded commit, then its own, recursively."""
    for path, commit in gitlinks(repo, under):
        sh(["git", "submodule", "init", "--", path], repo)
        code, out = sh(["git", "submodule", "update", "--", path], repo)
        sub = os.path.join(repo, path)
        code_head, head = sh(["git", "rev-parse", "HEAD"], sub) if os.path.isdir(os.path.join(sub, ".git")) or \
            os.path.isfile(os.path.join(sub, ".git")) else (1, "")
        if code or code_head or head != commit:
            problems.append(f"{os.path.relpath(sub, repo)}: cannot be had at its recorded commit {commit[:12]}: "
                            + (out.splitlines()[-1] if out else "no checkout"))
            shutil.rmtree(sub, ignore_errors=True)
            os.makedirs(sub, exist_ok=True)
            continue
        submodules(sub, ".", problems, depth + 1)


def main():
    targets = tomllib.load(open(sys.argv[1], "rb"))["target"]
    dest = os.path.abspath(sys.argv[2])
    os.makedirs(dest, exist_ok=True)
    report = {}
    for t in targets:
        src = t["source"]
        repo = os.path.join(dest, src["repo"].split("/")[1])
        problems = []
        if not os.path.isdir(os.path.join(repo, ".git")):
            code, out = sh(["git", "clone", "-q", f"https://github.com/{src['repo']}", repo], dest)
            if code:
                report[t["id"]] = {"problems": [f"clone failed: {out}"]}
                continue
        sh(["git", "checkout", "-q", "--force", src["commit"]], repo)
        code, head = sh(["git", "rev-parse", "HEAD"], repo)
        if head != src["commit"]:
            problems.append(f"the contest repo has no commit {src['commit']}")
        submodules(repo, src["project"], problems)
        project = os.path.join(repo, src["project"])
        js = None
        foundry = tomllib.load(open(os.path.join(project, "foundry.toml"), "rb")) if \
            os.path.exists(os.path.join(project, "foundry.toml")) else {}
        libs = foundry.get("profile", {}).get("default", {}).get("libs", [])
        if "node_modules" in libs and os.path.exists(os.path.join(project, "yarn.lock")):
            yarn = shutil.which("yarn") or shutil.which("yarnpkg") or "yarn"
            code, out = sh([yarn, "install", "--frozen-lockfile", "--ignore-scripts", "--non-interactive",
                            "--silent"], project)
            js = {"lockfile": "yarn.lock", "yarn": sh([yarn, "--version"], project)[1], "ok": code == 0,
                  "output": out[-2000:]}
            if code:
                problems.append("yarn install from yarn.lock failed: " + (out.splitlines()[-1] if out else ""))
            # yarn removes packages package.json does not list, even ones the
            # repo commits under node_modules: the repo's own files win.
            sh(["git", "checkout", "--", src["project"]], repo)
        code, changed = sh(["git", "status", "--porcelain", "--untracked-files=no", "--ignore-submodules=all",
                            "--", src["project"]], repo)
        if changed:
            problems.append("files the repo commits differ after setup: " + changed.splitlines()[0])
        report[t["id"]] = {"repo": src["repo"], "commit": head, "project": project, "javascript": js,
                           "problems": problems}
        print(f"{t['id']}: " + ("ready" if not problems else "; ".join(problems)), flush=True)
    with open(os.path.join(dest, "prepare.json"), "w") as f:
        json.dump(report, f, indent=1)


if __name__ == "__main__":
    main()
