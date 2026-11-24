#!/usr/bin/env -S python3 -I
"""The ausweg evaluation runner.

    python3 -I eval/run.py --config eval/config.toml --targets <targets.toml> --out <dir>
        [--resume] [--shard K/N] [--only id,id]

For each target, in the order listed: copy the project, build it, run
`ausweg prove` with the frozen settings, replay each exit counterexample from
deployment, then run the selected Gambit mutants and replay each kill on the
original and on the mutant. Every command is saved with its arguments,
working directory, environment, timing and raw output, in execution order
(events.jsonl), and so is every tool executable it ran (each tool is reached
through a logging shim in <out>/bin). Results go to <out>/<target>/result.json
and <out>/summary.json.

Budgets, per target (config.toml, [limits], says the same):
- target_seconds, by the clock: copying and building the target, and
  ausweg's run on it as audited. ausweg is stopped at its end.
- mutation_seconds, by the clock: choosing the functions, Gambit, and every
  mutant's copy, build and run. Nothing in it runs past its end.
- replay_seconds, by the work done: every replay search and replay for the
  target and its mutants. Each is charged what it took.
A target therefore takes at most target_seconds + mutation_seconds +
replay_seconds, plus the runner's own bookkeeping between them.

--resume skips targets that have a result.json, and redoes one that was
interrupted. --shard K/N runs every target whose position in the list, from
0, leaves K - 1 when divided by N. A resumed or sharded run refuses to go on
if its settings, targets, tools or runner commit differ from the first run's
in the same directory.
"""

import argparse
import collections
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import files  # noqa: E402
import mutate  # noqa: E402
import proc  # noqa: E402
import replay  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
WRAPPER = os.path.join(HERE, "halmos_per_check.py")
REPORT_RESERVE = 60  # seconds kept, inside the target budget, for ausweg's report
MIN_START = 5  # a step with less time left than this is not started
# Environment variables a command keeps from the runner's own; every other
# one, such as AUSWEG_SMT_SOLVER, is dropped.
KEEP_ENV = ("HOME", "USER", "LOGNAME", "LANG", "LC_ALL", "TMPDIR", "TERM")
SHIMS = {"forge": "forge", "halmos": "halmos", "z3": "z3", "yices-smt2": "yices"}
# Every tool a manifest records, each with its path and sha256.
TOOLS = ("ausweg", "gambit", *SHIMS, "python3")

REFUSALS = [
    r"not an ERC-4626 vault ausweg can prove",
    r"not an ERC-7540 vault ausweg can prove",
    r"constructor parameter .* has no default",
    r"no constructor parameter takes the asset token",
    r"the proof supports one asset token",
    r"supports no constructor addresses besides the asset",
    r"ausweg calls fulfillRedeem",
    r"does not cover that accounting yet",
    r"numbers its requests is not supported",
]


# ------------------------------------------------------------------ budgets

class Window:
    """A budget by the clock: every step in it ends by `end`."""

    def __init__(self, seconds):
        self.seconds = seconds
        self.start = time.monotonic()
        self.end = self.start + seconds

    def left(self):
        return self.end - time.monotonic()

    def can_start(self):
        return self.left() >= MIN_START


class ReplayBudget:
    """A budget of replay work only: each replay step may use what is left,
    and is charged what it took. Time spent on anything else is not charged."""

    def __init__(self, seconds):
        self.remaining = float(seconds)

    def left(self):
        return max(0.0, self.remaining)

    def step(self, fn):
        """Run fn(deadline). Returns (result, True), or (None, False) when
        too little is left to start."""
        if self.left() < MIN_START:
            return None, False
        t0 = time.monotonic()
        try:
            return fn(t0 + self.left()), True
        finally:
            self.remaining -= time.monotonic() - t0


# ---------------------------------------------------------------- the run

def real_path(cmd):
    p = shutil.which(cmd) or cmd
    return os.path.realpath(p)


class Run:
    def __init__(self, cfg, out):
        self.cfg = cfg
        self.out = out
        self.events = os.path.join(out, "events.jsonl")
        self.bin = os.path.join(out, "bin")
        os.makedirs(self.bin, exist_ok=True)
        t = cfg["tools"]
        self.real = {name: real_path(t[key]["bin"]) for name, key in SHIMS.items()}
        self.real["python3"] = os.path.realpath(sys.executable)
        for name, real in self.real.items():
            shim = os.path.join(self.bin, name)
            with open(shim, "w") as f:
                f.write("#!/bin/sh\n"
                        f"printf '%s\\n' '{real}' >> \"${{EVAL_EXEC_LOG:-/dev/null}}\"\n"
                        f"exec '{real}' \"$@\"\n")
            os.chmod(shim, 0o755)
        self.forge = os.path.join(self.bin, "forge")
        self.halmos = os.path.join(self.bin, "halmos")
        self.base_env = {k: os.environ[k] for k in KEEP_ENV if k in os.environ}
        self.base_env["PATH"] = os.pathsep.join([self.bin, "/usr/bin", "/bin"])
        self.base_env["FOUNDRY_DYNAMIC_TEST_LINKING"] = "false"

    def env(self, extra=None, exec_log=None):
        e = dict(self.base_env)
        e["EVAL_EXEC_LOG"] = exec_log or os.path.join(self.out, "exec.log")
        e.update(extra or {})
        return e

    def cmd(self, argv, cwd, deadline, logdir, tag, extra_env=None, label=""):
        """Run a command until it ends or the monotonic deadline passes."""
        os.makedirs(logdir, exist_ok=True)
        exec_log = os.path.join(logdir, f"{tag}.exec.log")
        env = self.env(extra_env, exec_log)
        r = proc.run(argv, cwd, env, deadline, os.path.join(logdir, f"{tag}.stdout"),
                     os.path.join(logdir, f"{tag}.stderr"), label=label or tag)
        used = collections.Counter(files.read_lines(exec_log)) if os.path.exists(exec_log) else {}
        r["executables_used"] = dict(used)
        r["env"] = env
        with open(self.events, "a") as f:
            f.write(json.dumps(r) + "\n")
        return r


# ----------------------------------------------------------------- versions

def tool_versions(run):
    """Each tool's version as it reports it through its shim, its path and
    hash, against the frozen one."""
    cfg = run.cfg
    t = cfg["tools"]

    def first_line(argv):
        try:
            r = subprocess.run(argv, capture_output=True, text=True, timeout=60, env=run.env())
            return (r.stdout or r.stderr).strip().splitlines()[0]
        except (OSError, subprocess.SubprocessError, IndexError):
            return None

    def sha256(path):
        try:
            return files.sha256(path)
        except OSError:
            return None

    out = {name: {"path": real, "sha256": sha256(real)} for name, real in run.real.items()}
    ausweg = real_path(t["ausweg"]["bin"])
    gambit = real_path(t["gambit"]["bin"])
    out["ausweg"] = {"path": ausweg, "sha256": sha256(ausweg), "reported": first_line([ausweg, "--version"])}
    out["gambit"] = {"path": gambit, "sha256": sha256(gambit), "reported": None,
                     "note": "Gambit prints no version: config.toml gives its tag and commit"}
    out["halmos"]["reported"] = first_line([run.halmos, "--version"])
    out["z3"]["reported"] = first_line([os.path.join(run.bin, "z3"), "--version"])
    out["yices-smt2"]["reported"] = first_line([os.path.join(run.bin, "yices-smt2"), "--version"])
    try:
        forge_v = subprocess.run([run.forge, "--version"], capture_output=True, text=True, timeout=60,
                                 env=run.env()).stdout
    except (OSError, subprocess.SubprocessError):
        forge_v = ""
    out["forge"]["reported"] = forge_v.strip().splitlines()[0] if forge_v else None
    out["forge"]["commit"] = next((ln.split(":", 1)[1].strip() for ln in forge_v.splitlines()
                                   if ln.startswith("Commit SHA")), None)
    # Halmos also uses z3 in its own process, through the z3-solver module.
    shebang = (files.read_lines(run.real["halmos"]) or [""])[0]
    py = shebang[2:].strip().split()[0] if shebang.startswith("#!") else None
    out["halmos"]["z3_module"] = first_line([py, "-c", "import z3; print(z3.get_version_string())"]) if py else None
    problems = []
    for name, want in (("ausweg", t["ausweg"]["version"]), ("halmos", t["halmos"]["version"]),
                       ("z3", t["z3"]["version"]), ("yices-smt2", t["yices"]["version"]),
                       ("forge", t["forge"]["version"])):
        got = out[name]["reported"] or ""
        if not got.startswith(want):
            problems.append(f"{name}: expected {want!r}, found {got!r}")
    if out["forge"]["commit"] != t["forge"]["commit"]:
        problems.append(f"forge: expected commit {t['forge']['commit']}, found {out['forge']['commit']}")
    want_z3 = t["z3"]["version"].split()[-1]
    if not (out["halmos"]["z3_module"] or "").startswith(want_z3):
        problems.append(f"Halmos's z3 module: expected {want_z3}, found {out['halmos']['z3_module']!r}")
    return out, problems


def runner_commit():
    def git(*a):
        try:
            r = subprocess.run(["git", "-C", HERE, *a], capture_output=True, text=True, timeout=60)
        except (OSError, subprocess.SubprocessError):
            return None
        return r.stdout.strip() if r.returncode == 0 else None
    status = git("status", "--porcelain", "--", ".")
    return {"commit": git("rev-parse", "HEAD"), "eval_dir_changed_since": bool(status), "status": status}


# ------------------------------------------------------------------- proving

def prove(run, work, target, window, logdir, tag, mutant=False, only=None, hooks=None):
    """ausweg prove on one project copy, ending by the window's end. Returns
    its report, the Halmos wrapper's per-check record, and the run's record."""
    p = run.cfg["prove"]
    limits = dict(run.cfg["limits"])
    limits.update((hooks or {}).get("limits", {}))
    json_path = os.path.join(logdir, f"{tag}.report.json")
    record = os.path.join(logdir, f"{tag}.checks.jsonl")
    os.makedirs(logdir, exist_ok=True)
    for f in (json_path, record):
        if os.path.exists(f):
            os.remove(f)
    argv = [real_path(run.cfg["tools"]["ausweg"]["bin"]), "prove", "--contract", target, "--no-mutation",
            "--solver-timeout", str(limits["query_seconds"]),
            "--check-rewrite", p["mutant_check_rewrite"] if mutant else p["check_rewrite"],
            "--check-every", str(p["check_every"]), "--check-seed", str(p["check_seed"]),
            "--check-timeout", str(p["check_timeout"]),
            "--halmos", WRAPPER, "--forge-bin", run.forge, "--json", json_path]
    if p.get("loop") is not None:
        argv += ["--loop", str(p["loop"])]
    if p.get("bound_amounts"):
        argv.append("--bound-amounts")
    if not p.get("price", True):
        argv.append("--no-price")
    # The checks stop early enough for ausweg to write its report in time.
    reserve = min(REPORT_RESERVE, 0.2 * window.seconds)
    checks_end = time.time() + (window.end - reserve - time.monotonic())
    extra = {
        "EVAL_REAL_HALMOS": run.halmos,
        "EVAL_CHECK_CAP": str(limits["check_seconds"]),
        "EVAL_TARGET_DEADLINE": str(checks_end),
        "EVAL_CHECK_RECORD": record,
        "EVAL_LOG_DIR": os.path.join(logdir, f"{tag}.halmos"),
    }
    if limits.get("branch_query_ms") is not None:
        extra["EVAL_BRANCH_TIMEOUT"] = f"{limits['branch_query_ms']}ms"
    if only:
        extra["EVAL_ONLY_CHECKS"] = ",".join(only)
    if mutant:
        extra["EVAL_EARLY_EXIT"] = "1"
        extra["EVAL_CHECK_ORDER"] = "exits-first"
    deadline = window.end
    if hooks and "runner_seconds" in hooks:
        deadline = min(deadline, time.monotonic() + hooks["runner_seconds"])
    r = run.cmd(argv, work, deadline, logdir, tag, extra_env=extra, label=f"ausweg prove {target} ({tag})")
    report = None
    if os.path.exists(json_path):
        try:
            report = files.read_json(json_path)
        except ValueError:
            report = None
    checks = []
    if os.path.exists(record):
        checks = [json.loads(ln) for ln in files.read_lines(record)]
    return {"report": report, "checks": checks, "run": r, "argv": argv, "asked": asked_checks(work, only)}


def asked_checks(work, only):
    """The checks of ausweg's proof file, or the subset a test asked for."""
    gen = os.path.join(work, "test", "generated")
    names = []
    for dirpath, _, fnames in os.walk(gen):
        for f in sorted(fnames):
            if f.endswith(".proof.t.sol"):
                names += re.findall(r"\bfunction\s+(check_\w+)\s*\(", files.read_text(os.path.join(dirpath, f)))
    names = list(dict.fromkeys(names))
    return [c for c in names if c in only] if only else names


def check_classes(result):
    """Each check's class, from ausweg's report and the wrapper's record:
    proved, counterexample, timeout, unfinished, incomplete, vacuous or
    error. A check with no result has no class."""
    classes = {}
    rep = (result["report"] or {}).get("reports") or []
    if rep:
        for c in rep[0].get("checks", []):
            classes[c["name"]] = {"proved": "proved", "counterexample": "counterexample",
                                  "timeout": "timeout", "incomplete": "incomplete",
                                  "vacuous": "vacuous"}.get(c["verdict"], "error")
    for c in result["checks"]:
        if c["outcome"].startswith(("unfinished", "not started")):
            classes[c["check"]] = "unfinished"
    if result["run"]["status"] != "exited":
        # Stopped by the runner: every check asked for and not finished is
        # unfinished, whether or not the wrapper got to record it.
        for c in result.get("asked", []):
            if classes.get(c) not in ("proved", "counterexample"):
                classes[c] = "unfinished"
    return classes


def mutant_class(result, classes, asked):
    """A mutant's class before replay. "counterexample" means a claimed kill.
    It survived only if ausweg reported and every check asked for was proved;
    anything missing or unfinished is inconclusive."""
    if any(classes.get(c) == "counterexample" for c in asked):
        return "counterexample"
    if result["report"] is None or not asked:
        return "inconclusive"
    if all(classes.get(c) == "proved" for c in asked):
        return "survived"
    return "inconclusive"


def refusal(result):
    rep = result["report"] or {}
    text = " ".join(json.dumps(f) for f in rep.get("failed", []))
    if not text and not rep.get("reports"):
        try:
            text = files.read_text(result["run"]["stderr"], errors="replace")[-4000:]
        except OSError:
            text = ""
    for pat in REFUSALS:
        if re.search(pat, text):
            return text.strip()[:600]
    return None


def target_class(result, classes, confirmed):
    if result["run"]["status"] != "exited" and not result["report"]:
        return "unfinished"
    if refusal(result):
        return "unsupported"
    if not (result["report"] or {}).get("reports"):
        return "other inconclusive"
    if any(v == "counterexample" for k, v in classes.items() if k in confirmed):
        return "confirmed counterexample"
    if any(v == "counterexample" for v in classes.values()):
        return "unconfirmed counterexample"
    rep = result["report"]["reports"][0]
    proved = rep.get("full_exit_proved") if "full_exit_proved" in rep else rep.get("liquidity_proved")
    asked = result.get("asked") or list(classes)
    if proved and asked and all(classes.get(c) == "proved" for c in asked):
        return "proved"
    for c in ("timeout", "unfinished", "incomplete"):
        if c in classes.values():
            return c
    return "other inconclusive"


# -------------------------------------------------------------------- replay

def confirm(run, project, target_path, contract, abi, checks, budget, logdir, tag, original=None):
    """Search for each exit check's failure from deployment, and replay it,
    within the target's replay budget. With `original`, a confirmation also
    needs the replay to pass there."""
    out = {}
    wanted = [c for c in checks if c in replay.PROPERTIES]
    for c in checks:
        if c not in replay.PROPERTIES:
            out[c] = {"confirmed": False, "why": "not an exit property: the replay checks exit properties only"}
    if not wanted:
        return out
    why = replay.install(project, target_path, contract, abi)
    if why:
        return {c: {"confirmed": False, "why": f"no replay: {why}"} for c in wanted} | out
    if original:
        replay.install(original, target_path, contract, abi)
    spent = {c: {"confirmed": False, "why": "the target's replay budget was spent"} for c in wanted}
    got, ran = budget.step(lambda deadline: replay.search(
        project, wanted, deadline, run.cfg["replay"], run.forge, run.env(), logdir, run.events,
        run.cfg["replay"]["first_seed"]))
    if not ran:
        return spent | out
    found, campaigns = got
    for c in wanted:
        if c not in found:
            out[c] = {"confirmed": False, "why": "the search found no failure within the budget",
                      "campaigns": campaigns}
            continue
        f = found[c]
        name = f"AuswegEvalTrace_{re.sub(r'[^A-Za-z0-9_]', '_', tag)}_{c[len('check_exit_'):]}"
        trace = replay.write_trace(project, c, f, name)
        entry = {"search": {"seed": f["seed"], "reason": f["reason"], "calls": len(f["sequence"]),
                            "saved_sequence": f["saved"]},
                 "trace": trace, "campaigns": campaigns, "confirmed": False}
        out[c] = entry
        on_target, ran = budget.step(lambda deadline: replay.run_trace(
            project, trace, name, run.forge, run.env(), deadline, logdir, run.events,
            "mutant" if original else "target"))
        if not ran:
            entry["why"] = "the target's replay budget was spent before the replay"
            continue
        entry["on_target"] = on_target
        if not original:
            entry["confirmed"] = on_target["exit_failed"]
            continue
        on_original, ran = budget.step(lambda deadline: replay.run_trace(
            original, trace, name, run.forge, run.env(), deadline, logdir, run.events, "original"))
        if not ran:
            entry["why"] = "the target's replay budget was spent before the replay on the original"
            continue
        entry["on_original"] = on_original
        entry["confirmed"] = on_target["exit_failed"] and on_original["passed"]
    return out


# ------------------------------------------------------------------- targets

def build(run, work, deadline, logdir, tag):
    """True if the project builds, False if it does not, None if there was
    no time left to start."""
    if deadline - time.monotonic() < MIN_START:
        return None
    r = run.cmd([run.forge, "build", "--ast"], work, deadline, logdir, tag, label=f"forge build ({tag})")
    if r["status"] != "exited":
        return None
    return r["returncode"] == 0


def run_target(run, t, original_hash):
    """One target, from the original project, whose hash the caller took."""
    tid = t["id"]
    tdir = os.path.join(run.out, tid)
    logs = os.path.join(tdir, "logs")
    os.makedirs(logs, exist_ok=True)
    hooks = t.get("test_hooks", {})
    limits = dict(run.cfg["limits"])
    limits.update(hooks.get("limits", {}))
    res = {"id": tid, "contract": t["contract"], "label": t.get("label"), "test_hooks": hooks}
    started = time.monotonic()
    window = Window(limits["target_seconds"])
    work = os.path.join(tdir, "work")
    shutil.rmtree(work, ignore_errors=True)
    mutate.copy_project(t["project"], work)
    built = build(run, work, window.end, logs, "build")
    if not built:
        res["class"] = "other inconclusive" if built is False else "unfinished"
        res["why"] = "the project does not build" if built is False else "the target's budget was spent"
        return finish(res, t, original_hash, started, window)
    name = os.path.splitext(os.path.basename(t["contract"]))[0]
    abi = files.read_json(os.path.join(work, "out", os.path.basename(t["contract"]), f"{name}.json"))["abi"]
    if not window.can_start():
        res.update({"class": "unfinished", "why": "the target's budget was spent before the proof"})
        return finish(res, t, original_hash, started, window)
    clean = prove(run, work, t["contract"], window, logs, "prove", only=hooks.get("only_checks"), hooks=hooks)
    classes = check_classes(clean)
    replay_budget = ReplayBudget(limits["replay_seconds"])
    claimed = [c for c, v in classes.items() if v == "counterexample"]
    confirmations = confirm(run, work, t["contract"], name, abi, claimed, replay_budget, logs, "target")
    confirmed = {c for c, v in confirmations.items() if v.get("confirmed")}
    res.update({
        "class": target_class(clean, classes, confirmed),
        "checks": {c: ("confirmed counterexample" if c in confirmed else
                       "unconfirmed counterexample" if v == "counterexample" else v)
                   for c, v in classes.items()},
        "replays": confirmations,
        "refusal": refusal(clean),
        "verdict": {k: ((clean["report"] or {}).get("reports") or [{}])[0].get(k)
                    for k in ("full_exit_proved", "full_exit_withheld", "liquidity_proved", "withheld")},
        "prove": {"argv": clean["argv"], "seconds": clean["run"]["seconds"], "status": clean["run"]["status"],
                  "returncode": clean["run"]["returncode"],
                  "left_running_and_stopped": clean["run"]["left_running_and_stopped"],
                  "still_running_after_stop": clean["run"]["still_running_after_stop"],
                  "executables_used": clean["run"]["executables_used"],
                  "wrapper_checks": clean["checks"]},
    })
    if t.get("mutate"):
        res["mutation"] = run_mutants(run, t, work, name, abi, classes, replay_budget, logs, hooks, limits)
    res["replay_seconds_left"] = round(replay_budget.left(), 3)
    return finish(res, t, original_hash, started, window)


def finish(res, t, original_hash, started, window):
    res["original_unchanged"] = mutate.tree_hash(t["project"]) == original_hash
    res["seconds"] = round(time.monotonic() - started, 3)
    res["target_budget_left"] = round(window.left(), 3)
    return res


def run_mutants(run, t, work, name, abi, classes, replay_budget, logs, hooks, limits):
    window = Window(limits["mutation_seconds"])
    proved = [c for c, v in classes.items() if v == "proved"]
    out = {"selection": None, "mutants": []}
    if not proved:
        out["note"] = "no check was proved on the target as audited, so no mutant can break a proof"
    sel = mutate.select(work, t["contract"], name)
    out["selection"] = [{"file": f, "contract": c, "function": fn} for f, c, fn in sel]

    def cmd(argv, cwd, tag, label):
        # Every command of the mutation step, under its budget.
        if not window.can_start():
            return None
        return run.cmd(argv, cwd, window.end, logs, tag, label=label)

    m = run.cfg["mutation"]
    solc = mutate.solc_for(work, run.forge, cmd)
    if "error" in solc:
        out["not_run"] = solc["error"]
        allm = []
    else:
        allm = mutate.generate(work, sel, os.path.join(os.path.dirname(work), "gambit"),
                               real_path(run.cfg["tools"]["gambit"]["bin"]), solc["path"], solc["remappings"],
                               cmd, operators=m["operators"])
    picked = mutate.sample(allm, m["max_mutants"], m["seed"])
    out.update(generated=len([x for x in allm if "error" not in x]),
               gambit_errors=[x for x in allm if "error" in x], selected=len(picked), solc=solc.get("version"))
    stop_after = hooks.get("stop_after_confirmed_kills")
    kills = 0
    for k, mu in enumerate(picked):
        entry = {"n": k, "file": mu["file"], "gambit_id": mu["gambit_id"], "description": mu["description"],
                 "diff": mu["diff"]}
        out["mutants"].append(entry)
        if not proved:
            entry["class"] = "not run: nothing proved on the original"
            continue
        if stop_after and kills >= stop_after:
            entry["class"] = "not run: the smoke test stops at its first confirmed kill"
            continue
        if not window.can_start():
            entry["class"] = "not run: the mutation budget was spent"
            continue
        mdir = os.path.join(os.path.dirname(work), "mutants", f"m{k:03d}")
        shutil.rmtree(mdir, ignore_errors=True)
        mutate.copy_project(work, mdir)
        mutate.apply(mdir, mu)
        mlogs = os.path.join(logs, f"mutant{k:03d}")
        built = build(run, mdir, window.end, mlogs, "build")
        if built is None:
            entry["class"] = "not run: the mutation budget was spent"
            continue
        if built is False:
            entry["class"] = "does not compile"
            continue
        if not window.can_start():
            entry["class"] = "not run: the mutation budget was spent"
            continue
        r = prove(run, mdir, t["contract"], window, mlogs, "prove", mutant=True, only=proved)
        mclasses = check_classes(r)
        entry["checks"] = mclasses
        entry["run"] = {"status": r["run"]["status"], "returncode": r["run"]["returncode"],
                        "seconds": r["run"]["seconds"], "report": r["report"] is not None}
        cls = mutant_class(r, mclasses, proved)
        if cls == "counterexample":
            broken = [c for c in proved if mclasses.get(c) == "counterexample"]
            conf = confirm(run, mdir, t["contract"], name, abi, broken, replay_budget, mlogs, f"m{k:03d}",
                           original=work)
            entry["replays"] = conf
            entry["class"] = ("killed, confirmed" if any(v.get("confirmed") for v in conf.values())
                              else "killed, unconfirmed")
            kills += entry["class"] == "killed, confirmed"
        else:
            entry["class"] = cls
        shutil.rmtree(os.path.join(mdir, "out"), ignore_errors=True)
    cl = [x.get("class") for x in out["mutants"]]
    compiling = [c for c in cl if c != "does not compile"]
    out["counts"] = {c: cl.count(c) for c in sorted(set(cl))}
    out["kill_rate"] = {"confirmed_kills": cl.count("killed, confirmed"), "out_of": len(compiling),
                        "note": "every selected mutant that compiles, run or not"}
    out["budget_left"] = round(window.left(), 3)
    return out


# --------------------------------------------------------------- run control

def shard_of(targets, shard):
    if not shard:
        return targets
    k, n = (int(x) for x in shard.split("/"))
    if not 1 <= k <= n:
        raise SystemExit(f"--shard {shard}: K must be between 1 and N")
    return [t for i, t in enumerate(targets) if i % n == k - 1]


def file_hash(path):
    return files.sha256(path)


def finished(path):
    """A target's result is there and whole."""
    try:
        files.read_json(path)
        return True
    except (OSError, ValueError):
        return False


def changed_sources(out, targets):
    """Finished targets whose project, dependencies included, no longer hashes
    as it did when the target ran."""
    now, changed = {}, []
    for t in targets:
        done = os.path.join(out, t["id"], "result.json")
        if not finished(done):
            continue
        p = os.path.realpath(t["project"])
        if p not in now:
            now[p] = mutate.tree_hash(p)
        if files.read_json(done).get("project_sha256") != now[p]:
            changed.append(t["id"])
    return changed


def same_run(first, now):
    """What differs between the first run in a directory and this one."""
    diffs = []
    for key in ("config_sha256", "targets_sha256"):
        if first.get(key) != now.get(key):
            diffs.append(key)
    for name, tool in now["tools"].items():
        was = first["tools"].get(name, {})
        if was.get("sha256") != tool.get("sha256") or was.get("reported") != tool.get("reported"):
            diffs.append(f"tool {name}")
    if first["runner"].get("commit") != now["runner"].get("commit") or \
            first["runner"].get("status") != now["runner"].get("status"):
        diffs.append("runner commit")
    if first.get("shard") != now.get("shard"):
        diffs.append("shard")
    return diffs


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", required=True)
    ap.add_argument("--targets", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--only", help="run only these target ids, comma-separated")
    ap.add_argument("--shard", help="K/N: this machine's share of the targets")
    ap.add_argument("--resume", action="store_true", help="skip targets with a result; redo interrupted ones")
    a = ap.parse_args(argv)
    cfg = files.read_toml(a.config)
    targets = files.read_toml(a.targets)["target"]
    if a.only:
        targets = [t for t in targets if t["id"] in a.only.split(",")]
    targets = shard_of(targets, a.shard)
    os.makedirs(a.out, exist_ok=True)
    subreaper = proc.become_subreaper()
    run = Run(cfg, a.out)
    versions, problems = tool_versions(run)
    manifest = {
        "started": time.time(), "config_file": os.path.abspath(a.config), "config_sha256": file_hash(a.config),
        "config": cfg, "targets_file": os.path.abspath(a.targets), "targets_sha256": file_hash(a.targets),
        "targets": [t["id"] for t in targets], "shard": a.shard, "resume": a.resume,
        "tools": versions, "version_problems": problems, "runner": runner_commit(),
        "host": {"platform": platform.platform(), "cpus": os.cpu_count(), "python": sys.version,
                 "subreaper": subreaper},
        "environment": run.base_env,
    }
    mdir = os.path.join(a.out, "manifests")
    os.makedirs(mdir, exist_ok=True)
    earlier = sorted(os.listdir(mdir))
    if earlier:
        if not a.resume:
            raise SystemExit(f"{a.out} holds an earlier run: use --resume to go on with it, or a new directory")
        diffs = same_run(files.read_json(os.path.join(mdir, earlier[0])), manifest)
        if diffs:
            raise SystemExit("this run differs from the first one in the same directory: " + ", ".join(diffs))
        changed = changed_sources(a.out, targets)
        if changed:
            raise SystemExit("these targets' sources changed since their results were made: " + ", ".join(changed)
                             + f"\nstart a new directory, or remove their directories in {a.out} to run them again")
    files.write_json(os.path.join(mdir, f"{len(earlier) + 1:03d}.json"), manifest)
    if problems and not cfg["runner"].get("allow_version_mismatch"):
        raise SystemExit("tool versions differ from the frozen ones:\n  " + "\n  ".join(problems))
    for t in targets:
        tdir = os.path.join(a.out, t["id"])
        done = os.path.join(tdir, "result.json")
        if a.resume and finished(done):
            print(f"== {t['id']}: done in an earlier run", flush=True)
            continue
        if os.path.exists(tdir):
            # Interrupted, or not resumed: start the target again.
            shutil.rmtree(tdir)
        print(f"== {t['id']}", flush=True)
        project_hash = mutate.tree_hash(t["project"])
        r = run_target(run, t, project_hash)
        r["project_sha256"] = project_hash
        os.makedirs(tdir, exist_ok=True)
        files.write_json(done, r)
        print(f"   {r['class']}" + (f" ({r.get('why')})" if r.get("why") else ""), flush=True)
    results = [files.read_json(os.path.join(a.out, t["id"], "result.json")) for t in targets
               if os.path.exists(os.path.join(a.out, t["id"], "result.json"))]
    summary = {"finished": time.time(), "shard": a.shard,
               "targets": {r["id"]: {"class": r["class"], "checks": r.get("checks"),
                                     "mutation": (r.get("mutation") or {}).get("counts"),
                                     "kill_rate": (r.get("mutation") or {}).get("kill_rate"),
                                     "original_unchanged": r.get("original_unchanged"),
                                     "project_sha256": r.get("project_sha256"),
                                     "seconds": r.get("seconds")} for r in results}}
    files.write_json(os.path.join(a.out, "summary.json"), summary)


if __name__ == "__main__":
    main()
