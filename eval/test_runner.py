#!/usr/bin/env -S python3 -I
"""Regression tests for the runner, with no Foundry, Halmos or solver:

    python3 -I eval/test_runner.py

Each test reproduces a defect found in review, and fails on the runner as it
was before the fix.
"""

import json
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import files  # noqa: E402
import halmos_per_check  # noqa: E402
import merge  # noqa: E402
import mutate  # noqa: E402
import proc  # noqa: E402
import run as runner  # noqa: E402

proc.become_subreaper()


def write(path, text, mode=None):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write(text)
    if mode:
        os.chmod(path, mode)


class Tmp(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="ausweg-eval-test-")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def p(self, *parts):
        return os.path.join(self.tmp, *parts)


class MutantsStayInTheCopy(Tmp):
    """A mutant applied inside a copied project once changed the original,
    when a dependency was a symlinked directory."""

    def project_with_linked_dependency(self):
        write(self.p("elsewhere", "dep", "A.sol"), "original")
        write(self.p("proj", "src", "V.sol"), "vault")
        os.makedirs(self.p("proj", "lib"))
        os.symlink(self.p("elsewhere", "dep"), self.p("proj", "lib", "dep"))
        write(self.p("gambit", "A.sol"), "mutant")
        return self.p("proj")

    def test_a_mutant_of_a_linked_dependency_leaves_the_original(self):
        proj = self.project_with_linked_dependency()
        before = mutate.tree_hash(proj)
        mutate.copy_project(proj, self.p("copy"))
        self.assertFalse(os.path.islink(self.p("copy", "lib", "dep")))
        mutate.apply(self.p("copy"), {"file": "lib/dep/A.sol", "mutant_path": self.p("gambit", "A.sol")})
        self.assertEqual(files.read_text(self.p("elsewhere", "dep", "A.sol")), "original")
        self.assertEqual(files.read_text(self.p("copy", "lib", "dep", "A.sol")), "mutant")
        self.assertEqual(mutate.tree_hash(proj), before)

    def test_a_mutant_path_that_leaves_the_copy_is_refused(self):
        proj = self.project_with_linked_dependency()
        mutate.copy_project(proj, self.p("copy"))
        write(self.p("outside.sol"), "outside")
        os.symlink(self.p("elsewhere", "dep"), self.p("copy", "lib", "relinked"))
        for rel in ("../outside.sol", self.p("outside.sol"), "lib/relinked/A.sol"):
            with self.assertRaises(RuntimeError, msg=rel):
                mutate.apply(self.p("copy"), {"file": rel, "mutant_path": self.p("gambit", "A.sol")})
        self.assertEqual(files.read_text(self.p("outside.sol")), "outside")
        self.assertEqual(files.read_text(self.p("elsewhere", "dep", "A.sol")), "original")


class ReplayTimeIsReplayWorkOnly(Tmp):
    """The replay budget once ran on the clock from the target's start, so
    building and proving used it up; then each replay was still given at least
    120 seconds."""

    def test_time_outside_replays_is_not_charged(self):
        b = runner.ReplayBudget(30)
        time.sleep(1.5)
        self.assertEqual(b.left(), 30)

    def test_a_replay_gets_only_what_is_left_and_nothing_after(self):
        b = runner.ReplayBudget(runner.MIN_START + 1)
        t0 = time.monotonic()
        r, ran = b.step(lambda deadline: proc.run(
            ["sleep", "60"], self.tmp, dict(os.environ), deadline,
            self.p("out"), self.p("err")))
        self.assertTrue(ran)
        self.assertEqual(r["status"], "stopped at the deadline")
        self.assertLess(time.monotonic() - t0, runner.MIN_START + 5)
        _, ran = b.step(lambda deadline: self.fail("started with nothing left"))
        self.assertFalse(ran)


class Erc7540CounterexamplesSayTheyHaveNoReplay(unittest.TestCase):
    """A counterexample to an ERC-7540 exit check was reported as "not an exit
    property". It is one; it stays unconfirmed because the runner has no
    ERC-7540 replay."""

    def test_the_reason_names_the_missing_replay(self):
        exits = ["check_request", "check_fulfil", "check_mature", "check_claim_redeem", "check_claim_withdraw",
                 "check_stable_redeem", "check_fair_deposit"]
        out = runner.confirm(None, None, None, None, None, exits + ["check_keeps_deposit"], None, None, "target")
        for c in exits:
            self.assertEqual(out[c], {"confirmed": False,
                                      "why": "No ERC-7540 replay implemented; counterexample remains unconfirmed."})
        self.assertIn("not an exit property", out["check_keeps_deposit"]["why"])


class FailedRunsAreNotSurvivors(unittest.TestCase):
    """A mutant run that ended with an error and no report was labelled
    survived."""

    def result(self, report, checks=(), status="exited", returncode=0, asked=("check_a", "check_b")):
        return {"report": report, "checks": list(checks), "asked": list(asked),
                "run": {"status": status, "returncode": returncode, "stderr": os.devnull}}

    @staticmethod
    def report(**verdicts):
        return {"reports": [{"checks": [{"name": n, "verdict": v} for n, v in verdicts.items()]}]}

    def test_no_report_is_inconclusive(self):
        r = self.result(None, returncode=1)
        self.assertEqual(runner.mutant_class(r, runner.check_classes(r), r["asked"]), "inconclusive")

    def test_a_check_with_no_result_is_inconclusive(self):
        r = self.result(self.report(check_a="proved"))
        self.assertEqual(runner.mutant_class(r, runner.check_classes(r), r["asked"]), "inconclusive")

    def test_an_unfinished_check_is_inconclusive(self):
        r = self.result(self.report(check_a="proved", check_b="proved"),
                        checks=[{"check": "check_b", "outcome": "unfinished: stopped at its limit"}])
        self.assertEqual(runner.mutant_class(r, runner.check_classes(r), r["asked"]), "inconclusive")

    def test_a_stopped_run_is_inconclusive(self):
        r = self.result(None, status="stopped at the deadline")
        classes = runner.check_classes(r)
        self.assertEqual(classes, {"check_a": "unfinished", "check_b": "unfinished"})
        self.assertEqual(runner.mutant_class(r, classes, r["asked"]), "inconclusive")

    def test_every_check_proved_survives(self):
        r = self.result(self.report(check_a="proved", check_b="proved"))
        self.assertEqual(runner.mutant_class(r, runner.check_classes(r), r["asked"]), "survived")

    def test_a_counterexample_is_a_claimed_kill(self):
        r = self.result(self.report(check_a="counterexample"))
        self.assertEqual(runner.mutant_class(r, runner.check_classes(r), r["asked"]), "counterexample")


class BudgetsAreUpperBounds(Tmp):
    """With one second left, a mutant build was still given 1,800 seconds,
    and the proof after it a negative budget."""

    def test_no_build_starts_with_too_little_left(self):
        class NoRun:
            def cmd(self, *a, **k):
                raise AssertionError("a build started with too little time left")
        self.assertIsNone(runner.build(NoRun(), self.tmp, time.monotonic() + 1, self.tmp, "build"))

    def test_a_command_ends_by_its_window(self):
        w = runner.Window(2)
        t0 = time.monotonic()
        r = proc.run(["sleep", "60"], self.tmp, dict(os.environ), w.end, self.p("out"), self.p("err"))
        self.assertEqual(r["status"], "stopped at the deadline")
        self.assertLess(time.monotonic() - t0, 6)
        self.assertFalse(w.can_start())


class ToolsAreTheConfiguredOnes(Tmp):
    """ausweg finds z3 and yices on PATH, or takes them from AUSWEG_SMT_*
    variables, so a run could use other solvers than the ones checked."""

    def run_and_env(self):
        for name in ("z3", "yices-smt2", "forge", "halmos", "bitwuzla", "cvc5"):
            write(self.p("decoy", name), "#!/bin/sh\necho decoy\n", 0o755)
            write(self.p("frozen", name), f"#!/bin/sh\necho frozen {name}\n", 0o755)
        cfg = {"tools": {"forge": {"bin": self.p("frozen", "forge")}, "halmos": {"bin": self.p("frozen", "halmos")},
                         "z3": {"bin": self.p("frozen", "z3")}, "yices": {"bin": self.p("frozen", "yices-smt2")},
                         "bitwuzla": {"bin": self.p("frozen", "bitwuzla")}, "cvc5": {"bin": self.p("frozen", "cvc5")}}}
        env = {"PATH": self.p("decoy") + os.pathsep + os.environ["PATH"], "AUSWEG_SMT_SOLVER": self.p("decoy", "z3"),
               "AUSWEG_SMT_FALLBACK": "decoy", "AUSWEG_SMT_CHECKER": "decoy", "HOME": os.environ.get("HOME", "/")}
        with mock.patch.dict(os.environ, env, clear=True):
            run = runner.Run(cfg, self.p("out"))
            return run, run.env(exec_log=self.p("exec.log"))

    def test_commands_reach_only_the_configured_tools(self):
        run, e = self.run_and_env()
        self.assertFalse([k for k in e if k.startswith("AUSWEG_")])
        self.assertEqual(e["PATH"].split(os.pathsep)[0], run.bin)
        got = subprocess.run(["sh", "-c", "z3; yices-smt2; forge; halmos"], env=e, capture_output=True, text=True)
        self.assertEqual(got.stdout.split("\n")[:4], ["frozen z3", "frozen yices-smt2", "frozen forge", "frozen halmos"])
        used = files.read_text(self.p("exec.log")).split()
        self.assertEqual(used, [os.path.realpath(self.p("frozen", n)) for n in ("z3", "yices-smt2", "forge", "halmos")])

    def test_the_baselines_bitwuzla_and_cvc5_are_on_no_commands_path(self):
        """ausweg looks for cvc5 and bitwuzla on PATH when z3 or yices is
        missing there: its runs must not find the baselines' solvers."""
        run, e = self.run_and_env()
        self.assertNotIn(run.solvers, e["PATH"].split(os.pathsep))
        for name in ("bitwuzla", "cvc5"):
            found = shutil.which(name, path=e["PATH"])
            self.assertFalse(found and os.path.realpath(found) == os.path.realpath(self.p("frozen", name)), found)
        got = subprocess.run([run.shim("bitwuzla")[1]], env=e, capture_output=True, text=True)
        self.assertEqual(got.stdout, "frozen bitwuzla\n")
        self.assertEqual(files.read_text(self.p("exec.log")).split(), [os.path.realpath(self.p("frozen", "bitwuzla"))])


class StoppedMeansStopped(Tmp):
    """Everything a command started is stopped with it, even a process that
    left the command's session."""

    def test_a_process_that_left_the_session_is_stopped(self):
        marker = f"ausweg-eval-marker-{os.getpid()}"
        pidfile = self.p("escaped.pid")
        # The escaped process writes its pid, then sleeps through the deadline.
        escaped = "import os, sys, time; open(sys.argv[1], 'w').write(str(os.getpid())); time.sleep(60)"
        script = textwrap.dedent(f"""
            import os, sys, time
            if os.fork() == 0:
                os.setsid()
                if os.fork() == 0:
                    os.execv(sys.executable, [sys.executable, "-c", {escaped!r}, {pidfile!r}, {marker!r}])
                os._exit(0)
            time.sleep(60)
        """)
        r = proc.run([sys.executable, "-c", script], self.tmp, dict(os.environ), time.monotonic() + 3,
                     self.p("out"), self.p("err"))
        self.assertEqual(r["status"], "stopped at the deadline")
        pid = int(files.read_text(pidfile))
        self.assertTrue(r["left_running_and_stopped"], "the escaped process was running at the deadline")
        self.assertIsNone(proc._stat(pid), "the escaped process is gone")
        self.assertEqual(r["still_running_after_stop"], [])
        left = []
        for pid in os.listdir("/proc"):
            try:
                if pid.isdigit() and marker in files.read_text(f"/proc/{pid}/cmdline", errors="replace"):
                    left.append(pid)
            except OSError:
                pass
        self.assertEqual(left, [])


class ForgeQueriesAreBounded(Tmp):
    """forge config and forge remappings run under the mutation budget."""

    def cmd(self, deadline):
        def run_cmd(argv, cwd, tag, label):
            return proc.run(argv, cwd, dict(os.environ), deadline, self.p(tag + ".out"), self.p(tag + ".err"))
        return run_cmd

    def test_a_forge_that_hangs_is_stopped_at_the_deadline(self):
        forge = self.p("forge")
        write(forge, "#!/bin/sh\nexec sleep 60\n", 0o755)
        start = time.monotonic()
        found = mutate.solc_for(self.tmp, forge, self.cmd(start + 2))
        self.assertEqual(found, {"error": "forge config was stopped at the end of the mutation budget"})
        self.assertLess(time.monotonic() - start, 8)
        self.assertEqual(proc.descendants(os.getpid()), [])

    def test_no_query_starts_without_time_and_answers_are_read(self):
        self.assertIn("error", mutate.solc_for(self.tmp, "forge", lambda argv, cwd, tag, label: None))
        forge = self.p("forge")
        write(forge, "#!/bin/sh\ncase $1 in\nconfig) echo '{\"solc\": \"/opt/solc-0.8.38\"}';;\n"
                     "remappings) printf 'a/=lib/a/\\nb/=lib/b/\\n';;\nesac\n", 0o755)
        found = mutate.solc_for(self.tmp, forge, self.cmd(time.monotonic() + 30))
        self.assertEqual(found, {"path": "/opt/solc-0.8.38", "version": "/opt/solc-0.8.38",
                                 "remappings": ["a/=lib/a/", "b/=lib/b/"]})


class SolcIsWhereForgeInstallsIt(Tmp):
    """On a machine with ~/.local/share and no ~/.svm, forge installs solc in
    ~/.local/share/svm. The runner looked only in ~/.svm, so there it skipped
    every target's mutants."""

    def solc_for(self, *dirs):
        home = self.p("home")
        for d in dirs:
            os.makedirs(os.path.join(home, d), exist_ok=True)
        forge = self.p("forge")
        write(forge, "#!/bin/sh\n[ \"$1\" = config ] && echo '{\"solc\": \"0.8.38\"}'\nexit 0\n", 0o755)

        def run_cmd(argv, cwd, tag, label):
            return proc.run(argv, cwd, dict(os.environ), time.monotonic() + 30,
                            self.p(tag + ".out"), self.p(tag + ".err"))
        with mock.patch.dict(os.environ, {"HOME": home}):
            return mutate.solc_for(self.tmp, forge, run_cmd)

    def test_without_a_home_svm_it_is_under_local_share(self):
        solc = os.path.join(".local", "share", "svm", "0.8.38", "solc-0.8.38")
        write(self.p("home", solc), "")
        self.assertEqual(self.solc_for().get("path"), self.p("home", solc))

    def test_an_existing_home_svm_comes_first(self):
        solc = os.path.join(".svm", "0.8.38", "solc-0.8.38")
        write(self.p("home", solc), "")
        self.assertEqual(self.solc_for(os.path.join(".local", "share")).get("path"), self.p("home", solc))

    def test_a_missing_solc_names_where_it_was_looked_for(self):
        found = self.solc_for(os.path.join(".local", "share"))
        self.assertEqual(found, {"error": "forge's solc 0.8.38 is not installed in "
                                          + self.p("home", ".local", "share", "svm")})


class TheWrapperPinsTheBranchTimeout(Tmp):
    """Every Halmos process gets the runner's branch timeout, and each
    check's record keeps Halmos's path count."""

    def wrapper(self, *extra):
        write(self.p("work", "test", "generated", "V.proof.t.sol"),
              "contract VProof {\n  function check_a() public {}\n}\n")
        write(self.p("halmos"), textwrap.dedent(f"""\
            #!{sys.executable}
            import json, os, sys
            a = sys.argv[1:]
            with open({self.p("argv")!r}, "a") as f:
                f.write(json.dumps(a) + "\\n")
            with open(os.environ["EVAL_EXEC_LOG"], "a") as f:
                f.write("/x/solver\\n/x/solver\\n")
            result = {{"name": "check_a()", "exitcode": 0, "num_models": 0, "models": [],
                       "num_paths": [7, 7, 0], "time": [0.1, 0.1, 0], "num_bounded_loops": 0}}
            with open(a[a.index("--json-output") + 1], "w") as f:
                json.dump({{"exitcode": 0, "test_results": {{"test/generated/V.proof.t.sol:VProof": [result]}}}}, f)
            """), 0o755)
        write(self.p("exec.log"), "/x/before\n")
        env = dict(os.environ, EVAL_REAL_HALMOS=self.p("halmos"), EVAL_CHECK_RECORD=self.p("checks.jsonl"),
                   EVAL_LOG_DIR=self.p("logs"), EVAL_BRANCH_TIMEOUT="1ms", EVAL_EXEC_LOG=self.p("exec.log"))
        return subprocess.run([sys.executable, "-I", halmos_per_check.__file__, "--root", self.p("work"),
                               "--contract", "VProof", "--json-output", self.p("merged.json"), *extra],
                              cwd=self.p("work"), env=env, capture_output=True, text=True, timeout=60)

    def test_each_check_runs_with_the_branch_timeout_and_keeps_its_path_count(self):
        r = self.wrapper()
        self.assertEqual(r.returncode, 0, r.stderr)
        argv = [json.loads(x) for x in files.read_lines(self.p("argv"))]
        self.assertEqual(len(argv), 1)
        i = argv[0].index("--solver-timeout-branching")
        self.assertEqual(argv[0][i + 1], "1ms")
        rec = json.loads(files.read_lines(self.p("checks.jsonl"))[0])
        self.assertEqual((rec["outcome"], rec["num_paths"]), ("completed", [7, 7, 0]))

    def test_each_record_keeps_auswegs_arguments_the_loop_bound_count_and_the_solver_runs(self):
        """The solver baselines run ausweg's Halmos arguments again, read a
        check's verdict from its record as ausweg reads Halmos's, and count
        the solver runs of that check alone."""
        r = self.wrapper("--loop", "2")
        self.assertEqual(r.returncode, 0, r.stderr)
        rec = json.loads(files.read_lines(self.p("checks.jsonl"))[0])
        self.assertEqual(rec["args"], ["--root", self.p("work"), "--contract", "VProof", "--loop", "2"])
        self.assertEqual((rec["halmos_exitcodes"], rec["num_bounded_loops"]), ([0], [0]))
        self.assertEqual(rec["executables_used"], {"/x/solver": 2})

    def test_a_second_branch_timeout_is_refused(self):
        r = self.wrapper("--solver-timeout-branching", "5ms")
        self.assertNotEqual(r.returncode, 0)
        self.assertFalse(os.path.exists(self.p("argv")), "Halmos never ran")


class SolverBaselinesRunAuswegsProofAgain(Tmp):
    """Halmos's own solvers run every check of ausweg's proof again, with the
    arguments ausweg gave Halmos and each solver in place of `ausweg smt`, as
    Halmos's `--solver` would run it, under the same limits and a budget of
    their own. A check one solver proved and the other refuted is flagged."""

    ARGS = ["--root", ".", "--contract", "VProof", "--solver-command", "/opt/ausweg-eval/bin/ausweg smt",
            "--solver-timeout-assertion", "65s", "--loop", "2"]
    CHECKS = ["check_a", "check_b", "check_c"]
    AUSWEG = {"check_a": "proved", "check_b": "proved", "check_c": "counterexample"}

    def setUp(self):
        super().setUp()
        write(self.p("work", "test", "generated", "V.proof.t.sol"),
              "contract VProof {\n" + "".join(f"  function {c}() public {{}}\n" for c in self.CHECKS) + "}\n")
        for name in ("forge", "z3", "yices-smt2", "bitwuzla", "cvc5"):
            write(self.p("frozen", name), "#!/bin/sh\nexit 0\n", 0o755)
        # Runs the solver command once, then answers the check as plan.json
        # says for that solver's file name: [exit code, loop-bound count].
        write(self.p("frozen", "halmos"), textwrap.dedent(f"""\
            #!{sys.executable}
            import json, os, shlex, subprocess, sys, time
            a = sys.argv[1:]
            with open({self.p("argv.jsonl")!r}, "a") as f:
                f.write(json.dumps(a) + "\\n")
            command = shlex.split(a[a.index("--solver-command") + 1])
            subprocess.run(command + ["query.smt2"])
            plan = json.load(open({self.p("plan.json")!r})).get(os.path.basename(command[0]), {{}})
            time.sleep(plan.get("sleep", 0))
            check = a[a.index("--match-test") + 1][1:-2]
            code, bounded = plan.get(check, [0, 0])
            result = {{"name": check + "()", "exitcode": code, "num_models": 0, "models": [],
                       "num_paths": [3, 3, 0], "time": [0.1, 0.1, 0], "num_bounded_loops": bounded}}
            with open(a[a.index("--json-output") + 1], "w") as f:
                json.dump({{"exitcode": code, "test_results": {{"test/generated/V.proof.t.sol:VProof": [result]}}}}, f)
            """), 0o755)
        frozen = files.read_toml(os.path.join(runner.HERE, "config.toml"))
        self.limits = frozen["limits"]
        cfg = {"tools": {key: {"bin": self.p("frozen", name)} for key, name in (
                   ("forge", "forge"), ("halmos", "halmos"), ("z3", "z3"), ("yices", "yices-smt2"),
                   ("bitwuzla", "bitwuzla"), ("cvc5", "cvc5"))},
               "baselines": frozen["baselines"]}
        self.run = runner.Run(cfg, self.p("out"))
        self.plan({})

    def plan(self, plan):
        write(self.p("plan.json"), json.dumps(plan))

    def baselines(self, args=ARGS, hooks=None, **limits):
        clean = {"checks": [{"check": "check_a", "args": args}] if args else [], "asked": self.CHECKS}
        return runner.solver_baselines(self.run, self.p("work"), clean, self.AUSWEG, dict(self.limits, **limits),
                                       self.p("logs"), hooks or {})

    def argv(self):
        return [json.loads(x) for x in files.read_lines(self.p("argv.jsonl"))]

    def test_each_solver_runs_every_check_as_halmos_would_run_it(self):
        b = self.baselines()
        want = [shlex.join([self.run.shim(s["tool"])[1], *s["arguments"]])
                for s in self.run.cfg["baselines"]["solvers"]]
        argv = self.argv()
        self.assertEqual([a[a.index("--solver-command") + 1] for a in argv], [w for w in want for _ in self.CHECKS])
        self.assertEqual([a[a.index("--match-test") + 1] for a in argv[:3]], [f"^{c}\\(" for c in self.CHECKS])
        for a in argv:
            self.assertNotIn("/opt/ausweg-eval/bin/ausweg smt", a)
            self.assertEqual([a[a.index(f) + 1] for f in ("--root", "--contract", "--loop",
                                                          "--solver-timeout-assertion", "--solver-timeout-branching")],
                             [".", "VProof", "2", f"{self.limits['query_seconds']}s",
                              f"{self.limits['branch_query_ms']}ms"])
        bw = b["solvers"]["bitwuzla"]
        real = os.path.realpath(self.p("frozen", "bitwuzla"))
        self.assertEqual(bw["binary"], {"path": real, "sha256": files.sha256(real)})
        self.assertEqual((bw["arguments"], bw["run"]["executables_used"][real]), (["--produce-models"], 3))
        self.assertEqual(bw["solver_runs"], dict.fromkeys(self.CHECKS, 1))

    def test_verdicts_are_read_as_ausweg_reads_them_and_disagreements_flagged(self):
        self.plan({"yices-smt2": {"check_c": [1, 0]},
                   "bitwuzla": {"check_a": [1, 0], "check_b": [2, 0]},
                   "cvc5": {"check_a": [0, 1], "check_b": [4, 0], "check_c": [5, 0]}})
        b = self.baselines()
        self.assertEqual({n: s["checks"] for n, s in b["solvers"].items()}, {
            "yices": {"check_a": "proved", "check_b": "proved", "check_c": "counterexample"},
            "bitwuzla": {"check_a": "counterexample", "check_b": "timeout", "check_c": "proved"},
            "cvc5-int": {"check_a": "incomplete", "check_b": "vacuous", "check_c": "error"}})
        self.assertEqual(b["disagreements"], [
            {"check": "check_a", "solver": "bitwuzla", "by_ausweg_smt": "proved", "by_solver": "counterexample"},
            {"check": "check_c", "solver": "bitwuzla", "by_ausweg_smt": "counterexample", "by_solver": "proved"}])

    def test_a_solver_stops_at_its_own_budget_and_the_next_one_gets_its_own(self):
        self.plan({"bitwuzla": {"sleep": 30}})
        b = self.baselines(solver_seconds=runner.WRAPPER_RESERVE + 3)
        bw = b["solvers"]["bitwuzla"]
        self.assertEqual(bw["checks"], dict.fromkeys(self.CHECKS, "unfinished"))
        self.assertLess(bw["run"]["seconds"], runner.WRAPPER_RESERVE + 3)
        self.assertEqual(bw["wrapper_checks"][0]["left_running_and_stopped"][0], "halmos")
        self.assertEqual(bw["run"]["still_running_after_stop"], [])
        self.assertEqual(b["solvers"]["cvc5-int"]["checks"], dict.fromkeys(self.CHECKS, "proved"))

    def test_each_check_stops_at_the_check_cap(self):
        self.plan({"bitwuzla": {"sleep": 30}})
        b = self.baselines(check_seconds=1)
        bw = b["solvers"]["bitwuzla"]
        self.assertEqual(bw["checks"], dict.fromkeys(self.CHECKS, "unfinished"))
        self.assertEqual([r["limit_seconds"] for r in bw["wrapper_checks"]], [1, 1, 1])
        self.assertLess(bw["run"]["seconds"], 10)

    def test_no_baseline_without_auswegs_arguments_to_run_again(self):
        self.assertIn("not_run", self.baselines(args=None))
        b = self.baselines(args=["--root", ".", "--contract", "VProof", "--solver", "yices"])
        self.assertEqual([("not_run" in s) for s in b["solvers"].values()], [True, True, True])
        self.assertFalse(os.path.exists(self.p("argv.jsonl")), "Halmos never ran")

    def test_the_smoke_test_can_run_a_subset_of_the_solvers_and_checks(self):
        b = self.baselines(hooks={"baseline_solvers": ["yices"], "baseline_checks": ["check_b"]})
        self.assertEqual([n for n, s in b["solvers"].items() if "not_run" not in s], ["yices"])
        self.assertEqual(b["solvers"]["yices"]["checks"], {"check_b": "proved"})
        self.assertEqual([a[a.index("--match-test") + 1] for a in self.argv()], ["^check_b\\("])


class BaselineVerdictsAreAusweg(unittest.TestCase):
    """A baseline's verdicts must mean what ausweg's mean."""

    def test_halmos_results_read_by_auswegs_rule(self):
        # The results of prove.rs's own tests of parse_results, then the edges
        # of its types: a count must be a JSON integer, an exit code too.
        cases = [({"exitcode": 1, "num_bounded_loops": 0}, "counterexample"),
                 ({"exitcode": 0, "num_bounded_loops": 0}, "proved"),
                 ({"exitcode": 2}, "timeout"),
                 ({"exitcode": 0, "num_bounded_loops": 1}, "incomplete"),
                 ({"exitcode": 0, "num_paths": [1, 1, 0]}, "incomplete"),
                 ({"exitcode": 0, "num_bounded_loops": "two"}, "incomplete"),
                 ({"exitcode": 1, "num_bounded_loops": 3}, "counterexample"),
                 ({"exitcode": 4, "num_bounded_loops": 0}, "vacuous"),
                 ({"exitcode": 0, "num_bounded_loops": None}, "incomplete"),
                 ({"exitcode": 0, "num_bounded_loops": False}, "incomplete"),
                 ({"exitcode": 0, "num_bounded_loops": 0.0}, "incomplete"),
                 ({"exitcode": 0, "num_bounded_loops": -1}, "incomplete"),
                 ({"exitcode": 3}, "error"), ({"exitcode": 5}, "error"), ({"exitcode": 124}, "error"),
                 ({}, "error"), ({"exitcode": False, "num_bounded_loops": 0}, "error"),
                 ({"exitcode": 0.0, "num_bounded_loops": 0}, "error")]
        self.assertEqual([runner.halmos_class(e) for e, _ in cases], [c for _, c in cases])

    def test_a_check_with_no_finished_result_is_never_proved(self):
        def rec(check, outcome, codes=(0,), bounded=(0,)):
            return {"check": check, "outcome": outcome, "halmos_exitcodes": list(codes),
                    "num_bounded_loops": list(bounded)}
        records = [rec("a", "unfinished: stopped at its limit"), rec("b", "not started: the target's budget was spent"),
                   rec("c", "Halmos wrote no result"), rec("d", "completed", (0, 0), (0, 0)), rec("e", "completed")]
        asked = ["a", "b", "c", "d", "e", "f"]
        self.assertEqual(runner.baseline_classes(records, asked, stopped=False),
                         {"a": "unfinished", "b": "unfinished", "c": "error", "d": "error", "e": "proved", "f": "error"})
        self.assertEqual(runner.baseline_classes(records[:1], ["a", "f"], stopped=True),
                         {"a": "unfinished", "f": "unfinished"})

    def test_the_solver_command_is_replaced_only_when_unambiguous(self):
        args = ["--root", ".", "--solver-command", "a smt", "--solver-timeout-assertion", "65s", "--loop", "2"]
        self.assertEqual(runner.with_solver(args, "b x", 60),
                         ["--root", ".", "--solver-command", "b x", "--solver-timeout-assertion", "60s", "--loop", "2"])
        self.assertEqual(runner.with_solver(["--solver-command", "a"], "b", 5),
                         ["--solver-command", "b", "--solver-timeout-assertion", "5s"])
        for bad in (["--root", "."], ["--solver-command"], ["--solver-command", "a", "--solver-command", "c"],
                    ["--solver-command", "a", "--solver", "z3"], ["--solver-command=a"],
                    ["--solver-command", "--loop", "2"], ["--solver-command", "a", "--solver-timeout-assertion"],
                    ["--solver-command", "a", "--solver-timeout-assertion=65s"],
                    ["--solver-command", "a", "--solver-timeout-assertion", "1s", "--solver-timeout-assertion", "2s"]):
            self.assertIsNone(runner.with_solver(bad, "b", 60), bad)

    def test_a_solver_must_be_the_binary_halmos_runs_with_halmos_arguments(self):
        cfg = {"tools": {"bitwuzla": {"bin": "/x/solvers/bitwuzla", "sha256": "ab" * 32}},
               "baselines": {"solvers": [{"name": "bitwuzla", "tool": "bitwuzla", "arguments": ["--produce-models"]}]}}
        halmos = {"name": "bitwuzla-0.8.1", "binary": "bitwuzla", "arguments": ["--produce-models"]}
        self.assertEqual(runner.solver_problems(cfg, {"bitwuzla": halmos}), [])
        for table in ({"bitwuzla": dict(halmos, arguments=[])}, {"bitwuzla": dict(halmos, binary="bitwuzla-abs")},
                      {}, None):
            self.assertEqual(len(runner.solver_problems(cfg, table)), 1, table)
        self.assertEqual(runner.pin_problems(cfg, {"bitwuzla": {"sha256": "ab" * 32}}), [])
        self.assertEqual(len(runner.pin_problems(cfg, {"bitwuzla": {"sha256": "cd" * 32}})), 1)
        self.assertEqual(len(runner.pin_problems(cfg, {})), 1)


class TheRunnerReadsWhatToolsWrote(Tmp):
    """The files ausweg and forge write, read where the runner reads them."""

    def setUp(self):
        super().setUp()
        write(self.p("work", "test", "generated", "V.proof.t.sol"),
              "contract VProof {\n  function check_a() public {}\n  function check_b(uint x) public {}\n}\n")

    def test_the_asked_checks_are_the_proof_files(self):
        self.assertEqual(runner.asked_checks(self.p("work"), None), ["check_a", "check_b"])
        self.assertEqual(runner.asked_checks(self.p("work"), ["check_b"]), ["check_b"])

    def test_the_per_check_wrapper_finds_the_same_checks(self):
        path, names = halmos_per_check.proof_checks(self.p("work"), "VProof")
        self.assertEqual((path, names), (self.p("work", "test", "generated", "V.proof.t.sol"), ["check_a", "check_b"]))

    def test_the_mutation_selection_reads_forges_asts(self):
        ast = {"absolutePath": "src/V.sol", "nodeType": "SourceUnit"}
        write(self.p("work", "out", "V.sol", "V.json"), json.dumps({"ast": ast}))
        write(self.p("work", "out", "build-info", "x.json"), "[1]")
        self.assertEqual(mutate._asts(self.p("work")), {"src/V.sol": ast})


class ResumeAndShard(Tmp):
    def setUp(self):
        super().setUp()
        write(self.p("config.toml"), '[runner]\nallow_version_mismatch = false\n')
        write(self.p("proj", "src", "V.sol"), "contract V {}\n")
        self.targets()
        self.ran = []
        self.tools = {name: {"path": f"/opt/ausweg-eval/bin/{name}", "sha256": "ab" * 32, "reported": None}
                      for name in runner.TOOLS}

    def targets(self, contract="src/V.sol"):
        write(self.p("targets.toml"), "".join(
            f'[[target]]\nid = "t{i}"\nproject = "{self.p("proj")}"\ncontract = "{contract}"\n\n' for i in range(5)))

    def fake_target(self, run, t, project_hash):
        self.ran.append(t["id"])
        if t["id"] == getattr(self, "crash_on", None):
            os.makedirs(os.path.join(run.out, t["id"]), exist_ok=True)
            raise KeyboardInterrupt
        if t["id"] == getattr(self, "disagree_on", None):
            d = {"check": "check_x", "solver": "bitwuzla", "by_ausweg_smt": "proved", "by_solver": "counterexample"}
            solver = {"checks": {"check_x": "counterexample"}, "counts": {"counterexample": 1}, "run": {"seconds": 1}}
            return {"id": t["id"], "class": "proved", "baselines": {"solvers": {"bitwuzla": solver},
                                                                     "disagreements": [d]}}
        return {"id": t["id"], "class": "proved", "baselines": {"not_run": "ausweg does not support the target"}}

    def main(self, *extra, out="out"):
        argv = ["--config", self.p("config.toml"), "--targets", self.p("targets.toml"), "--out", self.p(out), *extra]
        with mock.patch.object(runner, "Run", lambda cfg, out: mock.Mock(out=out, base_env={})), \
                mock.patch.object(runner, "tool_versions", lambda run: (self.tools, [])), \
                mock.patch.object(runner, "run_target", self.fake_target):
            runner.main(argv)

    def test_a_shard_is_every_nth_target(self):
        targets = files.read_toml(self.p("targets.toml"))["target"]
        self.assertEqual([t["id"] for t in runner.shard_of(targets, "2/3")], ["t1", "t4"])
        self.assertEqual(sum(len(runner.shard_of(targets, f"{k}/3")) for k in (1, 2, 3)), 5)

    def test_resume_skips_finished_targets_and_redoes_an_interrupted_one(self):
        self.crash_on = "t2"
        with self.assertRaises(KeyboardInterrupt):
            self.main()
        self.assertEqual(self.ran, ["t0", "t1", "t2"])
        self.assertFalse(os.path.exists(self.p("out", "t2", "result.json")))
        self.crash_on, self.ran = None, []
        self.main("--resume")
        self.assertEqual(self.ran, ["t2", "t3", "t4"])
        summary = files.read_json(self.p("out", "summary.json"))
        self.assertEqual(sorted(summary["targets"]), ["t0", "t1", "t2", "t3", "t4"])

    def test_a_directory_with_a_run_needs_resume(self):
        self.main()
        with self.assertRaises(SystemExit):
            self.main()

    def test_resume_refuses_changed_settings(self):
        self.main()
        write(self.p("config.toml"), '[runner]\nallow_version_mismatch = true\n')
        with self.assertRaises(SystemExit):
            self.main("--resume")

    def test_resume_refuses_a_target_whose_sources_changed(self):
        self.main()
        write(self.p("proj", "src", "V.sol"), "contract V { uint x; }\n")
        with self.assertRaises(SystemExit) as e:
            self.main("--resume")
        self.assertIn("t0", str(e.exception))
        self.assertEqual(len(os.listdir(self.p("out", "manifests"))), 1)

    def test_resume_refuses_another_shard(self):
        self.main("--shard", "1/2")
        with self.assertRaises(SystemExit):
            self.main("--shard", "2/2", "--resume")

    def merge(self, *dirs):
        merge.main(["--targets", self.p("targets.toml"), "--out", self.p("merged"), *[self.p(d) for d in dirs]])

    def test_the_shards_merge_into_one_evaluation(self):
        self.main("--shard", "1/2", out="s1")
        self.main("--shard", "2/2", out="s2")
        self.merge("s1", "s2")
        summary = files.read_json(self.p("merged", "summary.json"))
        self.assertEqual(sorted(summary["targets"]), ["t0", "t1", "t2", "t3", "t4"])

    def test_the_summaries_list_every_disagreement_with_a_solver(self):
        self.disagree_on = "t3"
        self.main("--shard", "1/2", out="s1")
        self.main("--shard", "2/2", out="s2")
        self.merge("s1", "s2")
        merged = files.read_json(self.p("merged", "summary.json"))
        want = {"check": "check_x", "solver": "bitwuzla", "by_ausweg_smt": "proved", "by_solver": "counterexample"}
        self.assertEqual(merged["disagreements"], [dict(target="t3", **want)])
        shard = files.read_json(self.p("s2", "summary.json"))["targets"]
        self.assertEqual(shard["t3"]["baselines"]["disagreements"], [want])
        self.assertEqual(shard["t1"]["baselines"], {"not_run": "ausweg does not support the target"})

    def test_a_merge_refuses_another_targets_file(self):
        self.main("--shard", "1/2", out="s1")
        self.main("--shard", "2/2", out="s2")
        self.targets(contract="src/W.sol")
        with self.assertRaises(SystemExit):
            self.merge("s1", "s2")

    def test_a_merge_refuses_a_missing_shard_or_a_shard_with_other_settings(self):
        self.main("--shard", "1/2", out="s1")
        with self.assertRaises(SystemExit):
            self.merge("s1")
        write(self.p("config.toml"), '[runner]\nallow_version_mismatch = true\n')
        self.main("--shard", "2/2", out="s2")
        with self.assertRaises(SystemExit):
            self.merge("s1", "s2")

    def test_a_merge_refuses_binaries_that_differ_or_were_not_recorded(self):
        """Gambit reports no version, so shards that ran two different Gambit
        binaries passed the version check and merged. So did shards with no
        hash or no record of a tool, the first shard included."""
        tools = self.tools

        def shards(prefix, gambit):
            self.tools = {n: t for n, t in tools.items() if n != "gambit"}
            if gambit:
                self.tools["gambit"] = gambit
            self.main("--shard", "1/2", out=prefix + "1")
            self.main("--shard", "2/2", out=prefix + "2")
        shards("same", tools["gambit"])
        shards("other", dict(tools["gambit"], sha256="f96889c8" * 8))
        shards("unhashed", dict(tools["gambit"], sha256=None))
        shards("unrecorded", None)
        self.merge("same1", "same2")
        self.merge("other1", "other2")
        for pair in (("same1", "other2"), ("other1", "same2"), ("unhashed1", "unhashed2"),
                     ("unrecorded1", "unrecorded2"), ("unrecorded1", "same2"), ("same1", "unrecorded2")):
            with self.subTest(pair=pair):
                with self.assertRaises(SystemExit) as e:
                    self.merge(*pair)
                self.assertIn("gambit", str(e.exception))


if __name__ == "__main__":
    unittest.main(verbosity=2)
