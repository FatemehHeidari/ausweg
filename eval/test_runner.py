#!/usr/bin/env -S python3 -I
"""Regression tests for the runner, with no Foundry, Halmos or solver:

    python3 -I eval/test_runner.py

Each test reproduces a defect found in review, and fails on the runner as it
was before the fix.
"""

import json
import os
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

    def test_commands_reach_only_the_configured_tools(self):
        for name in ("z3", "yices-smt2", "forge", "halmos"):
            write(self.p("decoy", name), "#!/bin/sh\necho decoy\n", 0o755)
            write(self.p("frozen", name), f"#!/bin/sh\necho frozen {name}\n", 0o755)
        cfg = {"tools": {"forge": {"bin": self.p("frozen", "forge")}, "halmos": {"bin": self.p("frozen", "halmos")},
                         "z3": {"bin": self.p("frozen", "z3")}, "yices": {"bin": self.p("frozen", "yices-smt2")}}}
        env = {"PATH": self.p("decoy") + os.pathsep + os.environ["PATH"], "AUSWEG_SMT_SOLVER": self.p("decoy", "z3"),
               "AUSWEG_SMT_FALLBACK": "decoy", "AUSWEG_SMT_CHECKER": "decoy", "HOME": os.environ.get("HOME", "/")}
        with mock.patch.dict(os.environ, env, clear=True):
            run = runner.Run(cfg, self.p("out"))
            e = run.env(exec_log=self.p("exec.log"))
        self.assertFalse([k for k in e if k.startswith("AUSWEG_")])
        self.assertEqual(e["PATH"].split(os.pathsep)[0], run.bin)
        got = subprocess.run(["sh", "-c", "z3; yices-smt2; forge; halmos"], env=e, capture_output=True, text=True)
        self.assertEqual(got.stdout.split("\n")[:4], ["frozen z3", "frozen yices-smt2", "frozen forge", "frozen halmos"])
        used = files.read_text(self.p("exec.log")).split()
        self.assertEqual(used, [os.path.realpath(self.p("frozen", n)) for n in ("z3", "yices-smt2", "forge", "halmos")])


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
            import json, sys
            a = sys.argv[1:]
            with open({self.p("argv")!r}, "a") as f:
                f.write(json.dumps(a) + "\\n")
            result = {{"name": "check_a()", "exitcode": 0, "num_models": 0, "models": [],
                       "num_paths": [7, 7, 0], "time": [0.1, 0.1, 0], "num_bounded_loops": 0}}
            with open(a[a.index("--json-output") + 1], "w") as f:
                json.dump({{"exitcode": 0, "test_results": {{"test/generated/V.proof.t.sol:VProof": [result]}}}}, f)
            """), 0o755)
        env = dict(os.environ, EVAL_REAL_HALMOS=self.p("halmos"), EVAL_CHECK_RECORD=self.p("checks.jsonl"),
                   EVAL_LOG_DIR=self.p("logs"), EVAL_BRANCH_TIMEOUT="1ms")
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

    def test_a_second_branch_timeout_is_refused(self):
        r = self.wrapper("--solver-timeout-branching", "5ms")
        self.assertNotEqual(r.returncode, 0)
        self.assertFalse(os.path.exists(self.p("argv")), "Halmos never ran")


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

    def targets(self, contract="src/V.sol"):
        write(self.p("targets.toml"), "".join(
            f'[[target]]\nid = "t{i}"\nproject = "{self.p("proj")}"\ncontract = "{contract}"\n\n' for i in range(5)))

    def fake_target(self, run, t, project_hash):
        self.ran.append(t["id"])
        if t["id"] == getattr(self, "crash_on", None):
            os.makedirs(os.path.join(run.out, t["id"]), exist_ok=True)
            raise KeyboardInterrupt
        return {"id": t["id"], "class": "proved"}

    def main(self, *extra, out="out"):
        argv = ["--config", self.p("config.toml"), "--targets", self.p("targets.toml"), "--out", self.p(out), *extra]
        with mock.patch.object(runner, "Run", lambda cfg, out: mock.Mock(out=out, base_env={})), \
                mock.patch.object(runner, "tool_versions", lambda run: ({}, [])), \
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


if __name__ == "__main__":
    unittest.main(verbosity=2)
