# Evaluation runner

Runs ausweg on a list of targets with the frozen settings in `config.toml`,
replays each exit counterexample from deployment, runs Gambit's mutants, and
classifies every result. Step 21 lists the settings; Step 22 describes the
runner and its smoke test.

## On a fresh VM

Ubuntu 24.04, as root, with the ausweg commit that holds this runner:

```sh
curl -sSfLO https://raw.githubusercontent.com/FatemehHeidari/ausweg/<commit>/eval/setup_vm.sh
sh setup_vm.sh <commit>
cd /opt/ausweg-eval/src/ausweg
python3 -I eval/test_runner.py
sh eval/smoke/make_project.sh /tmp/eval-smoke/project
python3 -I eval/run.py --config eval/config.toml --targets eval/smoke.toml --out /tmp/eval-smoke/run && python3 -I eval/smoke_check.py --targets eval/smoke.toml --out /tmp/eval-smoke/run
```

## Running the evaluation in shards

Each VM runs its share, one target at a time; `--resume` continues after an
interruption, skipping finished targets and redoing the one that was cut off.
It refuses to continue if the settings, targets file, tools, runner commit or
shard changed, or if a finished target's project, dependencies included, no
longer hashes as it did when the target ran. `merge.py` refuses shards that
ran another targets file than the one it is given, shards that differ from
each other, and a target that is missing or present twice. Shards differ if
any tool's sha256 does: one version built on two VMs need not be the same
bytes. A shard, the first included, with no record or no hash of a tool is
refused too. So before starting the shards, compare
`sha256sum /opt/ausweg-eval/bin/*` across the VMs, and if ausweg's or Gambit's
builds differ, copy one VM's binaries to the others. Start the run inside
`tmux` so it outlives the SSH session.

```sh
python3 -I eval/run.py --config eval/config.toml --targets <targets.toml> --out /srv/eval --shard 2/6 --resume
python3 -I eval/merge.py --targets <targets.toml> --out merged shard1 shard2 shard3 shard4 shard5 shard6
```

Needs Python 3.11 or later and nothing outside its standard library, plus the
tools in `config.toml`. Time limits are enforced on Linux, where the runner is
a child subreaper.

| File | Role |
| --- | --- |
| `run.py` | The runner: builds, proves, classifies, replays, mutates, records; resume and shards |
| `halmos_per_check.py` | Given to `ausweg prove` as `--halmos`: one Halmos process per check, each with its own limit |
| `replay.py` | The search from deployment, and the replay of what it finds |
| `templates/Erc4626Replay.sol`, `templates/ReplayToken.sol` | The search's handler and exit properties, written apart from ausweg's proof |
| `mutate.py` | Which functions Gambit mutates, and the mutants' project copies |
| `proc.py` | Commands under deadlines, with everything they start stopped |
| `config.toml` | The settings, with what each budget covers |
| `setup_vm.sh` | Installs every tool at its frozen version on a fresh VM |
| `gambit-Cargo.lock`, `requirements-halmos.txt` | The versions of Gambit's and Halmos's dependencies, which their releases leave open |
| `merge.py` | Merges the shards of one evaluation |
| `test_runner.py` | Regression tests for the runner, without Foundry or solvers |
| `smoke.toml`, `smoke_check.py`, `smoke/` | The smoke test, its project, and the check of its results |

Each run directory holds `manifests/` (settings, tool paths, versions and
hashes, runner commit, host, the environment commands get), `events.jsonl`
(every command in execution order, with its environment, timing, output
files and the executables it ran), `<target>/result.json`, and
`summary.json`.
