"""Process control for the evaluation runner: run a command under a deadline and
leave nothing of it running afterwards.

Every command starts in a session of its own. On Linux the runner is also a
child subreaper, so a process whose parent dies is re-parented to the runner
instead of to init. When a deadline passes, or when a command ends, every
process left in its session is stopped, then every remaining descendant of
the runner. What was stopped is recorded, so a test can check that nothing
survived.
"""

import ctypes
import json
import os
import signal
import subprocess
import time

PR_SET_CHILD_SUBREAPER = 36


def become_subreaper():
    """Linux only: orphans of our descendants are re-parented to us."""
    try:
        libc = ctypes.CDLL(None, use_errno=True)
        return libc.prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) == 0
    except (OSError, AttributeError):
        return False


def _stat(pid):
    """(ppid, pgrp, session, comm) of a live process, or None."""
    try:
        with open(f"/proc/{pid}/stat") as f:
            s = f.read()
    except OSError:
        return None
    comm = s[s.index("(") + 1:s.rindex(")")]
    fields = s[s.rindex(")") + 2:].split()
    # fields[0] is the state; zombies are already gone for our purposes.
    if fields[0] == "Z":
        return None
    return int(fields[1]), int(fields[2]), int(fields[3]), comm


def _all_pids():
    return [int(p) for p in os.listdir("/proc") if p.isdigit()]


def in_session(sid):
    """Live processes of a session, other than us."""
    me = os.getpid()
    out = []
    for pid in _all_pids():
        st = _stat(pid)
        if st and st[2] == sid and pid != me:
            out.append((pid, st[3]))
    return out


def descendants(root):
    """Live descendants of `root`, by parent links."""
    children = {}
    names = {}
    for pid in _all_pids():
        st = _stat(pid)
        if st:
            children.setdefault(st[0], []).append(pid)
            names[pid] = st[3]
    out, todo = [], list(children.get(root, []))
    while todo:
        pid = todo.pop()
        out.append((pid, names.get(pid, "?")))
        todo.extend(children.get(pid, []))
    return out


def _signal_all(pids, sig):
    for pid, _ in pids:
        try:
            os.kill(pid, sig)
        except ProcessLookupError:
            pass


def stop_session(sid, grace=3.0):
    """Stop every process in a session, then every descendant of ours: the
    runner runs one command at a time, so any descendant left belongs to the
    command just stopped (an orphan re-parented to us as subreaper).
    Returns what was found running, by name."""
    found = in_session(sid)
    _signal_all(found, signal.SIGTERM)
    end = time.monotonic() + grace
    while time.monotonic() < end and in_session(sid):
        time.sleep(0.1)
    _signal_all(in_session(sid), signal.SIGKILL)
    strays = [p for p in descendants(os.getpid()) if p[0] not in {q for q, _ in found}]
    _signal_all(strays, signal.SIGKILL)
    time.sleep(0.2)
    _reap()
    return [name for _, name in found] + [name for _, name in strays]


def stop_descendants(root, grace=3.0):
    """Stop every descendant of `root`, not `root` itself. Used by a process
    that is a subreaper and runs one child at a time, with root = itself, so
    orphans of that child's descendants are still found."""
    found = descendants(root)
    _signal_all(found, signal.SIGTERM)
    end = time.monotonic() + grace
    while time.monotonic() < end and descendants(root):
        time.sleep(0.1)
    _signal_all(descendants(root), signal.SIGKILL)
    time.sleep(0.2)
    _reap()
    return [name for _, name in found]


def _reap():
    while True:
        try:
            pid, _ = os.waitpid(-1, os.WNOHANG)
        except ChildProcessError:
            return
        if pid == 0:
            return


def run(cmd, cwd, env, deadline, stdout_path, stderr_path, record=None, label=""):
    """Run `cmd` until it ends or until the monotonic `deadline`.

    Returns a dict: status ("exited" or "stopped at the deadline"), the exit
    code, the wall time, and what was left running and stopped. When `record`
    is a file path, the same dict, with the command, is appended to it as one
    JSON line.
    """
    start_wall = time.time()
    start = time.monotonic()
    with open(stdout_path, "wb") as out, open(stderr_path, "wb") as err:
        p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=out, stderr=err,
                             stdin=subprocess.DEVNULL, start_new_session=True)
        sid = p.pid
        status = "exited"
        try:
            p.wait(timeout=max(0.0, deadline - time.monotonic()))
        except subprocess.TimeoutExpired:
            status = "stopped at the deadline"
            # The command first, and reaped by Popen, so its exit status is
            # its own; then everything it started.
            p.kill()
            p.wait()
        left = stop_session(sid)
    # What is still running after the stop: must be nothing.
    remaining = [name for _, name in in_session(sid)] + [name for _, name in descendants(os.getpid())]
    result = {
        "label": label,
        "cmd": cmd,
        "cwd": str(cwd),
        "start": start_wall,
        "seconds": round(time.monotonic() - start, 3),
        "status": status,
        "returncode": p.returncode,
        "left_running_and_stopped": left,
        "still_running_after_stop": remaining,
        "stdout": str(stdout_path),
        "stderr": str(stderr_path),
    }
    if record:
        with open(record, "a") as f:
            f.write(json.dumps(result) + "\n")
    return result
