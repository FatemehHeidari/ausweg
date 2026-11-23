"""Reading and writing the runner's records."""

import hashlib
import json
import os
import tomllib


def read_text(path, errors=None):
    with open(path, errors=errors) as f:
        return f.read()


def read_lines(path):
    """The file's non-blank lines, stripped."""
    with open(path) as f:
        return [ln.strip() for ln in f if ln.strip()]


def read_json(path):
    with open(path) as f:
        return json.load(f)


def read_toml(path):
    with open(path, "rb") as f:
        return tomllib.load(f)


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path, obj):
    """Write the whole record or none of it, on disk before this returns, so
    a run resumed after a crash never reads half a record."""
    tmp = path + ".partial"
    with open(tmp, "w") as f:
        json.dump(obj, f, indent=1)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)
    d = os.open(os.path.dirname(os.path.abspath(path)), os.O_RDONLY)
    try:
        os.fsync(d)
    finally:
        os.close(d)
