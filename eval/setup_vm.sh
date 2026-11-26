#!/bin/sh
# Prepares a fresh Ubuntu 24.04 machine for the evaluation: every tool at its
# frozen version, under /opt/ausweg-eval, where eval/config.toml expects it.
# Run as root, with the ausweg commit that holds this runner:
#
#   sh setup_vm.sh <commit>
#
# It ends by printing each tool's version; eval/run.py checks them again at
# every run.
set -eu
commit=${1:?usage: setup_vm.sh <ausweg commit>}
prefix=/opt/ausweg-eval
foundry_sha256=8d17599b42e3139f1a9c171be3798c4ed8e743ae17b84cc3435e57bf2a51ae99

export DEBIAN_FRONTEND=noninteractive
apt-get update -q
apt-get install -y -q git curl ca-certificates build-essential pkg-config libssl-dev python3 python3-venv tmux
mkdir -p "$prefix/bin" "$prefix/src" "$prefix/foundry/bin"

# Rust, to build ausweg and Gambit: the toolchain the smoke-tested binaries
# were built with.
export RUSTUP_HOME="$prefix/rustup" CARGO_HOME="$prefix/cargo"
curl -sSf https://sh.rustup.rs | sh -s -- -y -q --profile minimal --default-toolchain 1.97.0 --no-modify-path
PATH="$CARGO_HOME/bin:$PATH"

# ausweg, and this runner, at the frozen commit.
if [ ! -d "$prefix/src/ausweg" ]; then
    git clone -q https://github.com/FatemehHeidari/ausweg "$prefix/src/ausweg"
fi
git -C "$prefix/src/ausweg" fetch -q origin
git -C "$prefix/src/ausweg" checkout -q "$commit"
cargo build -q --release --locked --manifest-path "$prefix/src/ausweg/Cargo.toml"
cp "$prefix/src/ausweg/target/release/ausweg" "$prefix/bin/ausweg"

# Gambit v1.0.7, with the dependency versions in eval/gambit-Cargo.lock: its
# tag ships no lockfile, so cargo install would resolve them anew on every
# machine. The smoke-tested binary was built from these versions.
gambit_commit=072ff4c6d747397f859e0a15a20fe1ff05672332
if [ ! -d "$prefix/src/gambit" ]; then
    git clone -q https://github.com/Certora/gambit "$prefix/src/gambit"
fi
git -C "$prefix/src/gambit" checkout -q "$gambit_commit"
cp "$prefix/src/ausweg/eval/gambit-Cargo.lock" "$prefix/src/gambit/Cargo.lock"
cargo build -q --release --locked --manifest-path "$prefix/src/gambit/Cargo.toml"
cp "$prefix/src/gambit/target/release/gambit" "$prefix/bin/gambit"

# Halmos 0.3.3, with the z3 and yices it pins and every other package it
# needs, at the versions in eval/requirements-halmos.txt.
python3 -m venv "$prefix/venv"
"$prefix/venv/bin/pip" install -q --disable-pip-version-check --no-deps -r "$prefix/src/ausweg/eval/requirements-halmos.txt"
"$prefix/venv/bin/pip" check

# Foundry 1.9.0, checked against the release the smoke test used.
curl -sSfL -o /tmp/foundry.tgz \
    https://github.com/foundry-rs/foundry/releases/download/v1.9.0/foundry_v1.9.0_linux_amd64.tar.gz
echo "$foundry_sha256  /tmp/foundry.tgz" | sha256sum -c -
tar -xzf /tmp/foundry.tgz -C "$prefix/foundry/bin"
rm /tmp/foundry.tgz

# bitwuzla 0.8.1 and cvc5 1.2.1, for the solver baselines: the archives
# Halmos 0.3.3 downloads for `--solver bitwuzla` and `--solver cvc5`, checked
# against the sha256 it pins, and the binary read from each as Halmos reads
# it. eval/config.toml pins the binaries' own sha256.
mkdir -p "$prefix/solvers"
solver() {
    curl -sSfL -o /tmp/solver.zip "$1"
    echo "$2  /tmp/solver.zip" | sha256sum -c -
    python3 -I -c 'import sys, zipfile; sys.stdout.buffer.write(zipfile.ZipFile(sys.argv[1]).read(sys.argv[2]))' \
        /tmp/solver.zip "$3" > "$prefix/solvers/$4"
    chmod 755 "$prefix/solvers/$4"
    rm /tmp/solver.zip
}
solver https://github.com/bitwuzla/bitwuzla/releases/download/0.8.1/Bitwuzla-Linux-x86_64-static.zip \
    d88ca19bd0495df4e83296d37b8e3b5b588af0768623d674000c681b472bb1d8 \
    Bitwuzla-Linux-x86_64-static/bin/bitwuzla bitwuzla
solver https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/cvc5-Linux-x86_64-static.zip \
    6d44abc233980a14d72cc5809287d27c3335b1d6ee863381d0b5ffcbd0d8de56 \
    cvc5-Linux-x86_64-static/bin/cvc5 cvc5

"$prefix/bin/ausweg" --version
"$prefix/venv/bin/halmos" --version
"$prefix/venv/bin/z3" --version
"$prefix/venv/bin/yices-smt2" --version
"$prefix/foundry/bin/forge" --version | head -2
"$prefix/solvers/bitwuzla" --version
"$prefix/solvers/cvc5" --version | head -1
sha256sum "$prefix/solvers/bitwuzla" "$prefix/solvers/cvc5"
echo "ready: the runner is in $prefix/src/ausweg/eval"
