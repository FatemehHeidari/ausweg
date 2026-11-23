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

# Gambit v1.0.7.
cargo install -q --locked --git https://github.com/Certora/gambit --tag v1.0.7 --root "$prefix"

# Halmos 0.3.3, with the z3 and yices it pins.
python3 -m venv "$prefix/venv"
"$prefix/venv/bin/pip" install -q halmos==0.3.3 z3-solver==4.12.6.0 yices-solver==2.6.4.post23

# Foundry 1.9.0, checked against the release the smoke test used.
curl -sSfL -o /tmp/foundry.tgz \
    https://github.com/foundry-rs/foundry/releases/download/v1.9.0/foundry_v1.9.0_linux_amd64.tar.gz
echo "$foundry_sha256  /tmp/foundry.tgz" | sha256sum -c -
tar -xzf /tmp/foundry.tgz -C "$prefix/foundry/bin"
rm /tmp/foundry.tgz

"$prefix/bin/ausweg" --version
"$prefix/venv/bin/halmos" --version
"$prefix/venv/bin/z3" --version
"$prefix/venv/bin/yices-smt2" --version
"$prefix/foundry/bin/forge" --version | head -2
echo "ready: the runner is in $prefix/src/ausweg/eval"
