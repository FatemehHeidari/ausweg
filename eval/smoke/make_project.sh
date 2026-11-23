#!/bin/sh
# Builds the smoke test's Foundry project from ausweg's examples and pinned
# libraries:  eval/smoke/make_project.sh /tmp/eval-smoke/project
# solmate is kept outside the project and linked in, as in a monorepo. Gambit
# mutates solmate's ERC20, so the smoke test also shows that a mutant of a
# linked dependency leaves the original alone.
set -eu
repo=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "${1:?usage: make_project.sh <directory>}"
dest=$(cd "$1" && pwd)
deps="$dest-deps"
mkdir -p "$dest/src" "$dest/lib" "$deps"
fetch() {
    git init -q "$1"
    git -C "$1" fetch -q --depth 1 "$2" "$3"
    git -C "$1" checkout -q FETCH_HEAD
    rm -rf "$1/.git"
}
fetch "$dest/lib/forge-std" https://github.com/foundry-rs/forge-std f3dae6e6ee381f25eb6a246f7da9b85c91a68219
fetch "$deps/solmate" https://github.com/transmissions11/solmate 89365b880c4f3c786bdd453d4b8e8fe410344a69
ln -s "$deps/solmate" "$dest/lib/solmate"
fetch "$dest/lib/openzeppelin-contracts" https://github.com/OpenZeppelin/openzeppelin-contracts 5fd1781b1454fd1ef8e722282f86f9293cacf256
cd "$dest"
cp "$repo/examples/SolmateVault.sol" "$repo/examples/SolmateVaultBug.sol" "$repo/examples/LoopVault.sol" \
    "$repo/eval/smoke/OZVault.sol" src/
cat > foundry.toml <<'TOML'
[profile.default]
src = "src"
out = "out"
libs = ["lib"]
solc_version = "0.8.38"
evm_version = "cancun"
remappings = [
    "forge-std/=lib/forge-std/src/",
    "solmate/=lib/solmate/src/",
    "@openzeppelin/contracts/=lib/openzeppelin-contracts/contracts/",
]
TOML
