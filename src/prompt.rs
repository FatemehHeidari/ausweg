//! Design A prompts: one prompt per contract, plus a repair prompt that feeds
//! compiler errors back. Milestone 2 replaces these with staged prompts.

/// Two worked examples so a small model sees the expected shape of a property test.
const EXAMPLES: &str = r#"Example 1 (ERC-20): transfers never change total supply.
    function testFuzz_transferKeepsSupply(address to, uint256 amount) public {
        vm.assume(to != address(0) && to != address(this));
        amount = bound(amount, 0, token.balanceOf(address(this)));
        uint256 before = token.totalSupply();
        token.transfer(to, amount);
        assertEq(token.totalSupply(), before);
    }

Example 2 (ERC-4626): a deposit followed by a full redeem never returns more than was deposited.
    function testFuzz_noFreeAssets(uint256 assets) public {
        assets = bound(assets, 1, 1e30);
        asset.mint(address(this), assets);
        asset.approve(address(vault), assets);
        uint256 shares = vault.deposit(assets, address(this));
        uint256 out = vault.redeem(shares, address(this), address(this));
        assertLe(out, assets);
    }"#;

pub fn baseline(contract_name: &str, import_path: &str, source: &str) -> String {
    format!(
        "You are a smart contract security engineer writing Foundry property tests.\n\
         \n\
         Write ONE complete Solidity test file for the contract `{contract_name}` below.\n\
         Rules:\n\
         - Start with `// SPDX-License-Identifier: MIT` and `pragma solidity ^0.8.0;`.\n\
         - Import `forge-std/Test.sol` and the contract with: import \"{import_path}\";\n\
         - Name the test contract `{contract_name}PropertyTest`, inheriting from `Test`.\n\
         - Deploy everything the contract needs in `setUp()`; write any mock it depends on in the same file.\n\
         - Write 3 to 6 fuzz tests named `testFuzz_<property>`, each checking one property that must hold\n\
           for ALL inputs (an invariant about balances, supply, accounting, access control), not one example.\n\
         - Use `bound()` to keep inputs in a valid range instead of `vm.assume` where possible.\n\
         - Output only the Solidity file inside one ```solidity code block.\n\
         \n\
         {EXAMPLES}\n\
         \n\
         Contract under test ({import_path}):\n\
         ```solidity\n{source}\n```\n"
    )
}

pub fn repair(test_source: &str, compiler_errors: &str) -> String {
    // Long error output wastes the context window of a small model.
    let errors: String = compiler_errors.chars().take(4000).collect();
    format!(
        "This Foundry test file does not compile.\n\
         Fix ONLY the compile errors. Keep every property and its meaning; do not weaken or delete assertions.\n\
         Output the whole fixed file inside one ```solidity code block.\n\
         \n\
         Compiler errors:\n```\n{errors}\n```\n\
         \n\
         Test file:\n```solidity\n{test_source}\n```\n"
    )
}

/// Pull the Solidity file out of a model answer. Takes the first fenced block
/// (```solidity or plain ```); if there is no fence, takes the whole answer.
pub fn extract_solidity(answer: &str) -> String {
    let mut lines = answer.lines();
    while let Some(line) = lines.next() {
        if line.trim_start().starts_with("```") {
            let body: Vec<&str> = lines
                .by_ref()
                .take_while(|l| !l.trim_start().starts_with("```"))
                .collect();
            return body.join("\n").trim().to_string() + "\n";
        }
    }
    answer.trim().to_string() + "\n"
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extracts_fenced_block() {
        let a = "Sure!\n```solidity\ncontract A {}\n```\nDone.";
        assert_eq!(extract_solidity(a), "contract A {}\n");
    }

    #[test]
    fn extracts_plain_fence_and_ignores_later_blocks() {
        let a = "```\ncontract A {}\n```\n```\ncontract B {}\n```";
        assert_eq!(extract_solidity(a), "contract A {}\n");
    }

    #[test]
    fn no_fence_returns_whole_answer() {
        assert_eq!(extract_solidity("  contract A {}  "), "contract A {}\n");
    }

    #[test]
    fn baseline_prompt_names_contract_and_import() {
        let p = baseline("Vault", "../../src/Vault.sol", "contract Vault {}");
        assert!(p.contains("VaultPropertyTest"));
        assert!(p.contains("import \"../../src/Vault.sol\""));
    }
}
