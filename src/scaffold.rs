//! Stage 3, scaffold: the tool writes the whole invariant test file except one
//! assertion line per invariant. The setup, the users, the handler and the
//! rate-moving actions are deterministic, so milestone 1's setup failures cannot
//! happen here.

use crate::abi::{Abi, Item, Param};
use crate::plan::{CtorValue, Invariant};

pub const TOKEN_FILE: &str = "AuswegToken.sol";

/// A plain ERC-20 anyone can mint. Self-contained, so it never clashes with
/// whatever ERC-20 the contract under test imports.
pub const TOKEN_SOURCE: &str = r#"// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// Mock token written by ausweg: a plain ERC-20 that anyone can mint.
contract AuswegToken {
    string public constant name = "AUSWEG Token";
    string public constant symbol = "AUSWEG";
    uint8 public constant decimals = 18;
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    function mint(address to, uint256 amount) external {
        totalSupply += amount;
        balanceOf[to] += amount;
        emit Transfer(address(0), to, amount);
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        emit Approval(msg.sender, spender, amount);
        return true;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        emit Transfer(msg.sender, to, amount);
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        uint256 allowed = allowance[from][msg.sender];
        if (allowed != type(uint256).max) allowance[from][msg.sender] = allowed - amount;
        balanceOf[from] -= amount;
        balanceOf[to] += amount;
        emit Transfer(from, to, amount);
        return true;
    }
}
"#;

/// Functions the handler never calls: they need a valid signature, so random
/// arguments only ever revert.
const SKIP: &[&str] = &["permit"];

/// Each user starts with this many of every mock token.
const FUNDING: &str = "1e30";
/// Upper bound for fuzzed amounts.
const AMOUNT_MAX: &str = "1e30";
/// Upper bound for one `yield` call.
const YIELD_MAX: &str = "1e24";

const SOLIDITY_KEYWORDS: &[&str] = &[
    "address",
    "after",
    "alias",
    "anonymous",
    "as",
    "assembly",
    "bool",
    "break",
    "byte",
    "bytes",
    "calldata",
    "case",
    "catch",
    "constant",
    "constructor",
    "continue",
    "contract",
    "default",
    "delete",
    "do",
    "else",
    "emit",
    "enum",
    "event",
    "external",
    "fallback",
    "false",
    "final",
    "for",
    "from",
    "function",
    "if",
    "immutable",
    "import",
    "in",
    "indexed",
    "inline",
    "interface",
    "internal",
    "is",
    "library",
    "mapping",
    "memory",
    "modifier",
    "new",
    "null",
    "override",
    "payable",
    "pragma",
    "private",
    "public",
    "pure",
    "receive",
    "return",
    "returns",
    "revert",
    "storage",
    "string",
    "struct",
    "super",
    "this",
    "throw",
    "true",
    "try",
    "type",
    "uint",
    "unchecked",
    "using",
    "var",
    "view",
    "virtual",
    "while",
];

/// Byte range of one invariant's assertion line in the generated file, so
/// compiler errors can be traced back to the invariant that caused them.
#[derive(Debug, Clone, PartialEq)]
pub struct Span {
    pub id: String,
    /// The assertion line itself.
    pub start: usize,
    pub end: usize,
    /// The whole invariant function, doc comment included: an error anywhere in
    /// it belongs to this invariant.
    pub fn_start: usize,
    pub fn_end: usize,
}

#[derive(Debug, Clone)]
pub struct Scaffold {
    pub source: String,
    pub spans: Vec<Span>,
}

/// Everything about the harness that does not depend on the invariants.
#[derive(Debug, Clone)]
pub struct Harness {
    pub contract: String,
    pub import_path: String,
    /// Mock token variable name per constructor parameter that got one.
    pub tokens: Vec<String>,
    /// Constructor argument expressions, in order.
    ctor_args: Vec<String>,
    /// Handler function sources.
    handler_fns: Vec<String>,
    /// `sumX` helper names.
    pub sums: Vec<String>,
    /// Handler function names, for the report.
    pub calls: Vec<String>,
    /// ABI functions left out, with the reason.
    pub skipped: Vec<String>,
    /// Append the tool's exit checks (ERC-4626 vaults only, see
    /// `supports_exit_checks`).
    pub exit_checks: bool,
}

/// The exit checks the tool writes, by test name.
pub const EXIT_CHECKS: [&str; 2] = [
    "invariant_ausweg_exit_redeem",
    "invariant_ausweg_exit_withdraw",
];

/// Functions the exit checks call.
const EXIT_FUNCTIONS: [&str; 8] = [
    "asset",
    "balanceOf",
    "maxRedeem",
    "previewRedeem",
    "redeem",
    "maxWithdraw",
    "previewWithdraw",
    "withdraw",
];

/// Whether the contract has the ERC-4626 functions the exit checks call.
pub fn supports_exit_checks(abi: &Abi) -> bool {
    EXIT_FUNCTIONS
        .iter()
        .all(|name| abi.items.iter().any(|i| i.is_function() && i.name == *name))
}

/// Liquidity, checked by running it: from every state the fuzzer reaches, each
/// user takes everything out, one after another, as in a bank run. A revert, a
/// payout below the preview, or a transfer that differs from the reported
/// amount fails the check. A snapshot rolls the exits back, so the campaign
/// continues from the state it reached. Messages start with `ausweg exit:`, which
/// the scorer counts as an assertion.
const EXIT_CHECKS_SOURCE: &str = r#"
    // Exit checks, written by ausweg: from every state the fuzzer reaches, each
    // user can take everything out, one after another. Each check runs in a
    // snapshot that is rolled back, so the campaign continues unchanged.

    /// ausweg: alice, bob and carol can each redeem every share they hold, one after another
    function invariant_ausweg_exit_redeem() public {
        uint256 snap = vm.snapshotState();
        address[3] memory exiting = [alice, bob, carol];
        for (uint256 i; i < exiting.length; i++) {
            address u = exiting[i];
            uint256 shares = target.balanceOf(u);
            if (shares == 0) continue;
            uint256 promised = target.previewRedeem(shares);
            uint256 before = AuswegToken(address(target.asset())).balanceOf(u);
            vm.prank(u);
            try target.redeem(shares, u, u) returns (uint256 paid) {
                assertGe(paid, promised, "ausweg exit: redeem paid less than previewRedeem");
                assertEq(AuswegToken(address(target.asset())).balanceOf(u), before + paid, "ausweg exit: redeem transferred a different amount");
                assertEq(target.balanceOf(u), 0, "ausweg exit: redeem left shares behind");
            } catch {
                assertTrue(false, "ausweg exit: redeem(balanceOf) reverted");
            }
        }
        vm.revertToStateAndDelete(snap);
    }

    /// ausweg: alice, bob and carol can each withdraw maxWithdraw, one after another
    function invariant_ausweg_exit_withdraw() public {
        uint256 snap = vm.snapshotState();
        address[3] memory exiting = [alice, bob, carol];
        for (uint256 i; i < exiting.length; i++) {
            address u = exiting[i];
            uint256 assets = target.maxWithdraw(u);
            if (assets == 0) continue;
            uint256 cost = target.previewWithdraw(assets);
            uint256 sharesBefore = target.balanceOf(u);
            uint256 before = AuswegToken(address(target.asset())).balanceOf(u);
            vm.prank(u);
            try target.withdraw(assets, u, u) returns (uint256 burned) {
                assertLe(burned, cost, "ausweg exit: withdraw burned more than previewWithdraw");
                assertEq(target.balanceOf(u) + burned, sharesBefore, "ausweg exit: withdraw burned a different amount");
                assertEq(AuswegToken(address(target.asset())).balanceOf(u), before + assets, "ausweg exit: withdraw transferred a different amount");
            } catch {
                assertTrue(false, "ausweg exit: withdraw(maxWithdraw) reverted");
            }
        }
        vm.revertToStateAndDelete(snap);
    }
"#;

fn is_identifier(s: &str) -> bool {
    !s.is_empty()
        && s.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !SOLIDITY_KEYWORDS.contains(&s)
}

fn capitalize(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        Some(f) => f.to_ascii_uppercase().to_string() + c.as_str(),
        None => String::new(),
    }
}

/// `asset_` -> `asset`; falls back to `token<i>` when that is not a usable name.
fn token_name(param: &str, i: usize, taken: &[String]) -> String {
    let n = param.trim_matches('_');
    let reserved = ["target", "handler", "users", "vm", "caller", "amount"];
    if is_identifier(n) && !reserved.contains(&n) && !taken.iter().any(|t| t == n) {
        n.to_string()
    } else {
        format!("token{i}")
    }
}

/// Wraps an address expression in the parameter's declared contract type, if any.
fn typed(p: &Param, address_expr: &str) -> String {
    match p.contract_type() {
        Some(c) => format!("{c}({address_expr})"),
        None => address_expr.to_string(),
    }
}

/// A handler function that calls `target.<item>` as a random user.
fn handler_fn(item: &Item, fn_name: &str) -> String {
    let mut params = vec!["uint256 callerSeed".to_string()];
    let mut body = vec!["address caller = _user(callerSeed);".to_string()];
    let mut args = Vec::new();
    for (i, p) in item.inputs.iter().enumerate() {
        let n = if is_identifier(&p.name)
            && !["caller", "callerSeed", "target", "users"].contains(&p.name.as_str())
        {
            p.name.clone()
        } else {
            format!("a{i}")
        };
        if p.is_address() {
            if p.name == "owner" || p.name == "from" {
                args.push(typed(p, "caller"));
            } else {
                params.push(format!("uint256 {n}Seed"));
                args.push(typed(p, &format!("_user({n}Seed)")));
            }
        } else if p.ty == "uint256" {
            params.push(format!("uint256 {n}"));
            body.push(format!("{n} = bound({n}, 0, {AMOUNT_MAX});"));
            args.push(n);
        } else {
            params.push(format!("{} {n}", p.ty));
            args.push(n);
        }
    }
    body.push("vm.prank(caller);".into());
    body.push(format!("target.{}({});", item.name, args.join(", ")));
    format!(
        "    // From the ABI: {sig}\n    function {fn_name}({params}) external {{\n{body}\n    }}\n",
        sig = item.signature(),
        params = params.join(", "),
        body = body
            .iter()
            .map(|l| format!("        {l}"))
            .collect::<Vec<_>>()
            .join("\n"),
    )
}

impl Harness {
    pub fn new(contract: &str, import_path: &str, abi: &Abi, ctor: &[CtorValue]) -> Self {
        let params = abi.constructor();
        let mut tokens: Vec<String> = Vec::new();
        let mut ctor_args = Vec::new();
        for (i, (p, v)) in params.iter().zip(ctor).enumerate() {
            let arg = match v {
                CtorValue::MockToken => {
                    let t = token_name(&p.name, i, &tokens);
                    let arg = typed(p, &format!("address({t})"));
                    tokens.push(t);
                    arg
                }
                CtorValue::User => typed(p, "users[0]"),
                CtorValue::NewAddress => typed(p, &format!("makeAddr(\"{}\")", p.name)),
                CtorValue::Number(n) => n.clone(),
                CtorValue::Bool(b) => b.to_string(),
                CtorValue::Str(s) => format!(
                    "\"{}\"",
                    s.chars()
                        .filter(|c| c.is_ascii() && !c.is_ascii_control())
                        .collect::<String>()
                        .replace(['\\', '"'], "")
                ),
            };
            ctor_args.push(arg);
        }

        // One handler function per state-changing function the scaffold can fill.
        let mut handler_fns = Vec::new();
        let mut calls = Vec::new();
        let mut skipped = Vec::new();
        for item in abi.mutating() {
            if SKIP.contains(&item.name.as_str()) {
                skipped.push(format!("{} (needs a signature)", item.name));
                continue;
            }
            if let Some(p) = item.inputs.iter().find(|p| !p.is_supported()) {
                skipped.push(format!("{} (parameter type {})", item.name, p.ty));
                continue;
            }
            let base = format!("call_{}", item.name);
            let mut name = base.clone();
            let mut k = 2;
            while calls.contains(&name) {
                name = format!("{base}_{k}");
                k += 1;
            }
            handler_fns.push(handler_fn(item, &name));
            calls.push(name);
        }
        // Moving the exchange rate: tokens arrive without new shares.
        for t in &tokens {
            handler_fns.push(format!(
                "    // A user sends {t} straight to the contract: moves the rate, mints no shares.\n    function donate_{t}(uint256 callerSeed, uint256 amount) external {{\n        address caller = _user(callerSeed);\n        amount = bound(amount, 0, {t}.balanceOf(caller));\n        vm.prank(caller);\n        {t}.transfer(address(target), amount);\n    }}\n"
            ));
            calls.push(format!("donate_{t}"));
            handler_fns.push(format!(
                "    // {t} minted straight to the contract, like yield.\n    function yield_{t}(uint256 amount) external {{\n        amount = bound(amount, 0, {YIELD_MAX});\n        {t}.mint(address(target), amount);\n    }}\n"
            ));
            calls.push(format!("yield_{t}"));
        }

        // Saturating sums, so a view returning type(uint256).max cannot overflow.
        let mut sums = Vec::new();
        let views = abi.views();
        for item in &views {
            let one_address = item.inputs.len() == 1 && item.inputs[0].is_address();
            let returns_amount = item.outputs.len() == 1 && item.outputs[0].ty == "uint256";
            let overloaded = views.iter().filter(|v| v.name == item.name).count() > 1;
            if one_address && returns_amount && !overloaded {
                let s = format!("sum{}", capitalize(&item.name));
                if !sums.contains(&s) {
                    sums.push(s);
                }
            }
        }

        Self {
            contract: contract.to_string(),
            import_path: import_path.to_string(),
            tokens,
            ctor_args,
            handler_fns,
            sums,
            calls,
            skipped,
            exit_checks: false,
        }
    }

    /// The test file with these invariants.
    pub fn render(&self, invariants: &[Invariant]) -> Scaffold {
        let c = &self.contract;
        let mut out = String::new();
        out.push_str(&format!(
            "// SPDX-License-Identifier: MIT\npragma solidity ^0.8.0;\n\n// Written by ausweg (milestone 2). The tool wrote everything except the lines\n// ending in `// model`, one assertion per invariant.\n\nimport {{Test}} from \"forge-std/Test.sol\";\nimport {{CommonBase}} from \"forge-std/Base.sol\";\nimport {{StdUtils}} from \"forge-std/StdUtils.sol\";\nimport \"{}\";\nimport {{AuswegToken}} from \"./{TOKEN_FILE}\";\n\n",
            self.import_path
        ));

        // Handler.
        let token_fields: String = self
            .tokens
            .iter()
            .map(|t| format!("    AuswegToken public {t};\n"))
            .collect();
        let token_params: String = self
            .tokens
            .iter()
            .map(|t| format!(", AuswegToken {t}_"))
            .collect();
        let token_assigns: String = self
            .tokens
            .iter()
            .map(|t| format!("        {t} = {t}_;\n"))
            .collect();
        out.push_str(&format!(
            "contract {c}Handler is CommonBase, StdUtils {{\n    {c} public target;\n{token_fields}    address[] public users;\n\n    constructor({c} target_{token_params}, address[] memory users_) {{\n        target = target_;\n{token_assigns}        users = users_;\n    }}\n\n    function userCount() external view returns (uint256) {{\n        return users.length;\n    }}\n\n    function _user(uint256 seed) internal view returns (address) {{\n        return users[seed % users.length];\n    }}\n\n"
        ));
        for f in &self.handler_fns {
            out.push_str(f);
            out.push('\n');
        }
        for s in &self.sums {
            let view = {
                let mut n = s.trim_start_matches("sum").to_string();
                if let Some(f) = n.get_mut(0..1) {
                    f.make_ascii_lowercase();
                }
                n
            };
            out.push_str(&format!(
                "    function {s}() external view returns (uint256 total) {{\n        for (uint256 i; i < users.length; i++) {{\n            uint256 v = target.{view}(users[i]);\n            unchecked {{\n                total = total + v < total ? type(uint256).max : total + v;\n            }}\n        }}\n    }}\n\n"
            ));
        }
        out.truncate(out.trim_end().len());
        out.push_str("\n}\n\n");

        // Test contract.
        let token_state: String = self
            .tokens
            .iter()
            .map(|t| format!("    AuswegToken internal {t};\n"))
            .collect();
        let token_deploys: String = self
            .tokens
            .iter()
            .map(|t| format!("        {t} = new AuswegToken();\n"))
            .collect();
        let funding: String = if self.tokens.is_empty() {
            String::new()
        } else {
            let lines: String = self
                .tokens
                .iter()
                .map(|t| {
                    format!(
                        "            {t}.mint(users[i], {FUNDING});\n            vm.prank(users[i]);\n            {t}.approve(address(target), type(uint256).max);\n"
                    )
                })
                .collect();
            format!("        for (uint256 i; i < users.length; i++) {{\n{lines}        }}\n")
        };
        let handler_tokens: String = self.tokens.iter().map(|t| format!(", {t}")).collect();
        out.push_str(&format!(
            "contract {c}Invariants is Test {{\n    {c} internal target;\n{token_state}    {c}Handler internal handler;\n    // The three users, by the names the prompt gives them, so assertions can use them.\n    address internal alice;\n    address internal bob;\n    address internal carol;\n\n    function setUp() public {{\n        alice = makeAddr(\"alice\");\n        bob = makeAddr(\"bob\");\n        carol = makeAddr(\"carol\");\n        address[] memory users = new address[](3);\n        users[0] = alice;\n        users[1] = bob;\n        users[2] = carol;\n{token_deploys}        target = new {c}({args});\n{funding}        handler = new {c}Handler(target{handler_tokens}, users);\n        targetContract(address(handler));\n    }}\n",
            args = self.ctor_args.join(", "),
        ));

        let mut spans = Vec::new();
        for inv in invariants {
            let statement: String = inv
                .statement
                .chars()
                .filter(|c| c.is_ascii() && !c.is_ascii_control())
                .collect();
            out.push('\n');
            let fn_start = out.len();
            out.push_str(&format!(
                "    /// {statement}\n    function invariant_{}() public view {{\n        ",
                inv.id
            ));
            let start = out.len();
            out.push_str(&inv.assert);
            let end = out.len();
            out.push_str(" // model\n    }\n");
            spans.push(Span {
                id: inv.id.clone(),
                start,
                end,
                fn_start,
                fn_end: out.len(),
            });
        }
        if self.exit_checks {
            out.push_str(EXIT_CHECKS_SOURCE);
        }
        out.push_str("}\n");
        Scaffold { source: out, spans }
    }
}

/// The invariant whose assertion covers this byte offset.
pub fn span_at(spans: &[Span], offset: usize) -> Option<&Span> {
    spans
        .iter()
        .find(|s| offset >= s.fn_start && offset < s.fn_end)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::OZ_VAULT_ABI;

    fn harness() -> Harness {
        let abi = Abi::parse(OZ_VAULT_ABI).unwrap();
        Harness::new(
            "OZVault",
            "../../src/OZVault.sol",
            &abi,
            &[CtorValue::MockToken],
        )
    }

    fn inv(id: &str, assert: &str) -> Invariant {
        Invariant {
            id: id.into(),
            statement: format!("{id} holds"),
            assert: assert.into(),
        }
    }

    #[test]
    fn deploys_from_the_plan_with_the_declared_type() {
        let h = harness();
        assert_eq!(h.tokens, ["asset"]);
        let s = h.render(&[]).source;
        assert!(s.contains("asset = new AuswegToken();"));
        assert!(s.contains("target = new OZVault(IERC20(address(asset)));"));
        assert!(s.contains("asset.mint(users[i], 1e30);"));
        assert!(s.contains("handler = new OZVaultHandler(target, asset, users);"));
    }

    #[test]
    fn exit_checks_are_written_only_when_asked() {
        let mut h = harness();
        let plain = h.render(&[]).source;
        assert!(!plain.contains("invariant_ausweg_exit"));
        h.exit_checks = true;
        let sc = h.render(&[]);
        for name in EXIT_CHECKS {
            assert!(sc.source.contains(&format!("function {name}() public {{")));
        }
        assert!(sc.source.contains("uint256 snap = vm.snapshotState();"));
        assert_eq!(
            sc.source
                .matches("vm.revertToStateAndDelete(snap);")
                .count(),
            2
        );
        assert!(
            sc.source
                .contains("try target.redeem(shares, u, u) returns (uint256 paid) {")
        );
        assert!(
            sc.source
                .contains("try target.withdraw(assets, u, u) returns (uint256 burned) {")
        );
        assert!(sc.source.contains("AuswegToken(address(target.asset()))"));
        // The bank run redeems every share each user holds, not maxRedeem's quote.
        assert!(sc.source.contains("uint256 shares = target.balanceOf(u);"));
        assert!(
            sc.source
                .contains("\"ausweg exit: redeem left shares behind\"")
        );
        // Every failure message is marked, so the scorer counts it as an assertion.
        let section = &sc.source[sc.source.find("// Exit checks, written by ausweg").unwrap()..];
        let calls: Vec<&str> = section
            .lines()
            .filter(|l| {
                ["assertGe(", "assertLe(", "assertEq(", "assertTrue("]
                    .iter()
                    .any(|a| l.contains(a))
            })
            .collect();
        assert_eq!(calls.len(), 8);
        for line in calls {
            assert!(line.contains("\"ausweg exit: "), "unmarked: {line}");
        }
        // The checks are the tool's, so no model span covers them.
        assert!(sc.spans.is_empty());
        assert!(sc.source.trim_end().ends_with('}'));
    }

    #[test]
    fn exit_checks_need_the_whole_withdrawal_interface() {
        // The fixture has redeem but not maxRedeem, withdraw and the previews.
        assert!(!supports_exit_checks(&Abi::parse(OZ_VAULT_ABI).unwrap()));
        let fns = EXIT_FUNCTIONS
            .iter()
            .map(|n| {
                format!(
                    r#"{{"type":"function","name":"{n}","inputs":[],"outputs":[],"stateMutability":"view"}}"#
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        assert!(supports_exit_checks(
            &Abi::parse(&format!(r#"{{"abi":[{fns}]}}"#)).unwrap()
        ));
    }

    /// The prompt names the users; the test contract must let assertions use the names.
    #[test]
    fn assertions_can_name_the_three_users() {
        let s = harness().render(&[]).source;
        for (i, name) in ["alice", "bob", "carol"].iter().enumerate() {
            assert!(s.contains(&format!("    address internal {name};\n")));
            assert!(s.contains(&format!("{name} = makeAddr(\"{name}\");")));
            // The handler's users are the same addresses.
            assert!(s.contains(&format!("users[{i}] = {name};")));
        }
        // Declared before setUp runs, assigned before the handler gets them.
        let assign = s.find("alice = makeAddr").unwrap();
        assert!(assign < s.find("handler = new OZVaultHandler").unwrap());
    }

    #[test]
    fn handler_calls_as_a_random_user_with_owner_set_to_the_caller() {
        let s = harness().render(&[]).source;
        assert!(s.contains(
            "function call_redeem(uint256 callerSeed, uint256 shares, uint256 receiverSeed) external {"
        ));
        assert!(s.contains("shares = bound(shares, 0, 1e30);"));
        assert!(s.contains("target.redeem(shares, _user(receiverSeed), caller);"));
        assert!(s.contains("function donate_asset(uint256 callerSeed, uint256 amount) external {"));
        assert!(s.contains("function yield_asset(uint256 amount) external {"));
    }

    #[test]
    fn skips_what_random_arguments_cannot_call() {
        let h = harness();
        assert_eq!(
            h.skipped,
            [
                "permit (needs a signature)",
                "batch (parameter type uint256[])"
            ]
        );
        assert_eq!(
            h.calls,
            [
                "call_approve",
                "call_deposit",
                "call_redeem",
                "donate_asset",
                "yield_asset"
            ]
        );
    }

    #[test]
    fn offers_sums_over_users_for_address_to_amount_views() {
        let h = harness();
        assert_eq!(h.sums, ["sumBalanceOf"]);
        assert!(
            h.render(&[])
                .source
                .contains("uint256 v = target.balanceOf(users[i]);")
        );
    }

    #[test]
    fn spans_point_at_each_assertion() {
        let a = "assertEq(target.totalSupply(), handler.sumBalanceOf());";
        let b = "assertTrue(true);";
        let sc = harness().render(&[inv("supply", a), inv("trivial", b)]);
        assert_eq!(&sc.source[sc.spans[0].start..sc.spans[0].end], a);
        assert_eq!(&sc.source[sc.spans[1].start..sc.spans[1].end], b);
        assert_eq!(
            span_at(&sc.spans, sc.spans[1].start + 3).unwrap().id,
            "trivial"
        );
        assert!(span_at(&sc.spans, 10).is_none());
        // An error on the function header still belongs to the invariant.
        let header = sc.source.find("function invariant_trivial").unwrap();
        assert_eq!(span_at(&sc.spans, header).unwrap().id, "trivial");
        assert!(
            sc.source
                .contains("function invariant_supply() public view {")
        );
    }

    #[test]
    fn a_contract_without_tokens_gets_no_funding_or_rate_actions() {
        let abi = Abi::parse(r#"{"abi":[{"type":"function","name":"deposit","inputs":[{"name":"amount","type":"uint256","internalType":"uint256"}],"outputs":[],"stateMutability":"nonpayable"}]}"#).unwrap();
        let h = Harness::new("Bank", "../../src/Bank.sol", &abi, &[]);
        let s = h.render(&[]).source;
        assert!(s.contains("target = new Bank();"));
        assert!(!s.contains("for (uint256 i; i < users.length; i++) {\n            "));
        assert!(!s.contains("donate_"));
        assert!(s.contains("function call_deposit(uint256 callerSeed, uint256 amount) external {"));
    }
}
