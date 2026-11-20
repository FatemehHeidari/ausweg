//! Stage 2, plan: the model's only job in milestone 2. It returns JSON naming a
//! value for each constructor parameter (from a fixed menu) and a few invariants,
//! each one Solidity assertion. Everything here is checked before it is used.

use crate::abi::{Abi, Param};
use anyhow::{Context, Result, bail};
use serde_json::Value;

#[derive(Debug, Clone, PartialEq)]
pub enum CtorValue {
    /// A fresh mock ERC-20 the harness funds and the users approve.
    MockToken,
    /// The first user's address.
    User,
    /// An unused address, `makeAddr("<param>")`.
    NewAddress,
    Number(String),
    Bool(bool),
    Str(String),
}

#[derive(Debug, Clone, PartialEq, serde::Serialize)]
pub struct Invariant {
    pub id: String,
    pub statement: String,
    /// One Solidity statement, ending with `;`.
    pub assert: String,
}

/// An invariant the tool refused before compiling because it can never fail.
#[derive(Debug, Clone, PartialEq, serde::Serialize)]
pub struct Rejected {
    pub id: String,
    pub assert: String,
    pub reason: String,
}

#[derive(Debug, Clone)]
pub struct Plan {
    /// One value per constructor parameter, in order.
    pub ctor: Vec<CtorValue>,
    pub invariants: Vec<Invariant>,
    /// What the tool had to fill in or throw away, for the report.
    pub notes: Vec<String>,
}

/// Default cap on invariants kept from one plan; the prompt asks for 3 to 6.
pub const MAX_INVARIANTS: usize = 8;

/// What an assertion may refer to, as the scaffold names it.
pub struct Names<'a> {
    pub contract: &'a str,
    pub tokens: Vec<String>,
    pub sums: Vec<String>,
    pub abi: &'a Abi,
}

impl Names<'_> {
    pub fn describe(&self) -> String {
        let views: Vec<String> = self
            .abi
            .views()
            .iter()
            .map(|i| format!("    {}", i.signature()))
            .collect();
        let mut s = format!(
            "- target: the {} contract. Its view functions:\n{}\n",
            self.contract,
            views.join("\n")
        );
        for t in &self.tokens {
            s.push_str(&format!(
                "- {t}: a mock ERC-20 token: balanceOf(address), totalSupply()\n"
            ));
        }
        let mut helpers: Vec<String> = self.sums.iter().map(|f| format!("{f}()")).collect();
        helpers.push("userCount()".into());
        helpers.push("users(uint256)".into());
        s.push_str(&format!(
            "- handler: {} (each sum adds the value over the three users)\n",
            helpers.join(", ")
        ));
        s.push_str("- alice, bob, carol: the three users' addresses\n");
        s
    }
}

/// ERC-4626's rounding, fee and limit rules, paraphrased from the standard
/// (https://eips.ethereum.org/EIPS/eip-4626, CC0). These are the standard's
/// requirements, not invariants written for the bench, so a run with them still
/// tests what the model makes of them.
pub const ERC4626_RULES: &str = "\
The contract implements ERC-4626, the tokenized vault standard. The standard requires the
following, and a bug often breaks one of these rules:
- convertToShares and convertToAssets round down, and leave out fees.
- previewDeposit returns no more shares than deposit would mint for the same assets, and
  previewRedeem no more assets than redeem would pay for the same shares: both round down.
- previewMint returns no fewer assets than mint would take for the same shares, and
  previewWithdraw no fewer shares than withdraw would burn for the same assets: both round up.
- Preview functions include any deposit or withdrawal fees.
- Rounding always favours the vault over its users.
- maxDeposit, maxMint, maxWithdraw and maxRedeem return the most the matching call accepts
  without reverting.";

/// Whether the ABI has ERC-4626's conversion and preview functions.
pub fn is_erc4626(abi: &Abi) -> bool {
    [
        "asset",
        "totalAssets",
        "convertToShares",
        "convertToAssets",
        "previewDeposit",
        "previewMint",
        "previewWithdraw",
        "previewRedeem",
    ]
    .iter()
    .all(|name| abi.items.iter().any(|i| i.is_function() && i.name == *name))
}

pub fn prompt(
    contract: &str,
    path: &str,
    declaration: &str,
    abi: &Abi,
    source: Option<&str>,
    source_len: usize,
    rules: Option<&str>,
) -> String {
    let ctor = abi.constructor();
    let ctor_lines = if ctor.is_empty() {
        "   (the constructor takes no parameters: return an empty list)".to_string()
    } else {
        ctor.iter()
            .map(|p| {
                format!(
                    "   - {} ({}{})",
                    p.name,
                    p.ty,
                    if p.internal_type.is_empty() || p.internal_type == p.ty {
                        String::new()
                    } else {
                        format!(", declared as {}", p.internal_type)
                    }
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    };
    let views: Vec<String> = abi
        .views()
        .iter()
        .map(|i| format!("    {}", i.signature()))
        .collect();
    let mutating: Vec<String> = abi
        .mutating()
        .iter()
        .map(|i| format!("    {}", i.signature()))
        .collect();
    let rules_block = match rules {
        Some(r) => format!("Rules from the standard:\n{r}\n\n"),
        None => String::new(),
    };
    let source_block = match source {
        Some(src) => format!("Contract source:\n```solidity\n{src}\n```\n"),
        None => format!(
            "The source ({source_len} characters) is left out; rely on the function lists above.\n"
        ),
    };
    format!(
        r#"You are a smart contract security engineer. You write invariants: properties that must hold
after ANY sequence of calls, by any users, in any order.

Contract: {contract} ({path}), declared as: {declaration}

A test harness already exists. It deploys the contract, gives three users (alice, bob, carol)
tokens, and calls these state-changing functions in random order with random amounts:
{mutating}
It can also send mock tokens straight to the contract (donate) and mint mock tokens straight to it (yield).

1. Constructor. Choose a value for each parameter:
{ctor_lines}
   Allowed values: "mock_token" (a fresh ERC-20 the harness funds and the users approve),
   "user" (alice's address), "new_address" (an unused address), "number:<integer>",
   "true", "false", "string:<text>".

2. Invariants. Propose 3 to 6. Each has:
   - "id": a short snake_case name
   - "statement": one English sentence
   - "assert": ONE Solidity statement using a forge-std assertion (assertEq, assertLe, assertGe,
     assertLt, assertGt, assertTrue, assertApproxEqAbs). It may only read state, never change it.
   Names an assertion can use:
   - target: the {contract} contract, with these view functions:
{views}
   - each mock token, named after its constructor parameter without underscores
     (for example asset_ becomes asset): balanceOf(address), totalSupply()
   - handler: sum<Function>() for each view function that takes one address and returns a
     uint256 (for example sumBalanceOf() adds balanceOf over the three users), userCount(),
     users(uint256)
   - alice, bob, carol: the three users' addresses

{rules_block}Return ONLY JSON in exactly this shape:
{{"constructor": [{{"param": "<name>", "value": "<allowed value>"}}],
 "invariants": [{{"id": "...", "statement": "...", "assert": "..."}}]}}

{source_block}"#,
        mutating = mutating.join("\n"),
        views = views.join("\n"),
    )
}

/// Asks for new invariants in place of ones that can never fail. `base` is the
/// plan prompt, so the model sees the contract and the names again.
pub fn replace_prompt(
    base: &str,
    rejected: &[Rejected],
    kept: &[Invariant],
    wanted: usize,
) -> String {
    let rejected = rejected
        .iter()
        .map(|r| format!("- {}: {} ({})", r.id, r.assert, r.reason))
        .collect::<Vec<_>>()
        .join("\n");
    let kept = if kept.is_empty() {
        "(none)".to_string()
    } else {
        kept.iter()
            .map(|k| format!("- {}: {}", k.id, k.assert))
            .collect::<Vec<_>>()
            .join("\n")
    };
    format!(
        r#"{base}
Your previous answer had invariants that can never fail, whatever the contract does, so they
cannot catch a bug:
{rejected}

Already kept; do not repeat them:
{kept}

Propose up to {wanted} different invariants instead. Each assertion must be able to fail if the
contract has a bug.
Return ONLY JSON: {{"invariants": [{{"id": "...", "statement": "...", "assert": "..."}}]}}"#
    )
}

pub fn repair_prompt(inv: &Invariant, error: &str, names: &Names) -> String {
    format!(
        r#"This invariant's assertion does not compile.
Invariant: {statement}
Assertion: {assert}
Compiler error: {error}

Names the assertion can use:
{names}
Fix the assertion. Keep its meaning; do not weaken it. It must be ONE Solidity statement using a
forge-std assertion, reading state only.
Return ONLY JSON: {{"assert": "<the corrected statement>"}}"#,
        statement = inv.statement,
        assert = inv.assert,
        names = names.describe(),
    )
}

/// The first JSON object in a model answer.
fn json_object(answer: &str) -> Result<Value> {
    let start = answer.find('{').context("no JSON object in the answer")?;
    let end = answer.rfind('}').context("no JSON object in the answer")?;
    if end < start {
        bail!("no JSON object in the answer");
    }
    serde_json::from_str(&answer[start..=end]).context("the answer is not valid JSON")
}

/// snake_case, starting with a letter, at most 40 characters.
fn sanitize_id(raw: &str) -> String {
    let mut s: String = raw
        .trim()
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() {
                c.to_ascii_lowercase()
            } else {
                '_'
            }
        })
        .collect();
    while s.contains("__") {
        s = s.replace("__", "_");
    }
    let s = s.trim_matches('_').to_string();
    let s = if s.starts_with(|c: char| c.is_ascii_alphabetic()) {
        s
    } else {
        format!("p_{s}")
    };
    s.chars().take(40).collect()
}

/// One statement starting with an assertion, or None if it is not one.
pub fn clean_assert(raw: &str) -> Option<String> {
    let mut s = raw
        .trim()
        .trim_start_matches("```solidity")
        .trim_matches('`')
        .trim()
        .to_string();
    // A trailing line comment is harmless to drop.
    if let Some(i) = s.find("//") {
        s.truncate(i);
    }
    let s = s.trim().trim_end_matches(';').trim();
    let ok = s.starts_with("assert")
        && s.contains('(')
        && s.ends_with(')')
        && !s.contains(';')
        && !s.contains('{')
        && !s.contains('}')
        && s.len() <= 400;
    ok.then(|| format!("{s};"))
}

fn parse_ctor_value(raw: &str, p: &Param) -> Option<CtorValue> {
    let v = raw.trim();
    let address_like = p.is_address();
    if address_like {
        return match v {
            "mock_token" => Some(CtorValue::MockToken),
            "user" => Some(CtorValue::User),
            "new_address" => Some(CtorValue::NewAddress),
            _ => None,
        };
    }
    if p.ty.starts_with("uint") || p.ty.starts_with("int") {
        let n = v.strip_prefix("number:")?.trim();
        let digits = n.strip_prefix('-').unwrap_or(n);
        let valid = !digits.is_empty()
            && digits.chars().all(|c| c.is_ascii_digit())
            && (!n.starts_with('-') || p.ty.starts_with("int"));
        return valid.then(|| CtorValue::Number(n.to_string()));
    }
    if p.ty == "bool" {
        return match v {
            "true" => Some(CtorValue::Bool(true)),
            "false" => Some(CtorValue::Bool(false)),
            _ => None,
        };
    }
    if p.ty == "string" {
        return v
            .strip_prefix("string:")
            .map(|s| CtorValue::Str(s.to_string()));
    }
    None
}

/// What the tool picks when the model gives no usable value.
pub(crate) fn default_ctor_value(i: usize, p: &Param) -> Option<CtorValue> {
    if p.is_address() {
        let n = p.name.to_lowercase();
        let tokenish = n.contains("asset") || n.contains("token") || n.contains("underlying");
        return Some(if tokenish || (i == 0 && p.contract_type().is_some()) {
            CtorValue::MockToken
        } else {
            CtorValue::NewAddress
        });
    }
    if p.ty.starts_with("uint") || p.ty.starts_with("int") {
        return Some(CtorValue::Number("1".into()));
    }
    match p.ty.as_str() {
        "bool" => Some(CtorValue::Bool(false)),
        "string" => Some(CtorValue::Str("AUSWEG".into())),
        _ => None,
    }
}

pub fn parse(answer: &str, abi: &Abi, max_invariants: usize) -> Result<Plan> {
    let v = json_object(answer)?;
    let mut notes = Vec::new();

    // Constructor: a list of {param, value}, or an object {param: value}.
    let params = abi.constructor();
    let given: Vec<(String, String)> = match v.get("constructor") {
        Some(Value::Array(a)) => a
            .iter()
            .filter_map(|e| {
                Some((
                    e.get("param")?.as_str()?.to_string(),
                    e.get("value")?.as_str()?.to_string(),
                ))
            })
            .collect(),
        Some(Value::Object(m)) => m
            .iter()
            .filter_map(|(k, v)| Some((k.clone(), v.as_str()?.to_string())))
            .collect(),
        _ => Vec::new(),
    };
    let mut ctor = Vec::with_capacity(params.len());
    for (i, p) in params.iter().enumerate() {
        let by_name = given.iter().find(|(n, _)| n == &p.name).map(|(_, v)| v);
        let raw = by_name.or_else(|| given.get(i).map(|(_, v)| v));
        let value = match raw.and_then(|r| parse_ctor_value(r, p)) {
            Some(v) => v,
            None => {
                let d = default_ctor_value(i, p).with_context(|| {
                    format!(
                        "constructor parameter `{}` has type {}, which the harness cannot fill",
                        p.name, p.ty
                    )
                })?;
                notes.push(format!(
                    "constructor `{}`: {} not usable, used {:?}",
                    p.name,
                    raw.map_or("no value".to_string(), |r| format!("`{r}`")),
                    d
                ));
                d
            }
        };
        ctor.push(value);
    }

    // Invariants: keep the well-formed ones, rename duplicates.
    let invariants = collect_invariants(&v, &[], max_invariants, false, &mut notes);
    if invariants.is_empty() {
        bail!("the plan has no usable invariant");
    }
    Ok(Plan {
        ctor,
        invariants,
        notes,
    })
}

/// The well-formed invariants in `v`, at most `max`, with ids that clash with
/// `taken` (or with each other) renamed. With `dedupe`, an assertion that
/// repeats one in `taken` is dropped too.
fn collect_invariants(
    v: &Value,
    taken: &[Invariant],
    max: usize,
    dedupe: bool,
    notes: &mut Vec<String>,
) -> Vec<Invariant> {
    let mut out: Vec<Invariant> = Vec::new();
    for e in v
        .get("invariants")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
    {
        let raw_assert = e.get("assert").and_then(Value::as_str).unwrap_or("");
        let Some(assert) = clean_assert(raw_assert) else {
            notes.push(format!(
                "invariant dropped before compiling, not one assertion: `{}`",
                raw_assert.chars().take(80).collect::<String>()
            ));
            continue;
        };
        if dedupe {
            let key = crate::vacuous::norm(&assert);
            if let Some(t) = taken
                .iter()
                .chain(out.iter())
                .find(|t| crate::vacuous::norm(&t.assert) == key)
            {
                notes.push(format!("invariant dropped: repeats `{}`", t.id));
                continue;
            }
        }
        let mut id = sanitize_id(e.get("id").and_then(Value::as_str).unwrap_or("invariant"));
        let base = id.clone();
        let mut k = 2;
        while taken.iter().chain(out.iter()).any(|x| x.id == id) {
            id = format!("{base}_{k}");
            k += 1;
        }
        let statement = e
            .get("statement")
            .and_then(Value::as_str)
            .map(|s| s.split_whitespace().collect::<Vec<_>>().join(" "))
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| id.replace('_', " "));
        if out.len() == max {
            notes.push(format!(
                "invariant dropped: `{id}`: over the limit of {max}"
            ));
            continue;
        }
        out.push(Invariant {
            id,
            statement,
            assert,
        });
    }
    out
}

/// New invariants from a replacement answer, at most `max`. Names already in
/// `taken` are renamed and repeated assertions dropped, with notes saying so.
pub fn parse_replacements(
    answer: &str,
    taken: &[Invariant],
    max: usize,
) -> Result<(Vec<Invariant>, Vec<String>)> {
    let v = json_object(answer)?;
    let mut notes = Vec::new();
    let new = collect_invariants(&v, taken, max, true, &mut notes);
    Ok((new, notes))
}

pub fn parse_repair(answer: &str) -> Result<String> {
    let v = json_object(answer)?;
    let raw = v
        .get("assert")
        .and_then(Value::as_str)
        .context("no `assert` field")?;
    clean_assert(raw).context("the repaired assertion is not one assertion")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::OZ_VAULT_ABI;

    fn abi() -> Abi {
        Abi::parse(OZ_VAULT_ABI).unwrap()
    }

    #[test]
    fn parses_a_good_plan() {
        let answer = r#"Here you go:
        {"constructor": [{"param": "asset_", "value": "mock_token"}],
         "invariants": [
           {"id": "solvency", "statement": "The vault can pay out\n every share",
            "assert": "assertLe(target.convertToAssets(target.totalSupply()), target.totalAssets())"},
           {"id": "Supply Matches!", "statement": "", "assert": "assertEq(target.totalSupply(), handler.sumBalanceOf()); // sums"}
         ]}"#;
        let p = parse(answer, &abi(), MAX_INVARIANTS).unwrap();
        assert_eq!(p.ctor, vec![CtorValue::MockToken]);
        assert_eq!(
            p.invariants[0].statement,
            "The vault can pay out every share"
        );
        assert!(p.invariants[0].assert.ends_with("target.totalAssets());"));
        assert_eq!(p.invariants[1].id, "supply_matches");
        assert_eq!(p.invariants[1].statement, "supply matches");
        assert_eq!(
            p.invariants[1].assert,
            "assertEq(target.totalSupply(), handler.sumBalanceOf());"
        );
        assert!(p.notes.is_empty());
    }

    #[test]
    fn fills_a_missing_constructor_value_and_says_so() {
        let answer = r#"{"constructor": {"asset_": "a token please"},
                         "invariants": [{"id": "a", "statement": "s", "assert": "assertTrue(true)"}]}"#;
        let p = parse(answer, &abi(), MAX_INVARIANTS).unwrap();
        assert_eq!(p.ctor, vec![CtorValue::MockToken]);
        assert_eq!(p.notes.len(), 1);
    }

    #[test]
    fn drops_what_is_not_one_assertion_and_renames_duplicates() {
        let answer = r#"{"constructor": [], "invariants": [
            {"id": "x", "statement": "s", "assert": "uint256 a = 1; assertEq(a, 1);"},
            {"id": "x", "statement": "s", "assert": "if (true) { assertTrue(true); }"},
            {"id": "x", "statement": "s", "assert": "assertTrue(true);"},
            {"id": "x", "statement": "s", "assert": "assertTrue(false);"}]}"#;
        let p = parse(answer, &abi(), MAX_INVARIANTS).unwrap();
        let ids: Vec<_> = p.invariants.iter().map(|i| i.id.as_str()).collect();
        assert_eq!(ids, ["x", "x_2"]);
        let dropped = p
            .notes
            .iter()
            .filter(|n| n.starts_with("invariant dropped"))
            .count();
        assert_eq!(dropped, 2);
    }

    #[test]
    fn keeps_at_most_the_limit_and_says_what_it_cut() {
        let answer = r#"{"constructor": [], "invariants": [
            {"id": "a", "statement": "s", "assert": "assertTrue(true);"},
            {"id": "b", "statement": "s", "assert": "assertTrue(true);"}]}"#;
        let p = parse(answer, &abi(), 1).unwrap();
        assert_eq!(p.invariants.len(), 1);
        assert!(
            p.notes
                .iter()
                .any(|n| n.contains("`b`: over the limit of 1"))
        );
    }

    #[test]
    fn a_plan_without_usable_invariants_is_an_error() {
        let answer = r#"{"constructor": [], "invariants": [{"id": "x", "assert": "x = 1"}]}"#;
        assert!(parse(answer, &abi(), MAX_INVARIANTS).is_err());
        assert!(parse("no json here", &abi(), MAX_INVARIANTS).is_err());
    }

    #[test]
    fn replacements_get_fresh_names_and_skip_repeats() {
        let taken = [Invariant {
            id: "solvency".into(),
            statement: "s".into(),
            assert: "assertLe(target.convertToAssets(target.totalSupply()), target.totalAssets());"
                .into(),
        }];
        let answer = r#"{"invariants": [
            {"id": "solvency", "statement": "again", "assert": "assertLe( target.convertToAssets(target.totalSupply()) , target.totalAssets())"},
            {"id": "solvency", "statement": "new", "assert": "assertEq(target.totalSupply(), handler.sumBalanceOf())"},
            {"id": "c", "statement": "over", "assert": "assertGt(target.totalSupply(), 1)"}]}"#;
        let (new, notes) = parse_replacements(answer, &taken, 1).unwrap();
        assert_eq!(new.len(), 1);
        assert_eq!(new[0].id, "solvency_2");
        assert!(notes.iter().any(|n| n.contains("repeats `solvency`")));
        assert!(notes.iter().any(|n| n.contains("over the limit of 1")));
    }

    #[test]
    fn replace_prompt_says_what_was_rejected_and_what_is_kept() {
        let rejected = [Rejected {
            id: "nonneg".into(),
            assert: "assertGe(target.totalAssets(), 0);".into(),
            reason: "`target.totalAssets()` is unsigned, so it is never below 0".into(),
        }];
        let kept = [Invariant {
            id: "supply".into(),
            statement: "s".into(),
            assert: "assertEq(target.totalSupply(), handler.sumBalanceOf());".into(),
        }];
        let p = replace_prompt("BASE PROMPT", &rejected, &kept, 3);
        assert!(p.starts_with("BASE PROMPT"));
        assert!(p.contains(
            "- nonneg: assertGe(target.totalAssets(), 0); (`target.totalAssets()` is unsigned"
        ));
        assert!(p.contains("- supply: assertEq(target.totalSupply(), handler.sumBalanceOf());"));
        assert!(p.contains("Propose up to 3 different invariants"));
        assert!(replace_prompt("B", &rejected, &[], 1).contains("(none)"));
    }

    #[test]
    fn repair_answer_must_be_one_assertion() {
        assert_eq!(
            parse_repair(r#"{"assert": "assertEq(target.totalSupply(), 0)"}"#).unwrap(),
            "assertEq(target.totalSupply(), 0);"
        );
        assert!(parse_repair(r#"{"assert": "target.deposit(1, address(1));"}"#).is_err());
    }

    #[test]
    fn prompt_lists_the_menu_and_the_view_functions() {
        let p = prompt(
            "OZVault",
            "src/OZVault.sol",
            "contract OZVault is ERC4626",
            &abi(),
            None,
            26000,
            None,
        );
        assert!(p.contains("asset_ (address, declared as contract IERC20)"));
        assert!(p.contains("convertToAssets(uint256 shares) returns (uint256)"));
        assert!(p.contains("redeem(uint256 shares, address receiver, address owner)"));
        assert!(p.contains("The source (26000 characters) is left out"));
        assert!(!p.contains("Rules from the standard"));
        assert!(p.contains("- alice, bob, carol: the three users' addresses"));
    }

    #[test]
    fn rules_go_before_the_answer_format_when_given() {
        let p = prompt(
            "OZVault",
            "src/OZVault.sol",
            "contract OZVault is ERC4626",
            &abi(),
            None,
            26000,
            Some(ERC4626_RULES),
        );
        let rules = p.find("Rules from the standard:").unwrap();
        assert!(rules < p.find("Return ONLY JSON").unwrap());
        assert!(p.contains("previewWithdraw no fewer"));
        assert!(p.contains("both round up"));
        // The replacement prompt repeats the plan prompt, rules included.
        assert!(replace_prompt(&p, &[], &[], 1).contains("Rules from the standard:"));
    }

    #[test]
    fn recognises_erc4626_by_its_conversion_and_preview_functions() {
        let view = |n: &str| {
            format!(
                r#"{{"type":"function","name":"{n}","inputs":[],"outputs":[{{"name":"","type":"uint256","internalType":"uint256"}}],"stateMutability":"view"}}"#
            )
        };
        let names = [
            "asset",
            "totalAssets",
            "convertToShares",
            "convertToAssets",
            "previewDeposit",
            "previewMint",
            "previewWithdraw",
            "previewRedeem",
        ];
        let all = names.iter().map(|n| view(n)).collect::<Vec<_>>().join(",");
        assert!(is_erc4626(
            &Abi::parse(&format!(r#"{{"abi":[{all}]}}"#)).unwrap()
        ));
        let some = names[..7]
            .iter()
            .map(|n| view(n))
            .collect::<Vec<_>>()
            .join(",");
        assert!(!is_erc4626(
            &Abi::parse(&format!(r#"{{"abi":[{some}]}}"#)).unwrap()
        ));
        // The test fixture has only part of the interface.
        assert!(!is_erc4626(&abi()));
    }
}
