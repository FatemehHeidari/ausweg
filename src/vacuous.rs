//! Assertions that can never fail. `assertGe(x, 0)` holds for every uint256
//! `x`, whatever the contract does, so it cannot catch a bug. In the first
//! milestone-2 run, 17 of the 24 invariants qwen2.5-coder:14b proposed were of
//! this kind.
//!
//! The check reads the assertion's text and errs towards letting it through: it
//! rejects only the shapes below. An expression counts as unsigned unless it
//! casts to a signed type, starts with a minus, or calls a target function that
//! returns a signed integer.
//!
//! - `x >= 0` or `0 <= x` with `x` unsigned, in any assertion form
//! - `x <= type(uint256).max` with `x` unsigned
//! - both sides the same expression: `assertEq(a, a)`, `a >= a`
//! - the constant `true` (or `false` under `assertFalse`)
//! - `&&` of parts that each always hold, `||` with one part that always holds

use crate::abi::Abi;

/// Why `assert` can never fail, or None when it can.
pub fn never_fails(assert: &str, abi: &Abi) -> Option<String> {
    let s = assert.trim().trim_end_matches(';').trim();
    let open = s.find('(')?;
    let close = matching(s, open)?;
    if close != s.len() - 1 {
        return None;
    }
    let name = s[..open].trim();
    let args = split_top(&s[open + 1..close], ",");
    let arg = |i: usize| args.get(i).map(|a| a.trim());
    let signed: Vec<String> = abi
        .items
        .iter()
        .filter(|i| i.is_function())
        .filter(|i| i.outputs.first().is_some_and(|o| o.ty.starts_with("int")))
        .map(|i| i.name.clone())
        .collect();
    let cx = Cx { signed: &signed };
    match name {
        "assertGe" => cx.ge(arg(0)?, arg(1)?),
        "assertLe" => cx.ge(arg(1)?, arg(0)?),
        "assertEq"
        | "assertEqDecimal"
        | "assertApproxEqAbs"
        | "assertApproxEqRel"
        | "assertApproxEqAbsDecimal"
        | "assertApproxEqRelDecimal" => same(arg(0)?, arg(1)?),
        "assertTrue" | "assert" => cx.always_true(arg(0)?),
        "assertFalse" => cx.always_false(arg(0)?),
        _ => None,
    }
}

/// The expression without spaces, for comparing two of them.
pub fn norm(e: &str) -> String {
    e.chars().filter(|c| !c.is_whitespace()).collect()
}

struct Cx<'a> {
    /// Target functions that return a signed integer.
    signed: &'a [String],
}

impl Cx<'_> {
    /// Why `a >= b` always holds, if it does.
    fn ge(&self, a: &str, b: &str) -> Option<String> {
        if is_zero(b) && self.unsigned(a) {
            return Some(format!(
                "`{}` is unsigned, so it is never below 0",
                a.trim()
            ));
        }
        if is_uint_max(a) && self.unsigned(b) {
            return Some("no uint256 is above type(uint256).max".into());
        }
        same(a, b)
    }

    fn unsigned(&self, e: &str) -> bool {
        let n = norm(e);
        !(n.starts_with('-')
            || has_signed_type(&n)
            || self.signed.iter().any(|f| n.contains(&format!(".{f}("))))
    }

    fn always_true(&self, e: &str) -> Option<String> {
        let e = unparen(e);
        if norm(e) == "true" {
            return Some("it asserts the constant true".into());
        }
        let any = split_top(e, "||");
        if any.len() > 1 {
            return any.iter().find_map(|p| self.always_true(p));
        }
        let all = split_top(e, "&&");
        if all.len() > 1 {
            let reasons: Option<Vec<String>> = all.iter().map(|p| self.always_true(p)).collect();
            return reasons.map(|r| r.join("; "));
        }
        if let Some(rest) = e.strip_prefix('!').filter(|r| !r.starts_with('=')) {
            return self.always_false(rest);
        }
        let (l, op, r) = comparison(e)?;
        match op {
            ">=" => self.ge(l, r),
            "<=" => self.ge(r, l),
            "==" => same(l, r),
            _ => None,
        }
    }

    fn always_false(&self, e: &str) -> Option<String> {
        let e = unparen(e);
        if norm(e) == "false" {
            return Some("it asserts that the constant false is false".into());
        }
        let any = split_top(e, "||");
        if any.len() > 1 {
            let reasons: Option<Vec<String>> = any.iter().map(|p| self.always_false(p)).collect();
            return reasons.map(|r| r.join("; "));
        }
        let all = split_top(e, "&&");
        if all.len() > 1 {
            return all.iter().find_map(|p| self.always_false(p));
        }
        if let Some(rest) = e.strip_prefix('!').filter(|r| !r.starts_with('=')) {
            return self.always_true(rest);
        }
        let (l, op, r) = comparison(e)?;
        match op {
            "<" => self.ge(l, r),
            ">" => self.ge(r, l),
            "!=" => same(l, r),
            _ => None,
        }
    }
}

fn same(a: &str, b: &str) -> Option<String> {
    let (na, nb) = (norm(unparen(a)), norm(unparen(b)));
    (!na.is_empty() && na == nb).then(|| format!("both sides are `{}`", unparen(a)))
}

/// `0`, `0x00`, `0e18`, `0 ether`, `uint256(0)`.
fn is_zero(e: &str) -> bool {
    let n: String = norm(unparen(e)).replace('_', "");
    let n = ["ether", "gwei", "wei"]
        .iter()
        .find_map(|u| n.strip_suffix(u))
        .unwrap_or(&n);
    if let Some(rest) = n.strip_prefix("uint") {
        let inner = rest.trim_start_matches(|c: char| c.is_ascii_digit());
        return inner
            .strip_prefix('(')
            .and_then(|i| i.strip_suffix(')'))
            .is_some_and(is_zero);
    }
    let digits = n
        .strip_prefix("0x")
        .or_else(|| n.split_once('e').map(|(m, _)| m))
        .unwrap_or(n);
    let exponent_ok = n
        .split_once('e')
        .is_none_or(|(_, x)| x.chars().all(|c| c.is_ascii_digit()));
    !digits.is_empty() && digits.chars().all(|c| c == '0') && exponent_ok
}

fn is_uint_max(e: &str) -> bool {
    matches!(
        norm(unparen(e)).as_str(),
        "type(uint256).max" | "type(uint).max"
    )
}

/// `int256(`, `int(`, `type(int128)`: a signed type named in the expression.
fn has_signed_type(n: &str) -> bool {
    n.match_indices("int").any(|(i, _)| {
        let before = n[..i].chars().next_back();
        let ident_before = before.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_');
        let after = n[i + 3..].trim_start_matches(|c: char| c.is_ascii_digit());
        !ident_before && (after.starts_with('(') || after.starts_with(')'))
    })
}

/// The expression without parentheses that wrap all of it.
fn unparen(e: &str) -> &str {
    let mut e = e.trim();
    while e.starts_with('(') && matching(e, 0) == Some(e.len() - 1) {
        e = e[1..e.len() - 1].trim();
    }
    e
}

/// Index of the bracket closing the one at `open`, skipping string literals.
fn matching(s: &str, open: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut quote: Option<char> = None;
    for (i, c) in s.char_indices().skip_while(|(i, _)| *i < open) {
        if let Some(q) = quote {
            if c == q {
                quote = None;
            }
            continue;
        }
        match c {
            '"' | '\'' => quote = Some(c),
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Splits at `sep` where it is outside brackets and strings.
fn split_top<'a>(s: &'a str, sep: &str) -> Vec<&'a str> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut quote: Option<char> = None;
    let mut start = 0;
    let mut i = 0;
    let bytes = s.as_bytes();
    while i < s.len() {
        let c = bytes[i] as char;
        if let Some(q) = quote {
            if c == q {
                quote = None;
            }
        } else if c == '"' || c == '\'' {
            quote = Some(c);
        } else if "([{".contains(c) {
            depth += 1;
        } else if ")]}".contains(c) {
            depth = depth.saturating_sub(1);
        } else if depth == 0 && bytes[i..].starts_with(sep.as_bytes()) {
            // `sep` is ASCII, so `i` is a character boundary here.
            parts.push(&s[start..i]);
            i += sep.len();
            start = i;
            continue;
        }
        i += 1;
    }
    parts.push(&s[start..]);
    parts
}

/// The top-level comparison in `e`: left side, operator, right side.
fn comparison(e: &str) -> Option<(&str, &str, &str)> {
    let b = e.as_bytes();
    let mut depth = 0usize;
    let mut quote: Option<u8> = None;
    for i in 0..b.len() {
        let c = b[i];
        if let Some(q) = quote {
            if c == q {
                quote = None;
            }
            continue;
        }
        match c {
            b'"' | b'\'' => quote = Some(c),
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth = depth.saturating_sub(1),
            _ if depth == 0 => {
                let next = b.get(i + 1).copied();
                let prev = i.checked_sub(1).map(|p| b[p]);
                let two = match (c, next) {
                    (b'>', Some(b'=')) => Some(">="),
                    (b'<', Some(b'=')) => Some("<="),
                    (b'=', Some(b'=')) => Some("=="),
                    (b'!', Some(b'=')) => Some("!="),
                    _ => None,
                };
                if let Some(op) = two {
                    // `>>=` and `<<=` are assignments, never comparisons.
                    if matches!(prev, Some(b'>') | Some(b'<')) {
                        return None;
                    }
                    return Some((e[..i].trim(), op, e[i + 2..].trim()));
                }
                let shift = matches!(next, Some(b'>') | Some(b'<'))
                    || matches!(prev, Some(b'>') | Some(b'<') | Some(b'='));
                if (c == b'>' || c == b'<') && !shift {
                    let op = if c == b'>' { ">" } else { "<" };
                    return Some((e[..i].trim(), op, e[i + 1..].trim()));
                }
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::OZ_VAULT_ABI;

    fn abi() -> Abi {
        Abi::parse(OZ_VAULT_ABI).unwrap()
    }

    fn rejects(a: &str) -> bool {
        never_fails(a, &abi()).is_some()
    }

    /// Shapes from the first qwen2.5-coder:14b run, and their neighbours.
    #[test]
    fn rejects_what_can_never_fail() {
        for a in [
            "assertGe(target.totalAssets(), 0);",
            "assertGe(target.totalAssets(), 0, \"assets, (never) negative\");",
            "assertGe(handler.sumMaxWithdraw(), uint256(0));",
            "assertGe(target.totalAssets(), 0, \"assets \u{2265} 0, always\");",
            "assertGe(asset.balanceOf(address(target)), 0x00);",
            "assertLe(0, target.totalSupply());",
            "assertTrue(target.maxRedeem(address(this)) >= 0);",
            "assertTrue((target.totalSupply() >= 0) && 0 <= target.totalAssets());",
            "assertTrue(target.totalSupply() > 1 || target.totalAssets() >= 0);",
            "assertFalse(target.totalAssets() < 0);",
            "assertFalse(!(target.totalAssets() >= 0));",
            "assert(target.totalSupply() >= 0);",
            "assertEq(target.totalSupply(), target.totalSupply());",
            "assertEq( target.totalSupply() , target.totalSupply());",
            "assertGe(target.totalSupply(), target.totalSupply());",
            "assertApproxEqAbs(target.totalAssets(), target.totalAssets(), 1);",
            "assertLe(target.totalSupply(), type(uint256).max);",
            "assertTrue(true);",
            "assertGe(target.balanceOf(address(1)) - target.balanceOf(address(2)), 0);",
        ] {
            assert!(rejects(a), "should reject: {a}");
        }
    }

    #[test]
    fn keeps_what_a_bug_could_break() {
        for a in [
            "assertGt(target.totalSupply(), 0);",
            "assertLe(target.convertToAssets(target.totalSupply()), target.totalAssets());",
            "assertEq(target.totalSupply(), handler.sumBalanceOf());",
            "assertGe(target.convertToAssets(target.previewWithdraw(1e18)), 1e18);",
            "assertTrue(target.totalSupply() >= 0 && target.totalAssets() > 5);",
            "assertTrue(target.totalSupply() >> 1 >= 0 == false);",
            "assertGe(int256(target.totalAssets()) - int256(target.totalSupply()), 0);",
            "assertGe(-1, 0);",
            "assertTrue(target.totalSupply() != target.totalSupply());",
            "assertFalse(target.totalSupply() >= 0);",
            "assertLe(target.totalSupply(), type(uint128).max);",
            "assertEq(target.totalSupply(), 0);",
        ] {
            assert!(!rejects(a), "should keep: {a}");
        }
    }

    #[test]
    fn a_function_returning_a_signed_integer_is_not_unsigned() {
        let signed = Abi::parse(
            r#"{"abi": [{"type":"function","name":"pnl","inputs":[],"outputs":[{"name":"","type":"int256","internalType":"int256"}],"stateMutability":"view"}]}"#,
        )
        .unwrap();
        assert!(never_fails("assertGe(target.pnl(), 0);", &signed).is_none());
        assert!(never_fails("assertGe(target.pnl() * 2, 0);", &signed).is_none());
    }

    #[test]
    fn says_why_in_words_the_model_can_use() {
        assert_eq!(
            never_fails("assertGe(target.totalAssets(), 0);", &abi()).unwrap(),
            "`target.totalAssets()` is unsigned, so it is never below 0"
        );
        assert_eq!(
            never_fails(
                "assertEq(target.totalSupply(), target.totalSupply());",
                &abi()
            )
            .unwrap(),
            "both sides are `target.totalSupply()`"
        );
    }

    #[test]
    fn reads_zero_in_its_usual_spellings() {
        for z in [
            "0",
            "00",
            "0x0",
            "0e18",
            "0 ether",
            "uint256(0)",
            "uint(0)",
            "(0)",
            "0_0",
        ] {
            assert!(is_zero(z), "{z}");
        }
        for nz in ["1", "0x1", "1e18", "10", "uint256(1)", "e0", "0ex"] {
            assert!(!is_zero(nz), "{nz}");
        }
    }
}
