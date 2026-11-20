//! Built-in source mutator: the stand-in for SuMo/Gambit until milestone 3.
//! It only has to answer one question for the baseline: do the generated tests
//! notice when the contract is wrong?
//!
//! Two kinds of mutant, each changing exactly one spot:
//! - operator swaps (`+=` -> `-=`, `>` -> `>=`, a `require` switched off, ...).
//!   In Solidity 0.8 many of these underflow or overflow and revert, which any
//!   test that merely calls the code will notice.
//! - statement deletions: a `+=` / `-=` line removed. These never revert, so
//!   only an assertion that checks state can catch them.
//! - rounding flips: `mulDivDown` <-> `mulDivUp`, `Rounding.Floor` <-> `Rounding.Ceil`.
//!   Also non-reverting; this is where ERC-4626 vaults usually go wrong.
//!
//! Comments and string literals are never touched, and neither are `pragma` /
//! `import` lines.

#[derive(Debug, Clone)]
pub struct Mutant {
    pub line: usize,
    /// What changed, e.g. "`+=` → `-=`" or "delete `total += a;`".
    pub change: String,
    pub source: String,
}

/// (from, to). Binary operators carry their spaces so `++`, `=>`, unary minus and
/// `x<=y` written without spaces are left alone; missing some mutants is fine,
/// producing garbage is not.
const OPERATORS: &[(&str, &str)] = &[
    ("+=", "-="),
    ("-=", "+="),
    (" + ", " - "),
    (" - ", " + "),
    (" * ", " / "),
    (" / ", " * "),
    (" <= ", " < "),
    (" < ", " <= "),
    (" >= ", " > "),
    (" > ", " >= "),
    (" == ", " != "),
    (" != ", " == "),
    // Turns a check off while keeping the file compiling.
    ("require(", "require(true || "),
    // Rounding direction, the classic ERC-4626 bug class (Solmate, Solady, OpenZeppelin
    // spellings). These never revert, so only a property about value catches them.
    ("mulDivDown(", "mulDivUp("),
    ("mulDivUp(", "mulDivDown("),
    ("fullMulDiv(", "fullMulDivUp("),
    ("fullMulDivUp(", "fullMulDiv("),
    ("Rounding.Floor", "Rounding.Ceil"),
    ("Rounding.Ceil", "Rounding.Floor"),
];

/// Marks which bytes are code (true) versus comment or string literal (false).
fn code_mask(src: &str) -> Vec<bool> {
    let b = src.as_bytes();
    let mut mask = vec![true; b.len()];
    let mut i = 0;
    while i < b.len() {
        let start = i;
        if b[i] == b'/' && b.get(i + 1) == Some(&b'/') {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
        } else if b[i] == b'/' && b.get(i + 1) == Some(&b'*') {
            i += 2;
            while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                i += 1;
            }
            i = (i + 2).min(b.len());
        } else if b[i] == b'"' || b[i] == b'\'' {
            let q = b[i];
            i += 1;
            while i < b.len() && b[i] != q {
                if b[i] == b'\\' {
                    i += 1;
                }
                i += 1;
            }
            i = (i + 1).min(b.len());
        } else {
            i += 1;
            continue;
        }
        mask[start..i].iter_mut().for_each(|m| *m = false);
    }
    mask
}

/// One planned edit: replace `len` bytes at `pos` with `to`.
struct Edit {
    pos: usize,
    len: usize,
    to: String,
    change: String,
}

pub fn mutants(src: &str, max: usize) -> Vec<Mutant> {
    let mask = code_mask(src);
    // Byte ranges of lines we never mutate.
    let mut skip = vec![false; src.len()];
    let mut off = 0;
    for line in src.split_inclusive('\n') {
        let t = line.trim_start();
        if t.starts_with("pragma") || t.starts_with("import") {
            skip[off..off + line.len()]
                .iter_mut()
                .for_each(|s| *s = true);
        }
        off += line.len();
    }
    let is_code = |range: std::ops::Range<usize>| range.into_iter().all(|k| mask[k] && !skip[k]);

    let mut edits: Vec<Edit> = Vec::new();
    for &(from, to) in OPERATORS {
        for (pos, _) in src.match_indices(from) {
            if is_code(pos..pos + from.len()) {
                edits.push(Edit {
                    pos,
                    len: from.len(),
                    to: to.to_string(),
                    change: format!("`{}` → `{}`", from.trim(), to.trim()),
                });
            }
        }
    }

    // Statement deletions: a whole line that is one `+=` / `-=` statement.
    // Lines with braces are skipped so deleting never unbalances a block.
    let mut off = 0;
    for line in src.split_inclusive('\n') {
        let t = line.trim();
        let start = off + (line.len() - line.trim_start().len());
        let updates = t.contains("+=") || t.contains("-=");
        if updates
            && t.ends_with(';')
            && !t.contains('{')
            && !t.contains('}')
            && is_code(start..start + t.len())
        {
            edits.push(Edit {
                pos: start,
                len: t.len(),
                to: "/* ausweg: deleted */".to_string(),
                change: format!("delete `{t}`"),
            });
        }
        off += line.len();
    }

    // Source order, so the same file always yields the same mutants.
    edits.sort_by(|a, b| (a.pos, &a.change).cmp(&(b.pos, &b.change)));
    edits.dedup_by(|a, b| a.pos == b.pos && a.change == b.change);

    edits
        .into_iter()
        .take(max)
        .map(|e| {
            let mut s = String::with_capacity(src.len() + 16);
            s.push_str(&src[..e.pos]);
            s.push_str(&e.to);
            s.push_str(&src[e.pos + e.len..]);
            Mutant {
                line: src[..e.pos].matches('\n').count() + 1,
                change: e.change,
                source: s,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const SRC: &str = r#"pragma solidity >=0.8.0 <0.9.0;
import "./A.sol";
contract V {
    // a + b in a comment
    string s = "x - y";
    function f(uint a, uint b) public returns (uint) {
        require(a > b, "a <= b");
        total += a;
        return a - b;
    }
}
"#;

    #[test]
    fn mutates_code_only() {
        let ms = mutants(SRC, 100);
        let ops: Vec<_> = ms.iter().map(|m| (m.line, m.change.as_str())).collect();
        assert_eq!(
            ops,
            vec![
                (7, "`require(` → `require(true ||`"),
                (7, "`>` → `>=`"),
                (8, "delete `total += a;`"),
                (8, "`+=` → `-=`"),
                (9, "`-` → `+`"),
            ]
        );
    }

    #[test]
    fn each_mutant_changes_one_spot() {
        for m in mutants(SRC, 100) {
            let changed = SRC
                .lines()
                .zip(m.source.lines())
                .filter(|(a, b)| a != b)
                .count();
            assert_eq!(
                changed, 1,
                "mutant at line {} changed {changed} lines",
                m.line
            );
        }
    }

    #[test]
    fn deletion_keeps_indentation_and_the_rest_of_the_file() {
        let ms = mutants(SRC, 100);
        let del = ms.iter().find(|m| m.change.starts_with("delete")).unwrap();
        assert!(
            del.source
                .contains("\n        /* ausweg: deleted */\n        return a - b;")
        );
    }

    #[test]
    fn never_deletes_a_line_with_braces() {
        let src = "contract C {\n    function f(uint a) public { total += a; }\n}\n";
        assert!(
            mutants(src, 100)
                .iter()
                .all(|m| !m.change.starts_with("delete"))
        );
    }

    #[test]
    fn flips_rounding_direction_in_all_three_spellings() {
        let src = "contract V {\n    function a(uint x) public pure returns (uint) { return x.mulDivDown(2, 3); }\n    function b(uint x) public pure returns (uint) { return x.fullMulDivUp(2, 3); }\n    function c(uint x) public pure returns (uint) { return _c(x, Math.Rounding.Floor); }\n    // x.mulDivUp(1, 2) in a comment stays put\n}\n";
        let changes: Vec<_> = mutants(src, 100).into_iter().map(|m| m.change).collect();
        assert_eq!(
            changes,
            vec![
                "`mulDivDown(` → `mulDivUp(`",
                "`fullMulDivUp(` → `fullMulDiv(`",
                "`Rounding.Floor` → `Rounding.Ceil`",
            ]
        );
    }

    #[test]
    fn respects_max() {
        assert_eq!(mutants(SRC, 2).len(), 2);
    }

    /// The demo contract in the README: keeps its documented mutant list honest.
    #[test]
    fn demo_bank_has_ten_mutants() {
        let bank = include_str!("../examples/Bank.sol");
        let ops: Vec<_> = mutants(bank, 100)
            .iter()
            .map(|m| (m.line, m.change.clone()))
            .collect();
        let want = [
            (9, "delete `balanceOf[msg.sender] += amount;`"),
            (9, "`+=` → `-=`"),
            (10, "delete `totalDeposits += amount;`"),
            (10, "`+=` → `-=`"),
            (14, "`require(` → `require(true ||`"),
            (14, "`>=` → `>`"),
            (15, "delete `balanceOf[msg.sender] -= amount;`"),
            (15, "`-=` → `+=`"),
            (16, "delete `totalDeposits -= amount;`"),
            (16, "`-=` → `+=`"),
        ];
        assert_eq!(ops.len(), want.len(), "{ops:#?}");
        for ((line, op), (wl, wop)) in ops.iter().zip(want) {
            assert_eq!((*line, op.as_str()), (wl, wop));
        }
    }
}
