//! Integer back end for Halmos: `ausweg smt <query.smt2>`.
//!
//! Halmos hands every assertion query to an external solver. The queries are
//! bit-vector formulas, and a vault's share math puts 256-bit multiplication
//! and division in them. Bit-blasting solvers (yices, bitwuzla, z3's bit-vector
//! mode) time out on those, even when the numbers involved are small.
//!
//! This back end rewrites the query exactly into integer arithmetic: an n-bit
//! value becomes an integer in [0, 2^n), and each operation keeps its modular
//! meaning, `bvadd` becoming `(a + b) mod 2^n` and so on. Where the bounds
//! asserted in the query show that a sum or product cannot wrap, the `mod` is
//! left out. z3 then reasons about x*y/d as numbers.
//!
//! Exact means the integer query is satisfiable if and only if the bit-vector
//! query is. A few operations have no simple integer form (a bitwise and of two
//! unknown words, a shift by an unknown amount); they become uninterpreted
//! functions. Then an `unsat` answer still holds, and a `sat` answer goes to a
//! bit-vector solver, since its model may not be a real one.

use anyhow::{Context, Result, anyhow, bail};
use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

// ---------------------------------------------------------------- S-expressions

#[derive(Debug, Clone, PartialEq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl Sexp {
    fn atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(a) => Some(a),
            Sexp::List(_) => None,
        }
    }
    fn list(&self) -> Option<&[Sexp]> {
        match self {
            Sexp::List(l) => Some(l),
            Sexp::Atom(_) => None,
        }
    }
}

fn is_delim(c: u8) -> bool {
    c.is_ascii_whitespace() || c == b'(' || c == b')' || c == b';'
}

pub fn parse_sexps(src: &str) -> Result<Vec<Sexp>> {
    let b = src.as_bytes();
    let mut i = 0;
    let mut stack: Vec<Vec<Sexp>> = vec![Vec::new()];
    while i < b.len() {
        match b[i] {
            b';' => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
            }
            b'(' => {
                stack.push(Vec::new());
                i += 1;
            }
            b')' => {
                let done = stack.pop().ok_or_else(|| anyhow!("unbalanced )"))?;
                stack
                    .last_mut()
                    .ok_or_else(|| anyhow!("unbalanced )"))?
                    .push(Sexp::List(done));
                i += 1;
            }
            b'|' => {
                let start = i;
                i += 1;
                while i < b.len() && b[i] != b'|' {
                    i += 1;
                }
                i = (i + 1).min(b.len());
                stack
                    .last_mut()
                    .unwrap()
                    .push(Sexp::Atom(src[start..i].to_string()));
            }
            b'"' => {
                let start = i;
                i += 1;
                while i < b.len() {
                    if b[i] == b'"' {
                        if i + 1 < b.len() && b[i + 1] == b'"' {
                            i += 2;
                            continue;
                        }
                        break;
                    }
                    i += 1;
                }
                i = (i + 1).min(b.len());
                stack
                    .last_mut()
                    .unwrap()
                    .push(Sexp::Atom(src[start..i].to_string()));
            }
            c if c.is_ascii_whitespace() => i += 1,
            _ => {
                let start = i;
                while i < b.len() && !is_delim(b[i]) {
                    i += 1;
                }
                stack
                    .last_mut()
                    .unwrap()
                    .push(Sexp::Atom(src[start..i].to_string()));
            }
        }
    }
    if stack.len() != 1 {
        bail!("unbalanced (");
    }
    Ok(stack.pop().unwrap())
}

// ---------------------------------------------------------------- sorts

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Sort {
    Bool,
    Bv(u32),
    Array(Box<Sort>, Box<Sort>),
}

impl Sort {
    fn width(&self) -> Option<u32> {
        match self {
            Sort::Bv(w) => Some(*w),
            _ => None,
        }
    }
    /// The sort in the integer query.
    fn int(&self) -> String {
        match self {
            Sort::Bool => "Bool".into(),
            Sort::Bv(_) => "Int".into(),
            Sort::Array(d, r) => format!("(Array {} {})", d.int(), r.int()),
        }
    }
}

fn parse_sort(s: &Sexp) -> Result<Sort> {
    match s {
        Sexp::Atom(a) if a == "Bool" => Ok(Sort::Bool),
        Sexp::List(l) => match l.as_slice() {
            [Sexp::Atom(u), Sexp::Atom(bv), Sexp::Atom(w)] if u == "_" && bv == "BitVec" => {
                Ok(Sort::Bv(w.parse().context("bit width")?))
            }
            [Sexp::Atom(a), d, r] if a == "Array" => Ok(Sort::Array(
                Box::new(parse_sort(d)?),
                Box::new(parse_sort(r)?),
            )),
            _ => bail!("unsupported sort {s:?}"),
        },
        _ => bail!("unsupported sort {s:?}"),
    }
}

// ---------------------------------------------------------------- term graph

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Op {
    Lit(BigUint),
    Bool(bool),
    /// A declared constant.
    Var(String),
    /// An application of a declared function.
    Fun(String),
    /// A built-in operation, by its SMT-LIB name.
    Prim(String),
    /// Halmos's `f_evm_<op>_<n>`: EVM arithmetic, where division by 0 gives 0.
    Evm(String),
    Extract(u32, u32),
    ZeroExt(u32),
    SignExt(u32),
    ConstArray,
}

#[derive(Debug, Clone)]
struct Node {
    op: Op,
    args: Vec<usize>,
    sort: Sort,
}

struct Macro {
    params: Vec<String>,
    body: Sexp,
}

#[derive(Default)]
struct Graph {
    nodes: Vec<Node>,
    intern: HashMap<(Op, Vec<usize>, Sort), usize>,
    consts: HashMap<String, Sort>,
    funs: HashMap<String, (Vec<Sort>, Sort)>,
    defs: HashMap<String, usize>,
    macros: HashMap<String, Macro>,
    scopes: Vec<HashMap<String, usize>>,
    asserts: Vec<usize>,
    /// Declaration order, for a stable output.
    decl_order: Vec<String>,
    /// `check-sat` commands seen: the translation answers exactly one.
    check_sats: usize,
}

fn pow2(n: u32) -> BigUint {
    BigUint::one() << n
}

fn parse_literal(a: &str) -> Option<(BigUint, u32)> {
    if let Some(h) = a.strip_prefix("#x") {
        return Some((BigUint::parse_bytes(h.as_bytes(), 16)?, 4 * h.len() as u32));
    }
    if let Some(bits) = a.strip_prefix("#b") {
        return Some((BigUint::parse_bytes(bits.as_bytes(), 2)?, bits.len() as u32));
    }
    None
}

const BOOL_PRIMS: &[&str] = &[
    "=", "distinct", "not", "and", "or", "xor", "=>", "bvule", "bvult", "bvuge", "bvugt", "bvsle",
    "bvslt", "bvsge", "bvsgt",
];

impl Graph {
    fn add(&mut self, op: Op, args: Vec<usize>, sort: Sort) -> usize {
        let key = (op.clone(), args.clone(), sort.clone());
        if let Some(&id) = self.intern.get(&key) {
            return id;
        }
        let id = self.nodes.len();
        self.nodes.push(Node { op, args, sort });
        self.intern.insert(key, id);
        id
    }

    fn sort(&self, id: usize) -> &Sort {
        &self.nodes[id].sort
    }

    fn command(&mut self, c: &Sexp) -> Result<()> {
        let l = match c.list() {
            Some(l) if !l.is_empty() => l,
            _ => return Ok(()),
        };
        let head = l[0].atom().unwrap_or("");
        match head {
            "declare-fun" => {
                let name = l[1].atom().context("declare-fun name")?.to_string();
                let params = l[2].list().context("declare-fun params")?;
                let ret = parse_sort(&l[3])?;
                if params.is_empty() {
                    self.consts.insert(name.clone(), ret);
                } else {
                    let ps = params.iter().map(parse_sort).collect::<Result<Vec<_>>>()?;
                    self.funs.insert(name.clone(), (ps, ret));
                }
                self.decl_order.push(name);
            }
            "declare-const" => {
                let name = l[1].atom().context("declare-const name")?.to_string();
                self.consts.insert(name.clone(), parse_sort(&l[2])?);
                self.decl_order.push(name);
            }
            "define-fun" => {
                let name = l[1].atom().context("define-fun name")?.to_string();
                let params = l[2].list().context("define-fun params")?;
                if evm_op(&name).is_some() {
                    // Halmos's refinement defines these; we give them their
                    // meaning directly.
                    return Ok(());
                }
                if params.is_empty() {
                    let id = self.term(&l[4])?;
                    self.defs.insert(name, id);
                } else {
                    let ps = params
                        .iter()
                        .map(|p| {
                            p.list()
                                .and_then(|pl| pl.first())
                                .and_then(|x| x.atom())
                                .map(|s| s.to_string())
                                .context("define-fun param")
                        })
                        .collect::<Result<Vec<_>>>()?;
                    self.macros.insert(
                        name,
                        Macro {
                            params: ps,
                            body: l[4].clone(),
                        },
                    );
                }
            }
            "assert" => {
                let id = self.term(&l[1])?;
                self.asserts.push(id);
            }
            // The translation keeps every assertion it reads: a popped one would
            // stay, and could make a satisfiable query unsat. Such a script
            // goes to the bit-vector solver unchanged.
            "push" | "pop" => bail!("{head}: assertion scopes are not translated"),
            "check-sat" => {
                self.check_sats += 1;
                if self.check_sats > 1 {
                    bail!("more than one check-sat: the translation answers one");
                }
            }
            "set-logic" | "set-info" | "set-option" | "get-model" | "exit" | "get-value"
            | "get-unsat-core" => {}
            other => bail!("unsupported command {other}"),
        }
        Ok(())
    }

    fn lookup(&self, name: &str) -> Option<usize> {
        for s in self.scopes.iter().rev() {
            if let Some(&id) = s.get(name) {
                return Some(id);
            }
        }
        self.defs.get(name).copied()
    }

    fn term(&mut self, s: &Sexp) -> Result<usize> {
        match s {
            Sexp::Atom(a) => {
                if a == "true" || a == "false" {
                    return Ok(self.add(Op::Bool(a == "true"), vec![], Sort::Bool));
                }
                if let Some((v, w)) = parse_literal(a) {
                    return Ok(self.add(Op::Lit(v), vec![], Sort::Bv(w)));
                }
                if let Some(id) = self.lookup(a) {
                    return Ok(id);
                }
                if let Some(sort) = self.consts.get(a).cloned() {
                    return Ok(self.add(Op::Var(a.clone()), vec![], sort));
                }
                bail!("unknown symbol {a}")
            }
            Sexp::List(l) => self.app(l),
        }
    }

    fn app(&mut self, l: &[Sexp]) -> Result<usize> {
        let Some(first) = l.first() else {
            bail!("empty application")
        };
        // (_ bvN w)
        if first.atom() == Some("_")
            && let [_, Sexp::Atom(bv), Sexp::Atom(w)] = l
            && let Some(n) = bv.strip_prefix("bv")
        {
            let v = BigUint::parse_bytes(n.as_bytes(), 10).context("bv literal")?;
            return Ok(self.add(Op::Lit(v), vec![], Sort::Bv(w.parse()?)));
        }
        if first.atom() == Some("let") {
            let binds = l[1].list().context("let bindings")?;
            let mut scope = HashMap::new();
            for b in binds {
                let bl = b.list().context("let binding")?;
                let name = bl[0].atom().context("let name")?.to_string();
                let id = self.term(&bl[1])?;
                scope.insert(name, id);
            }
            self.scopes.push(scope);
            let r = self.term(&l[2]);
            self.scopes.pop();
            return r;
        }
        if first.atom() == Some("!") {
            return self.term(&l[1]);
        }
        // Indexed operators and `as const`.
        if let Some(fl) = first.list() {
            let head = fl.first().and_then(|x| x.atom()).unwrap_or("");
            if head == "_" {
                let name = fl[1].atom().unwrap_or("");
                let idx = |k: usize| -> Result<u32> {
                    fl.get(k)
                        .and_then(|x| x.atom())
                        .context("index")?
                        .parse()
                        .context("index")
                };
                let x = self.term(&l[1])?;
                let w = self
                    .sort(x)
                    .width()
                    .context("indexed op on a non-bit-vector")?;
                return Ok(match name {
                    "extract" => {
                        let (hi, lo) = (idx(2)?, idx(3)?);
                        self.add(Op::Extract(hi, lo), vec![x], Sort::Bv(hi - lo + 1))
                    }
                    "zero_extend" => {
                        let k = idx(2)?;
                        self.add(Op::ZeroExt(k), vec![x], Sort::Bv(w + k))
                    }
                    "sign_extend" => {
                        let k = idx(2)?;
                        self.add(Op::SignExt(k), vec![x], Sort::Bv(w + k))
                    }
                    other => {
                        // repeat, rotate_*: kept as opaque functions.
                        let sort = match other {
                            "repeat" => Sort::Bv(w * idx(2)?),
                            _ => Sort::Bv(w),
                        };
                        self.add(Op::Prim(format!("{other}_{}", idx(2)?)), vec![x], sort)
                    }
                });
            }
            if head == "as" && fl.get(1).and_then(|x| x.atom()) == Some("const") {
                let sort = parse_sort(&fl[2])?;
                let v = self.term(&l[1])?;
                return Ok(self.add(Op::ConstArray, vec![v], sort));
            }
            bail!("unsupported application head {first:?}");
        }
        let f = first.atom().unwrap().to_string();
        let args = l[1..]
            .iter()
            .map(|a| self.term(a))
            .collect::<Result<Vec<_>>>()?;
        if let Some((_, _)) = evm_op(&f) {
            let sort = self.sort(args[0]).clone();
            return Ok(self.add(Op::Evm(f), args, sort));
        }
        if let Some(m) = self.macros.get(&f) {
            let scope: HashMap<String, usize> =
                m.params.iter().cloned().zip(args.iter().copied()).collect();
            let body = m.body.clone();
            self.scopes.push(scope);
            let r = self.term(&body);
            self.scopes.pop();
            return r;
        }
        if let Some((_, ret)) = self.funs.get(&f).cloned() {
            return Ok(self.add(Op::Fun(f), args, ret));
        }
        let sort = if BOOL_PRIMS.contains(&f.as_str()) {
            Sort::Bool
        } else {
            match f.as_str() {
                "ite" => self.sort(args[1]).clone(),
                "concat" => Sort::Bv(
                    args.iter()
                        .map(|&a| self.sort(a).width().unwrap_or(0))
                        .sum(),
                ),
                "select" => match self.sort(args[0]) {
                    Sort::Array(_, r) => (**r).clone(),
                    _ => bail!("select on a non-array"),
                },
                "store" => self.sort(args[0]).clone(),
                "bvcomp" => Sort::Bv(1),
                _ if f.starts_with("bv") => self.sort(args[0]).clone(),
                _ => bail!("unsupported function {f}"),
            }
        };
        Ok(self.add(Op::Prim(f), args, sort))
    }
}

/// `(bvmul c y)` with c = 2^n - 1 is how Halmos writes `-y`: returns y.
fn negated(g: &Graph, id: usize) -> Option<usize> {
    let n = &g.nodes[id];
    let w = n.sort.width()?;
    if !matches!(&n.op, Op::Prim(p) if p == "bvmul") || n.args.len() != 2 {
        return None;
    }
    let top = pow2(w) - 1u32;
    (0..2)
        .find(|&k| lit(g, n.args[k]) == Some(&top))
        .map(|k| n.args[1 - k])
}

/// The terms of a plain sum, nested sums flattened; false if a term is
/// negated.
fn summands(g: &Graph, id: usize, out: &mut Vec<usize>) -> bool {
    if negated(g, id).is_some() {
        return false;
    }
    let n = &g.nodes[id];
    if matches!(&n.op, Op::Prim(p) if p == "bvadd") {
        n.args.iter().all(|&a| summands(g, a, out))
    } else {
        out.push(id);
        true
    }
}

/// Removes one occurrence of `x`; whether there was one.
fn take(v: &mut Vec<usize>, x: usize) -> bool {
    match v.iter().position(|&y| y == x) {
        Some(k) => {
            v.remove(k);
            true
        }
        None => false,
    }
}

/// a <= b along the asserted orderings, transitively (an equality orders both
/// ways): `owed = slot9` and `owed <= balance` give slot9 <= balance.
struct Order {
    next: HashMap<usize, Vec<usize>>,
    memo: std::cell::RefCell<HashMap<usize, HashSet<usize>>>,
}

impl Order {
    fn new(facts: &Facts) -> Self {
        let mut next: HashMap<usize, Vec<usize>> = HashMap::new();
        for &(a, b) in &facts.le {
            next.entry(a).or_default().push(b);
        }
        Order {
            next,
            memo: Default::default(),
        }
    }

    /// Every node b with a <= b, besides a itself.
    fn reach(&self, a: usize) -> HashSet<usize> {
        if let Some(s) = self.memo.borrow().get(&a) {
            return s.clone();
        }
        let mut seen = HashSet::new();
        let mut todo = vec![a];
        while let Some(x) = todo.pop() {
            for &y in self.next.get(&x).map(Vec::as_slice).unwrap_or(&[]) {
                if seen.insert(y) {
                    todo.push(y);
                }
            }
        }
        self.memo.borrow_mut().insert(a, seen.clone());
        seen
    }

    fn le(&self, a: usize, b: usize) -> bool {
        a == b || self.reach(a).contains(&b)
    }
}

/// Whether every term of `small` occurs in `big`, counting repeats.
fn within(small: &[usize], big: &[usize]) -> bool {
    let mut big = big.to_vec();
    small.iter().all(|&t| take(&mut big, t))
}

/// Whether the sum `id` = sum(pos) - sum(neg) does not wrap, that is sum(neg)
/// is at most sum(pos), all terms unsigned and already translated, sum(pos)
/// and sum(neg) each below 2^n. It follows from:
/// - `id <= x` for a term x of pos: solc's checked subtraction is
///   `diff := sub(x, y); if gt(diff, x) { panic }`, and a wrapped difference is
///   larger than x;
/// - an earlier difference shown not to wrap, with at least these positive
///   terms and at most these negated ones (`1 + balance - a - b` after
///   `balance - a - b`);
/// - orderings of one term against another, or of two sums (`a + b <= c`, as
///   a solvency check asserts);
/// - the terms' ranges.
#[allow(clippy::too_many_arguments)]
fn covered(
    g: &Graph,
    facts: &Facts,
    order: &Order,
    ranges: &[Range],
    proven: &[(usize, Vec<usize>, Vec<usize>)],
    id: usize,
    pos: &[usize],
    neg: &[usize],
    m: &BigUint,
) -> bool {
    let known = |ts: &[usize]| ts.iter().all(|&t| t < ranges.len());
    let hi_sum = |ts: &[usize]| -> BigUint { ts.iter().map(|&t| ranges[t].hi.clone()).sum() };
    // id <= x, or id <= a sum of positive terms (solc's check on `a + b - c`
    // compares the difference with a + b).
    if pos.iter().any(|&x| order.le(id, x)) {
        return true;
    }
    for r in order.reach(id) {
        let mut rs = Vec::new();
        if summands(g, r, &mut rs) && known(&rs) && hi_sum(&rs) < *m && within(&rs, pos) {
            return true;
        }
    }
    let mut pos: Vec<usize> = pos.to_vec();
    let mut neg: Vec<usize> = neg
        .iter()
        .copied()
        .filter(|&y| !ranges[y].hi.is_zero())
        .collect();
    if proven
        .iter()
        .any(|(_, pp, pn)| within(&neg, pn) && within(pp, &pos))
    {
        return true;
    }
    // One term at most another.
    let mut i = 0;
    while i < neg.len() {
        match pos.iter().position(|&x| order.le(neg[i], x)) {
            Some(k) => {
                pos.remove(k);
                neg.remove(i);
            }
            None => i += 1,
        }
    }
    // A sum of terms at most a sum of others. Sound when neither sum wraps.
    let mut pairs: Vec<(usize, usize)> = facts.le.iter().copied().collect();
    pairs.sort_unstable();
    for (l, r) in pairs {
        if neg.is_empty() {
            break;
        }
        let (mut ls, mut rs) = (Vec::new(), Vec::new());
        if !summands(g, l, &mut ls) || !summands(g, r, &mut rs) || !known(&ls) || !known(&rs) {
            continue;
        }
        if hi_sum(&ls) >= *m || hi_sum(&rs) >= *m {
            continue;
        }
        let mut pos2 = pos.clone();
        if !rs.iter().all(|&t| take(&mut pos2, t)) {
            continue;
        }
        let mut rest = Vec::new();
        for &y in &neg {
            if !take(&mut ls, y) {
                rest.push(y);
            }
        }
        if rest.len() == neg.len() {
            continue;
        }
        pos = pos2;
        neg = rest;
    }
    let lo: BigUint = pos.iter().map(|&x| ranges[x].lo.clone()).sum();
    lo >= hi_sum(&neg)
}

/// `f_evm_bvudiv_256` -> ("bvudiv", 256).
fn evm_op(name: &str) -> Option<(String, u32)> {
    let rest = name.strip_prefix("f_evm_")?;
    let (op, n) = rest.rsplit_once('_')?;
    let n: u32 = n.parse().ok()?;
    ["bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem"]
        .contains(&op)
        .then(|| (op.to_string(), n))
}

// ---------------------------------------------------------------- bounds

/// What the asserted facts say about a node's value.
#[derive(Clone)]
struct Range {
    lo: BigUint,
    hi: BigUint,
}

struct Facts {
    hi: HashMap<usize, BigUint>,
    lo: HashMap<usize, BigUint>,
    /// (a, b): a <= b holds.
    le: HashSet<(usize, usize)>,
}

fn lit(g: &Graph, id: usize) -> Option<&BigUint> {
    match &g.nodes[id].op {
        Op::Lit(v) => Some(v),
        _ => None,
    }
}

fn collect_facts(g: &Graph) -> Facts {
    let mut f = Facts {
        hi: HashMap::new(),
        lo: HashMap::new(),
        le: HashSet::new(),
    };
    let mut todo: Vec<(usize, bool)> = g.asserts.iter().map(|&a| (a, true)).collect();
    while let Some((id, pos)) = todo.pop() {
        let n = &g.nodes[id];
        let name = match &n.op {
            Op::Prim(p) => p.as_str(),
            _ => continue,
        };
        match (name, pos) {
            ("and", true) | ("or", false) => {
                todo.extend(n.args.iter().map(|&a| (a, pos)));
                continue;
            }
            ("not", _) => {
                todo.push((n.args[0], !pos));
                continue;
            }
            _ => {}
        }
        // Normalize to a <= b or a < b.
        let (a, b, strict) = match (name, pos) {
            ("bvule", true) => (n.args[0], n.args[1], false),
            ("bvult", true) => (n.args[0], n.args[1], true),
            ("bvuge", true) => (n.args[1], n.args[0], false),
            ("bvugt", true) => (n.args[1], n.args[0], true),
            ("bvule", false) => (n.args[1], n.args[0], true),
            ("bvult", false) => (n.args[1], n.args[0], false),
            ("bvuge", false) => (n.args[0], n.args[1], true),
            ("bvugt", false) => (n.args[0], n.args[1], false),
            ("=", true) if n.args.len() == 2 => {
                let (x, y) = (n.args[0], n.args[1]);
                if g.sort(x).width().is_some() {
                    f.le.insert((x, y));
                    f.le.insert((y, x));
                    for (p, q) in [(x, y), (y, x)] {
                        if let Some(c) = lit(g, q) {
                            tighten_hi(&mut f.hi, p, c.clone());
                            tighten_lo(&mut f.lo, p, c.clone());
                            // High bits that are zero bound the whole word:
                            // ((_ extract n-1 k) v) = 0 gives v < 2^k.
                            if c.is_zero()
                                && let Op::Extract(hi, lo) = g.nodes[p].op
                            {
                                let v = g.nodes[p].args[0];
                                if g.sort(v).width() == Some(hi + 1) {
                                    tighten_hi(&mut f.hi, v, pow2(lo) - 1u32);
                                }
                            }
                        }
                    }
                }
                continue;
            }
            _ => continue,
        };
        f.le.insert((a, b));
        if let Some(c) = lit(g, b) {
            let c = if strict {
                if c.is_zero() {
                    continue;
                }
                c - 1u32
            } else {
                c.clone()
            };
            tighten_hi(&mut f.hi, a, c);
        }
        if let Some(c) = lit(g, a) {
            let c = if strict { c + 1u32 } else { c.clone() };
            tighten_lo(&mut f.lo, b, c);
        }
    }
    propagate_order(&mut f);
    // A bound on the low bits of a word whose high bits are zero is a bound on
    // the word: z3's simplifier writes `v <= c` that way.
    let low_parts: Vec<(usize, usize, u32)> = g
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(id, n)| match n.op {
            Op::Extract(hi, 0) => Some((id, n.args[0], hi)),
            _ => None,
        })
        .collect();
    for (e, v, hi) in low_parts {
        let high_zero = f.hi.get(&v).is_some_and(|b| *b < pow2(hi + 1));
        if !high_zero {
            continue;
        }
        if let Some(c) = f.hi.get(&e).cloned() {
            tighten_hi(&mut f.hi, v, c);
        }
        if let Some(c) = f.lo.get(&e).cloned() {
            tighten_lo(&mut f.lo, v, c);
        }
    }
    propagate_order(&mut f);
    f
}

/// Bounds travel along asserted orderings: a <= b and b <= c give a <= c.
/// A checked `balance - amount` asserts amount <= balance, so the amount gets
/// the balance's bound.
fn propagate_order(f: &mut Facts) {
    let pairs: Vec<(usize, usize)> = f.le.iter().copied().collect();
    for _ in 0..8 {
        let mut changed = false;
        for &(a, b) in &pairs {
            if let Some(hb) = f.hi.get(&b).cloned()
                && f.hi.get(&a).is_none_or(|ha| hb < *ha)
            {
                f.hi.insert(a, hb);
                changed = true;
            }
            if let Some(la) = f.lo.get(&a).cloned()
                && f.lo.get(&b).is_none_or(|lb| la > *lb)
            {
                f.lo.insert(b, la);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

fn tighten_hi(m: &mut HashMap<usize, BigUint>, id: usize, v: BigUint) {
    let e = m.entry(id).or_insert_with(|| v.clone());
    if v < *e {
        *e = v;
    }
}

fn tighten_lo(m: &mut HashMap<usize, BigUint>, id: usize, v: BigUint) {
    let e = m.entry(id).or_insert_with(|| v.clone());
    if v > *e {
        *e = v;
    }
}

// ---------------------------------------------------------------- translation

struct Translation {
    script: String,
    /// The query without the assertions that depend on an abstracted
    /// operation, when there are any. If even this is unsat, so is the query.
    relaxed: Option<String>,
    /// Some operation became an uninterpreted function: only `unsat` is final.
    abstracted: bool,
    /// Halmos variables to read back from a model: (name, width).
    model_vars: Vec<(String, u32)>,
}

fn translate(g: &Graph) -> Translation {
    let facts = collect_facts(g);
    let order = Order::new(&facts);
    // Differences shown not to wrap: (node, positive terms, negated terms).
    let mut proven: Vec<(usize, Vec<usize>, Vec<usize>)> = Vec::new();
    let mut ranges: Vec<Range> = Vec::with_capacity(g.nodes.len());
    // Whether a node's integer form needs `mod 2^n` to stay exact.
    let mut wraps: Vec<bool> = Vec::with_capacity(g.nodes.len());
    let mut exprs: Vec<String> = Vec::with_capacity(g.nodes.len());
    let mut body = String::new();
    let mut side = String::new();
    let mut abstract_funs: HashMap<String, (usize, u32)> = HashMap::new();
    let mut abstracted = false;
    // Nodes that depend on an abstracted operation.
    let mut tainted: Vec<bool> = Vec::with_capacity(g.nodes.len());

    for (id, n) in g.nodes.iter().enumerate() {
        let w = n.sort.width().unwrap_or(0);
        let top = if w > 0 {
            pow2(w) - 1u32
        } else {
            BigUint::zero()
        };
        let full = Range {
            lo: BigUint::zero(),
            hi: top.clone(),
        };
        let a = |k: usize| -> &str { &exprs[n.args[k]] };
        let r = |k: usize| -> &Range { &ranges[n.args[k]] };
        let m = pow2(w);
        let mut wrap = false;
        let mut needs_range = false;
        let mut abs_here = false;
        let (expr, range): (String, Range) = match &n.op {
            Op::Lit(v) => (
                v.to_string(),
                Range {
                    lo: v.clone(),
                    hi: v.clone(),
                },
            ),
            Op::Bool(b) => (b.to_string(), full.clone()),
            Op::Var(name) => (name.clone(), full.clone()),
            Op::Fun(name) => {
                needs_range = w > 0;
                (call(name, &n.args, &exprs), full.clone())
            }
            Op::ConstArray => (
                format!("((as const {}) {})", n.sort.int(), a(0)),
                full.clone(),
            ),
            Op::Extract(hi, lo) => {
                let x = &ranges[n.args[0]];
                let width = hi - lo + 1;
                let shifted_hi = &x.hi >> *lo;
                if *lo == 0 && x.hi < pow2(width) {
                    (a(0).to_string(), x.clone())
                } else {
                    let base = if *lo == 0 {
                        a(0).to_string()
                    } else {
                        format!("(div {} {})", a(0), pow2(*lo))
                    };
                    if shifted_hi < pow2(width) {
                        (
                            base,
                            Range {
                                lo: BigUint::zero(),
                                hi: shifted_hi,
                            },
                        )
                    } else {
                        (format!("(mod {base} {})", pow2(width)), full.clone())
                    }
                }
            }
            Op::ZeroExt(_) => (a(0).to_string(), r(0).clone()),
            Op::SignExt(k) => {
                let iw = w - k;
                if r(0).hi < pow2(iw - 1) {
                    (a(0).to_string(), r(0).clone())
                } else {
                    (
                        format!(
                            "(ite (>= {x} {h}) (+ {x} {d}) {x})",
                            x = a(0),
                            h = pow2(iw - 1),
                            d = pow2(w) - pow2(iw)
                        ),
                        full.clone(),
                    )
                }
            }
            Op::Evm(name) => {
                let (op, _) = evm_op(name).unwrap();
                match divide_by_nonzero(&op, a(0), a(1), r(0), r(1)) {
                    Some(x) => x,
                    None => evm_expr(&op, w, a(0), a(1), r(0), r(1), &full),
                }
            }
            Op::Prim(p) => match p.as_str() {
                "=" | "distinct" | "and" | "or" | "xor" | "=>" | "not" | "ite" | "select"
                | "store" => {
                    let e = call(p, &n.args, &exprs);
                    if p == "select" && w > 0 {
                        needs_range = true;
                    }
                    let range = if p == "ite" && w > 0 {
                        Range {
                            lo: r(1).lo.clone().min(r(2).lo.clone()),
                            hi: r(1).hi.clone().max(r(2).hi.clone()),
                        }
                    } else {
                        full.clone()
                    };
                    (e, range)
                }
                "bvule" => (format!("(<= {} {})", a(0), a(1)), full.clone()),
                "bvult" => (format!("(< {} {})", a(0), a(1)), full.clone()),
                "bvuge" => (format!("(>= {} {})", a(0), a(1)), full.clone()),
                "bvugt" => (format!("(> {} {})", a(0), a(1)), full.clone()),
                "bvsle" | "bvslt" | "bvsge" | "bvsgt" => {
                    let aw = g.sort(n.args[0]).width().unwrap();
                    let rel = match p.as_str() {
                        "bvsle" => "<=",
                        "bvslt" => "<",
                        "bvsge" => ">=",
                        _ => ">",
                    };
                    (
                        format!("({rel} {} {})", signed(a(0), aw), signed(a(1), aw)),
                        full.clone(),
                    )
                }
                "bvadd" => {
                    // Halmos writes a - b as a + (2^n - 1) * b. When the facts
                    // show the negated terms sum to at most the others, the
                    // value is the plain difference, with no mod.
                    let neg: Vec<usize> = n.args.iter().filter_map(|&x| negated(g, x)).collect();
                    let pos: Vec<usize> = n
                        .args
                        .iter()
                        .copied()
                        .filter(|&x| negated(g, x).is_none())
                        .collect();
                    let sum = |ts: &[usize], f: fn(&Range) -> &BigUint| -> BigUint {
                        ts.iter().map(|&t| f(&ranges[t]).clone()).sum()
                    };
                    let (pos_lo, pos_hi) = (sum(&pos, |r| &r.lo), sum(&pos, |r| &r.hi));
                    let (neg_lo, neg_hi) = (sum(&neg, |r| &r.lo), sum(&neg, |r| &r.hi));
                    let nonzero: Vec<usize> = neg
                        .iter()
                        .copied()
                        .filter(|&y| !ranges[y].hi.is_zero())
                        .collect();
                    // The same negated terms as a difference already shown not
                    // to wrap, and more positive ones: that difference plus
                    // them (`totalAssets() + 1` after `totalAssets()`). Exact,
                    // and it keeps that difference's bounds.
                    let extends = if neg.is_empty() {
                        None
                    } else {
                        proven.iter().find_map(|(e, pp, pn)| {
                            let same = within(&nonzero, pn) && within(pn, &nonzero);
                            if !same || !within(pp, &pos) {
                                return None;
                            }
                            let mut extra = pos.clone();
                            for &t in pp {
                                take(&mut extra, t);
                            }
                            let hi = &ranges[*e].hi + sum(&extra, |r| &r.hi);
                            (hi < m).then(|| {
                                let lo = &ranges[*e].lo + sum(&extra, |r| &r.lo);
                                let mut terms = vec![exprs[*e].clone()];
                                terms.extend(extra.iter().map(|&t| exprs[t].clone()));
                                let expr = if terms.len() == 1 {
                                    terms.pop().unwrap()
                                } else {
                                    format!("(+ {})", terms.join(" "))
                                };
                                (expr, Range { lo, hi })
                            })
                        })
                    };
                    // A difference is exact only while it stays in [0, 2^n):
                    // the facts that showed it does are about its bit-vector
                    // value, and once it is written as `p - n`, a fact like
                    // solc's `p - n <= p` holds for any n. So assert the range
                    // (every bit-vector model meets it), or the integer query
                    // gains models the bit-vector one does not have.
                    if let Some(x) = extends {
                        proven.push((id, pos.clone(), nonzero));
                        needs_range = true;
                        x
                    } else if !neg.is_empty()
                        && pos_hi < m
                        && neg_hi < m
                        && covered(g, &facts, &order, &ranges, &proven, id, &pos, &neg, &m)
                    {
                        proven.push((id, pos.clone(), nonzero));
                        needs_range = true;
                        let lo = if pos_lo >= neg_hi {
                            &pos_lo - &neg_hi
                        } else {
                            BigUint::zero()
                        };
                        let hi = if pos_hi >= neg_lo {
                            &pos_hi - &neg_lo
                        } else {
                            BigUint::zero()
                        };
                        let plus = |ts: &[usize]| -> String {
                            match ts {
                                [] => "0".to_string(),
                                [t] => exprs[*t].clone(),
                                _ => call("+", ts, &exprs),
                            }
                        };
                        (
                            format!("(- {} {})", plus(&pos), plus(&neg)),
                            Range { lo, hi },
                        )
                    } else {
                        let hi: BigUint = n.args.iter().map(|&x| ranges[x].hi.clone()).sum();
                        let lo: BigUint = n.args.iter().map(|&x| ranges[x].lo.clone()).sum();
                        let s = call("+", &n.args, &exprs);
                        if hi < m {
                            (s, Range { lo, hi })
                        } else {
                            wrap = true;
                            (format!("(mod {s} {m})"), full.clone())
                        }
                    }
                }
                "bvsub" => {
                    let (x, y) = (n.args[0], n.args[1]);
                    let ordered = order.le(y, x) || r(0).lo >= r(1).hi;
                    if ordered {
                        let hi = if r(0).hi >= r(1).lo {
                            &r(0).hi - &r(1).lo
                        } else {
                            BigUint::zero()
                        };
                        let lo = if r(0).lo >= r(1).hi {
                            &r(0).lo - &r(1).hi
                        } else {
                            BigUint::zero()
                        };
                        needs_range = true;
                        (format!("(- {} {})", a(0), a(1)), Range { lo, hi })
                    } else {
                        wrap = true;
                        (
                            format!("(mod (+ (- {} {}) {m}) {m})", a(0), a(1)),
                            full.clone(),
                        )
                    }
                }
                "bvneg" => {
                    wrap = true;
                    (format!("(mod (- {m} {}) {m})", a(0)), full.clone())
                }
                "bvnot" => (format!("(- {top} {})", a(0)), full.clone()),
                "bvmul" => {
                    // A constant above 2^(n-1) is a negative one: c * x is -(2^n - c) * x
                    // modulo 2^n, which keeps the coefficient small.
                    let half = pow2(w - 1);
                    let negative = n
                        .args
                        .iter()
                        .position(|&x| lit(g, x).is_some_and(|c| *c > half));
                    if let (Some(k), 2) = (negative, n.args.len()) {
                        wrap = true;
                        let c = lit(g, n.args[k]).unwrap();
                        let other = &exprs[n.args[1 - k]];
                        let neg = &m - c;
                        if neg.is_one() {
                            (format!("(mod (- {m} {other}) {m})"), full.clone())
                        } else {
                            (format!("(mod (- (* {neg} {other})) {m})"), full.clone())
                        }
                    } else {
                        let hi: BigUint = n
                            .args
                            .iter()
                            .fold(BigUint::one(), |acc, &x| acc * &ranges[x].hi);
                        let lo: BigUint = n
                            .args
                            .iter()
                            .fold(BigUint::one(), |acc, &x| acc * &ranges[x].lo);
                        let s = call("*", &n.args, &exprs);
                        if hi < m {
                            (s, Range { lo, hi })
                        } else {
                            wrap = true;
                            (format!("(mod {s} {m})"), full.clone())
                        }
                    }
                }
                "bvudiv" | "bvurem" if divide_by_nonzero(p, a(0), a(1), r(0), r(1)).is_some() => {
                    divide_by_nonzero(p, a(0), a(1), r(0), r(1)).unwrap()
                }
                "bvudiv" => {
                    if r(1).lo >= BigUint::one() {
                        (
                            format!("(div {} {})", a(0), a(1)),
                            Range {
                                lo: BigUint::zero(),
                                hi: r(0).hi.clone(),
                            },
                        )
                    } else {
                        (
                            format!("(ite (= {y} 0) {top} (div {x} {y}))", x = a(0), y = a(1)),
                            full.clone(),
                        )
                    }
                }
                "bvurem" => {
                    let hi = if r(1).lo >= BigUint::one() {
                        r(0).hi.clone().min(&r(1).hi - 1u32)
                    } else {
                        r(0).hi.clone()
                    };
                    (
                        format!("(ite (= {y} 0) {x} (mod {x} {y}))", x = a(0), y = a(1)),
                        Range {
                            lo: BigUint::zero(),
                            hi,
                        },
                    )
                }
                "bvshl" | "bvlshr" if lit(g, n.args[1]).is_some() => {
                    let s = lit(g, n.args[1]).unwrap().to_u32().unwrap_or(u32::MAX);
                    if s >= w {
                        (
                            "0".into(),
                            Range {
                                lo: BigUint::zero(),
                                hi: BigUint::zero(),
                            },
                        )
                    } else if p == "bvlshr" {
                        (
                            format!("(div {} {})", a(0), pow2(s)),
                            Range {
                                lo: BigUint::zero(),
                                hi: &r(0).hi >> s,
                            },
                        )
                    } else {
                        let hi = &r(0).hi << s;
                        let e = format!("(* {} {})", a(0), pow2(s));
                        if hi < m {
                            (
                                e,
                                Range {
                                    lo: BigUint::zero(),
                                    hi,
                                },
                            )
                        } else {
                            wrap = true;
                            (format!("(mod {e} {m})"), full.clone())
                        }
                    }
                }
                "bvand" | "bvor" | "bvxor" if n.args.len() == 2 => {
                    match bitwise(p, n.args[0], n.args[1], g, &exprs, &ranges, w) {
                        Some(x) => x,
                        None => {
                            abstracted = true;
                            abs_here = true;
                            needs_range = true;
                            let f = format!("ausweg_{p}_{w}");
                            abstract_funs.insert(f.clone(), (2, w));
                            (call(&f, &n.args, &exprs), full.clone())
                        }
                    }
                }
                "bvcomp" => (
                    format!("(ite (= {} {}) 1 0)", a(0), a(1)),
                    Range {
                        lo: BigUint::zero(),
                        hi: BigUint::one(),
                    },
                ),
                "concat" if n.args.len() == 2 && lit(g, n.args[0]).is_some_and(|v| v.is_zero()) => {
                    // Zero-extension written as a concat.
                    (a(1).to_string(), r(1).clone())
                }
                "concat" => {
                    let mut e = exprs[n.args[0]].clone();
                    let mut hi = ranges[n.args[0]].hi.clone();
                    for &x in &n.args[1..] {
                        let xw = g.sort(x).width().unwrap();
                        e = format!("(+ (* {e} {}) {})", pow2(xw), exprs[x]);
                        hi = (hi << xw) + &ranges[x].hi;
                    }
                    (
                        e,
                        Range {
                            lo: BigUint::zero(),
                            hi,
                        },
                    )
                }
                other => {
                    // Anything else (signed division, arithmetic shifts, rotations):
                    // an uninterpreted function, which keeps `unsat` sound.
                    abstracted = true;
                    abs_here = true;
                    needs_range = w > 0;
                    let f = format!("ausweg_{}_{w}", other.replace(['-', '.'], "_"));
                    abstract_funs.insert(f.clone(), (n.args.len(), w));
                    (call(&f, &n.args, &exprs), full.clone())
                }
            },
        };
        let mut range = range;
        if let Some(h) = facts.hi.get(&id)
            && *h < range.hi
        {
            range.hi = h.clone();
        }
        if let Some(l) = facts.lo.get(&id)
            && *l > range.lo
        {
            range.lo = l.clone();
        }
        let _ = wrap;
        // Leaves stay inline; everything else gets a name, so shared subterms
        // are written once.
        let leaf = matches!(n.op, Op::Lit(_) | Op::Bool(_) | Op::Var(_));
        let e = if leaf {
            expr
        } else {
            let name = format!("_n{id}");
            let _ = writeln!(body, "(define-fun {name} () {} {expr})", n.sort.int());
            name
        };
        if needs_range {
            let _ = writeln!(side, "(assert (and (<= 0 {e}) (<= {e} {top})))");
        }
        tainted.push(abs_here || n.args.iter().any(|&x| tainted[x]));
        exprs.push(e);
        ranges.push(range);
        wraps.push(wrap);
    }

    // Declarations, in the original order.
    let mut out = String::from("(set-option :produce-models true)\n(set-logic ALL)\n");
    let mut model_vars = Vec::new();
    for name in &g.decl_order {
        if let Some(sort) = g.consts.get(name) {
            let _ = writeln!(out, "(declare-fun {name} () {})", sort.int());
            if let Sort::Bv(w) = sort {
                let _ = writeln!(
                    out,
                    "(assert (and (<= 0 {name}) (<= {name} {})))",
                    pow2(*w) - 1u32
                );
                if name.starts_with("p_") || name.starts_with("halmos_") {
                    model_vars.push((name.clone(), *w));
                }
            }
        } else if let Some((ps, ret)) = g.funs.get(name) {
            if evm_op(name).is_some() {
                continue;
            }
            let ps: Vec<String> = ps.iter().map(|p| p.int()).collect();
            let _ = writeln!(out, "(declare-fun {name} ({}) {})", ps.join(" "), ret.int());
        }
    }
    let mut abs: Vec<_> = abstract_funs.into_iter().collect();
    abs.sort();
    for (f, (arity, _)) in abs {
        let _ = writeln!(
            out,
            "(declare-fun {f} ({}) Int)",
            vec!["Int"; arity].join(" ")
        );
    }
    out.push_str(&body);
    out.push_str(&side);
    let mut relaxed = out.clone();
    let mut dropped = 0;
    for &a in &g.asserts {
        let line = format!("(assert {})\n", exprs[a]);
        out.push_str(&line);
        if tainted[a] {
            dropped += 1;
        } else {
            relaxed.push_str(&line);
        }
    }
    out.push_str("(check-sat)\n");
    relaxed.push_str("(check-sat)\n");
    if !model_vars.is_empty() {
        let names: Vec<&str> = model_vars.iter().map(|(n, _)| n.as_str()).collect();
        let _ = writeln!(out, "(get-value ({}))", names.join(" "));
    }
    Translation {
        script: out,
        relaxed: (dropped > 0).then_some(relaxed),
        abstracted,
        model_vars,
    }
}

fn call(f: &str, args: &[usize], exprs: &[String]) -> String {
    if args.is_empty() {
        return f.to_string();
    }
    let mut s = format!("({f}");
    for &a in args {
        s.push(' ');
        s.push_str(&exprs[a]);
    }
    s.push(')');
    s
}

fn signed(x: &str, w: u32) -> String {
    format!("(ite (>= {x} {}) (- {x} {}) {x})", pow2(w - 1), pow2(w))
}

/// Division and remainder by a divisor known to be nonzero, where the
/// zero case of the EVM and of SMT-LIB never arises. A remainder by more than
/// the dividend can reach is the dividend itself; a quotient is then 0.
fn divide_by_nonzero(
    op: &str,
    x: &str,
    y: &str,
    rx: &Range,
    ry: &Range,
) -> Option<(String, Range)> {
    if ry.lo.is_zero() {
        return None;
    }
    let zero = BigUint::zero();
    match op {
        "bvudiv" if rx.hi < ry.lo => Some((
            "0".into(),
            Range {
                lo: zero.clone(),
                hi: zero,
            },
        )),
        "bvudiv" => Some((
            format!("(div {x} {y})"),
            Range {
                lo: &rx.lo / &ry.hi.clone().max(BigUint::one()),
                hi: &rx.hi / &ry.lo,
            },
        )),
        "bvurem" if rx.hi < ry.lo => Some((x.to_string(), rx.clone())),
        "bvurem" => Some((
            format!("(mod {x} {y})"),
            Range {
                lo: zero,
                hi: rx.hi.clone().min(&ry.hi - 1u32),
            },
        )),
        _ => None,
    }
}

fn evm_expr(
    op: &str,
    w: u32,
    x: &str,
    y: &str,
    rx: &Range,
    ry: &Range,
    full: &Range,
) -> (String, Range) {
    let m = pow2(w);
    match op {
        "bvmul" => {
            let hi = &rx.hi * &ry.hi;
            if hi < m {
                (
                    format!("(* {x} {y})"),
                    Range {
                        lo: &rx.lo * &ry.lo,
                        hi,
                    },
                )
            } else {
                (format!("(mod (* {x} {y}) {m})"), full.clone())
            }
        }
        "bvudiv" => (
            format!("(ite (= {y} 0) 0 (div {x} {y}))"),
            Range {
                lo: BigUint::zero(),
                hi: rx.hi.clone(),
            },
        ),
        "bvurem" => (
            format!("(ite (= {y} 0) 0 (mod {x} {y}))"),
            Range {
                lo: BigUint::zero(),
                hi: if ry.hi.is_zero() {
                    BigUint::zero()
                } else {
                    rx.hi.clone().min(&ry.hi - 1u32)
                },
            },
        ),
        "bvsdiv" | "bvsrem" => {
            let (sx, sy) = (signed(x, w), signed(y, w));
            let ax = format!("(abs {sx})");
            let ay = format!("(abs {sy})");
            let e = if op == "bvsdiv" {
                format!(
                    "(ite (= {y} 0) 0 (mod (+ (ite (>= (* {sx} {sy}) 0) (div {ax} {ay}) (- (div {ax} {ay}))) {m}) {m}))"
                )
            } else {
                format!(
                    "(ite (= {y} 0) 0 (mod (+ (ite (>= {sx} 0) (mod {ax} {ay}) (- (mod {ax} {ay}))) {m}) {m}))"
                )
            };
            (e, full.clone())
        }
        _ => unreachable!(),
    }
}

/// Exact integer forms of `and`, `or` and `xor` in the cases EVM code produces:
/// a mask with a constant, or two flags that are 0 or 1.
fn bitwise(
    p: &str,
    x: usize,
    y: usize,
    g: &Graph,
    exprs: &[String],
    ranges: &[Range],
    w: u32,
) -> Option<(String, Range)> {
    let top = pow2(w) - 1u32;
    let zero = || Range {
        lo: BigUint::zero(),
        hi: BigUint::zero(),
    };
    for (c, v) in [(x, y), (y, x)] {
        let Some(k) = lit(g, c) else { continue };
        let ve = &exprs[v];
        let vr = &ranges[v];
        match p {
            "bvand" => {
                if k.is_zero() {
                    return Some(("0".into(), zero()));
                }
                if *k == top {
                    return Some((ve.clone(), vr.clone()));
                }
                let k1 = k + 1u32;
                if (k & &k1).is_zero() {
                    // Low mask 2^b - 1.
                    if vr.hi < k1 {
                        return Some((ve.clone(), vr.clone()));
                    }
                    return Some((
                        format!("(mod {ve} {k1})"),
                        Range {
                            lo: BigUint::zero(),
                            hi: k.clone(),
                        },
                    ));
                }
                let low = &top - k;
                let low1 = &low + 1u32;
                if (&low & &low1).is_zero() {
                    // High mask: clears the low bits.
                    return Some((
                        format!("(- {ve} (mod {ve} {low1}))"),
                        Range {
                            lo: BigUint::zero(),
                            hi: vr.hi.clone(),
                        },
                    ));
                }
            }
            "bvor" | "bvxor" if k.is_zero() => return Some((ve.clone(), vr.clone())),
            _ => {}
        }
    }
    let one = BigUint::one();
    if ranges[x].hi <= one && ranges[y].hi <= one {
        let (a, b) = (&exprs[x], &exprs[y]);
        let e = match p {
            "bvand" => format!("(* {a} {b})"),
            "bvor" => format!("(- (+ {a} {b}) (* {a} {b}))"),
            _ => format!("(mod (+ {a} {b}) 2)"),
        };
        return Some((
            e,
            Range {
                lo: BigUint::zero(),
                hi: one,
            },
        ));
    }
    None
}

// ---------------------------------------------------------------- solving

#[derive(Debug, PartialEq)]
pub enum Answer {
    Unsat,
    /// Model values for Halmos's variables: (name, width, value).
    Sat(Vec<(String, u32, BigUint)>),
    Unknown,
}

fn find_on_path(name: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join(name))
        .find(|p| p.is_file())
}

fn halmos_solver(name: &str) -> Option<PathBuf> {
    let home = std::env::var_os("HOME")?;
    let p = Path::new(&home).join(".halmos").join("solvers").join(name);
    p.is_file().then_some(p)
}

/// The integer solver: `AUSWEG_SMT_SOLVER`, else z3 on the PATH, else cvc5.
fn int_solver(timeout: Duration) -> Option<Vec<String>> {
    let secs = timeout.as_secs().max(1);
    if let Ok(cmd) = std::env::var("AUSWEG_SMT_SOLVER") {
        return Some(cmd.split_whitespace().map(String::from).collect());
    }
    if let Some(z3) = find_on_path("z3") {
        return Some(vec![
            z3.display().to_string(),
            "-smt2".into(),
            format!("-T:{secs}"),
        ]);
    }
    let cvc5 = find_on_path("cvc5").or_else(|| halmos_solver("cvc5"))?;
    Some(vec![
        cvc5.display().to_string(),
        "--lang=smt2".into(),
        format!("--tlimit={}", secs * 1000),
    ])
}

/// z3's general solver answers most of these queries in well under a second,
/// but stalls on some nonlinear ones that its `qfnia` tactic answers at once,
/// and the other way round. With z3, try the general solver for 2 s, then
/// `qfnia` for half of what is left, then the general solver again.
fn staged(script: &str, budget: Duration) -> String {
    let z3 = std::env::var_os("AUSWEG_SMT_SOLVER").is_none() && find_on_path("z3").is_some();
    if !z3 {
        return script.to_string();
    }
    let ms = budget.as_millis() as u64;
    let quick = 2000.min(ms / 4).max(100);
    let middle = (ms.saturating_sub(quick) / 2).max(100);
    script.replacen(
        "(check-sat)",
        &format!("(check-sat-using (or-else (try-for smt {quick}) (try-for qfnia {middle}) smt))"),
        1,
    )
}

/// Whether a script needs a solver in incremental mode: assertion scopes, or
/// more than one `check-sat`. yices without `--incremental` ignores `push` and
/// `pop` and answers as if every assertion held.
fn needs_incremental(cmds: &[Sexp]) -> bool {
    fn head(c: &Sexp) -> Option<&str> {
        c.list().and_then(|l| l.first()).and_then(|h| h.atom())
    }
    let mut check_sats = 0;
    for c in cmds {
        match head(c) {
            Some("push" | "pop") => return true,
            Some("check-sat") => check_sats += 1,
            _ => {}
        }
    }
    check_sats > 1
}

/// yices as Halmos runs it, so Halmos can read its model: without
/// `--smt2-model-format` yices writes `(= x #b10)`, which Halmos does not read,
/// and a counterexample would come back with no values.
fn yices(path: &Path, secs: u64, incremental: bool) -> Vec<String> {
    let mut cmd = vec![
        path.display().to_string(),
        format!("--timeout={secs}"),
        "--smt2-model-format".into(),
        "--bvconst-in-decimal".into(),
    ];
    if incremental {
        cmd.push("--incremental".into());
    }
    cmd
}

/// A bit-vector solver for answers the integer query cannot settle:
/// `AUSWEG_SMT_FALLBACK`, else yices, else bitwuzla. A script that needs
/// incremental mode gets yices with `--incremental`, or z3, which reads scopes
/// natively.
fn bv_solver(timeout: Duration, incremental: bool) -> Option<Vec<String>> {
    let secs = timeout.as_secs().max(1);
    if let Ok(cmd) = std::env::var("AUSWEG_SMT_FALLBACK") {
        return Some(cmd.split_whitespace().map(String::from).collect());
    }
    if let Some(y) = find_on_path("yices-smt2").or_else(|| halmos_solver("yices-smt2")) {
        return Some(yices(&y, secs, incremental));
    }
    if incremental {
        let z3 = find_on_path("z3")?;
        return Some(vec![z3.display().to_string(), format!("-T:{secs}")]);
    }
    let b = find_on_path("bitwuzla").or_else(|| halmos_solver("bitwuzla"))?;
    Some(vec![
        b.display().to_string(),
        "--produce-models".into(),
        format!("--time-limit={}", secs * 1000),
    ])
}

fn run(cmd: &[String], file: &Path) -> Result<String> {
    let out = Command::new(&cmd[0])
        .args(&cmd[1..])
        .arg(file)
        .output()
        .with_context(|| format!("running {}", cmd[0]))?;
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

fn parse_values(out: &str, vars: &[(String, u32)]) -> Option<Vec<(String, u32, BigUint)>> {
    let rest = out.trim_start().strip_prefix("sat")?;
    let sexps = parse_sexps(rest).ok()?;
    let mut vals = HashMap::new();
    for s in sexps {
        for pair in s.list().unwrap_or(&[]) {
            if let Some([Sexp::Atom(name), v]) = pair.list()
                && let Some(a) = v.atom()
                && let Some(n) = BigUint::parse_bytes(a.as_bytes(), 10)
            {
                vals.insert(name.clone(), n);
            }
        }
    }
    Some(
        vars.iter()
            .map(|(n, w)| (n.clone(), *w, vals.get(n).cloned().unwrap_or_default()))
            .collect(),
    )
}

/// Solves a Halmos query file. Returns the answer and, for the fallback, the
/// bit-vector solver's own output to pass through.
pub fn solve(file: &Path, timeout: Duration) -> Result<(Answer, Option<String>)> {
    let src =
        std::fs::read_to_string(file).with_context(|| format!("reading {}", file.display()))?;
    let cmds = parse_sexps(&src);
    let incremental = cmds.as_ref().is_ok_and(|cs| needs_incremental(cs));
    let translated = cmds.and_then(|cmds| {
        let mut g = Graph::default();
        for c in &cmds {
            g.command(c)?;
        }
        Ok(translate(&g))
    });
    // Every solver call shares one budget, so Halmos never has to kill us.
    let deadline = std::time::Instant::now() + timeout;
    let remaining = || {
        deadline
            .saturating_duration_since(std::time::Instant::now())
            .max(Duration::from_secs(1))
    };
    let fallback = |reason: &str| -> Result<(Answer, Option<String>)> {
        let _ = reason;
        match bv_solver(remaining(), incremental) {
            Some(cmd) => {
                let out = run(&cmd, file)?;
                let first = out.lines().next().unwrap_or("").trim();
                let a = match first {
                    "unsat" => Answer::Unsat,
                    "sat" => Answer::Sat(Vec::new()),
                    _ => Answer::Unknown,
                };
                Ok((a, Some(out)))
            }
            None => Ok((Answer::Unknown, None)),
        }
    };
    let t = match translated {
        Ok(t) => t,
        Err(e) => return fallback(&e.to_string()),
    };
    let int_file = file.with_extension("int.smt2");
    std::fs::write(&int_file, &t.script)?;
    if int_solver(timeout).is_none() {
        return fallback("no integer solver (install z3)");
    }
    // Paths through code ausweg abstracts (OpenZeppelin's 512-bit mulDiv branch)
    // are usually infeasible for reasons that do not need that code: try the
    // query without it first.
    if let Some(relaxed) = &t.relaxed {
        let quick = Duration::from_secs((timeout.as_secs() / 3).max(1));
        let rel_file = file.with_extension("relaxed.smt2");
        std::fs::write(&rel_file, staged(relaxed, quick))?;
        let out = run(&int_solver(quick).unwrap(), &rel_file)?;
        if out.lines().next().map(str::trim) == Some("unsat") {
            return Ok((Answer::Unsat, None));
        }
    }
    let left = remaining();
    std::fs::write(&int_file, staged(&t.script, left))?;
    let out = run(&int_solver(left).unwrap(), &int_file)?;
    let first = out.lines().next().unwrap_or("").trim().to_string();
    match first.as_str() {
        "unsat" => Ok((Answer::Unsat, None)),
        "sat" if !t.abstracted => match parse_values(&out, &t.model_vars) {
            Some(v) => Ok((Answer::Sat(v), None)),
            None => fallback("unreadable model"),
        },
        // The model may use an abstracted operation wrongly: let a bit-vector
        // solver decide.
        "sat" => fallback("sat with abstractions"),
        // Out of time: a bit-vector solver would not do better.
        _ => Ok((Answer::Unknown, None)),
    }
}

/// What Halmos reads: `sat` with a bit-vector model, `unsat`, or `unknown`.
pub fn render(answer: &Answer, passthrough: Option<&str>) -> String {
    if let Some(p) = passthrough {
        return if p.trim().is_empty() {
            "unknown\n".into()
        } else {
            p.to_string()
        };
    }
    match answer {
        Answer::Unsat => "unsat\n".into(),
        Answer::Unknown => "unknown\n".into(),
        Answer::Sat(vals) => {
            let mut s = String::from("sat\n(\n");
            for (name, w, v) in vals {
                let lit = if w % 4 == 0 {
                    format!(
                        "#x{:0>width$}",
                        v.to_str_radix(16),
                        width = (*w / 4) as usize
                    )
                } else {
                    format!("#b{:0>width$}", v.to_str_radix(2), width = *w as usize)
                };
                let _ = writeln!(s, "  (define-fun {name} () (_ BitVec {w}) {lit})");
            }
            s.push_str(")\n");
            s
        }
    }
}

/// `ausweg smt <file>`: the answer for Halmos, on stdout.
pub fn main(file: &Path) -> Result<()> {
    let secs = std::env::var("AUSWEG_SMT_TIMEOUT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(60);
    let (answer, passthrough) = solve(file, Duration::from_secs(secs))?;
    print!("{}", render(&answer, passthrough.as_deref()));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn translate_src(src: &str) -> Translation {
        let mut g = Graph::default();
        for c in parse_sexps(src).unwrap() {
            g.command(&c).unwrap();
        }
        translate(&g)
    }

    /// What reading the script's commands says: the first refusal, if any.
    fn read(src: &str) -> std::result::Result<(), String> {
        let mut g = Graph::default();
        for c in parse_sexps(src).unwrap() {
            g.command(&c).map_err(|e| e.to_string())?;
        }
        Ok(())
    }

    #[test]
    fn refuses_assertion_scopes_and_second_check_sats() {
        // x = 1 is popped before the check: the query is sat (x = 2). Read as
        // if push and pop were not there, it would be unsat.
        let scoped = "(declare-fun x () (_ BitVec 8))\n(push 1)\n(assert (= x #x01))\n(pop 1)\n\
                      (assert (= x #x02))\n(check-sat)";
        assert_eq!(
            read(scoped).unwrap_err(),
            "push: assertion scopes are not translated"
        );
        let twice =
            "(declare-fun x () (_ BitVec 8))\n(check-sat)\n(assert (= x #x01))\n(check-sat)";
        assert!(
            read(twice)
                .unwrap_err()
                .starts_with("more than one check-sat")
        );
        let once = "(declare-fun x () (_ BitVec 8))\n(assert (= x #x01))\n(check-sat)\n(get-model)";
        assert!(read(once).is_ok());
        // yices is run the way Halmos runs it, so Halmos can read its models.
        let y = yices(Path::new("yices-smt2"), 7, true);
        assert_eq!(
            y,
            [
                "yices-smt2",
                "--timeout=7",
                "--smt2-model-format",
                "--bvconst-in-decimal",
                "--incremental"
            ]
        );
        // Both refused scripts go to a solver in incremental mode; a plain one does not.
        assert!(needs_incremental(&parse_sexps(scoped).unwrap()));
        assert!(needs_incremental(&parse_sexps(twice).unwrap()));
        assert!(!needs_incremental(&parse_sexps(once).unwrap()));
    }

    #[test]
    fn parses_nested_lists_and_comments() {
        let s = parse_sexps("; c\n(a (b #x0f) |q r|)").unwrap();
        assert_eq!(
            s,
            vec![Sexp::List(vec![
                Sexp::Atom("a".into()),
                Sexp::List(vec![Sexp::Atom("b".into()), Sexp::Atom("#x0f".into())]),
                Sexp::Atom("|q r|".into()),
            ])]
        );
    }

    #[test]
    fn bounded_product_needs_no_mod() {
        let t = translate_src(
            "(declare-fun x () (_ BitVec 256))\n(declare-fun y () (_ BitVec 256))\n\
             (assert (bvule x (_ bv100 256)))\n(assert (bvule y (_ bv100 256)))\n\
             (assert (= (bvmul x y) (_ bv7 256)))",
        );
        assert!(t.script.contains("(* x y)"), "{}", t.script);
        assert!(!t.script.contains("(mod (* x y)"), "{}", t.script);
        assert!(!t.abstracted);
    }

    #[test]
    fn unbounded_sum_wraps() {
        let t = translate_src(
            "(declare-fun x () (_ BitVec 8))\n(assert (= (bvadd x (_ bv1 8)) (_ bv0 8)))",
        );
        assert!(t.script.contains("(mod (+ x 1) 256)"), "{}", t.script);
    }

    #[test]
    fn checked_subtraction_needs_no_mod() {
        let t = translate_src(
            "(declare-fun x () (_ BitVec 256))\n(declare-fun y () (_ BitVec 256))\n\
             (assert (not (bvult x y)))\n(assert (= (bvsub x y) (_ bv3 256)))",
        );
        assert!(t.script.contains("(- x y)"), "{}", t.script);
        assert!(!t.script.contains("(mod (+ (- x y)"), "{}", t.script);
    }

    const NEG1: &str =
        "(_ bv115792089237316195423570985008687907853269984665640564039457584007913129639935 256)";

    #[test]
    fn halmos_subtraction_needs_no_mod_when_ordered() {
        // x - y as Halmos writes it, after a checked subtraction's y <= x.
        let t = translate_src(&format!(
            "(declare-fun x () (_ BitVec 256))\n(declare-fun y () (_ BitVec 256))\n\
             (assert (bvule y x))\n(assert (= (bvadd x (bvmul {NEG1} y)) (_ bv3 256)))"
        ));
        assert!(t.script.contains("(- x y)"), "{}", t.script);
        assert!(!t.script.contains("(mod (+ x"), "{}", t.script);
    }

    #[test]
    fn solc_checked_subtraction_needs_no_mod() {
        // diff := sub(x, y); if gt(diff, x) { panic }: the path asserts diff <= x.
        let t = translate_src(&format!(
            "(declare-fun x () (_ BitVec 256))\n(declare-fun y () (_ BitVec 256))\n\
             (assert (bvule (bvadd x (bvmul {NEG1} y)) x))\n\
             (assert (= (bvadd x (bvmul {NEG1} y)) (_ bv3 256)))"
        ));
        assert!(t.script.contains("(- x y)"), "{}", t.script);
        assert!(!t.script.contains("(mod (+ x"), "{}", t.script);
    }

    #[test]
    fn a_proven_difference_covers_a_larger_one() {
        // b - a - c checked, then 1 + b - a - c (OpenZeppelin's totalAssets() + 1).
        let t = translate_src(&format!(
            "(declare-fun a () (_ BitVec 256))\n(declare-fun b () (_ BitVec 256))\n(declare-fun c () (_ BitVec 256))\n\
             (assert (bvule a (_ bv1000 256)))\n(assert (bvule b (_ bv1000 256)))\n(assert (bvule c (_ bv1000 256)))\n\
             (assert (bvule (bvadd b (bvmul {NEG1} a)) b))\n\
             (assert (bvule (bvadd b (bvmul {NEG1} a) (bvmul {NEG1} c)) (bvadd b (bvmul {NEG1} a))))\n\
             (assert (= (bvadd (_ bv1 256) b (bvmul {NEG1} a) (bvmul {NEG1} c)) (_ bv5 256)))"
        ));
        // b - a - c is shown not to wrap; 1 + b - a - c is that plus 1.
        assert!(t.script.contains("(- b (+ a c))"), "{}", t.script);
        assert!(t.script.contains("Int (+ _n12 1))"), "{}", t.script);
        assert!(!t.script.contains("(mod (+ 1 b"), "{}", t.script);
        // Two unbounded negated terms may sum past 2^256, and then diff <= x
        // proves nothing: the mod stays.
        let u = translate_src(&format!(
            "(declare-fun a () (_ BitVec 256))\n(declare-fun b () (_ BitVec 256))\n(declare-fun c () (_ BitVec 256))\n\
             (assert (bvule b (_ bv1000 256)))\n\
             (assert (bvule (bvadd b (bvmul {NEG1} a) (bvmul {NEG1} c)) b))\n\
             (assert (= (bvadd b (bvmul {NEG1} a) (bvmul {NEG1} c)) (_ bv5 256)))"
        ));
        assert!(!u.script.contains("(- b (+ a c))"), "{}", u.script);
    }

    #[test]
    fn an_extended_difference_keeps_its_bound() {
        // As in a fairness check: the vault's balance b is unbounded, but
        // totalAssets() = b - a is checked and asserted <= 1000. Then
        // totalAssets() + 1 is at most 1001, and a product with it needs no mod.
        let t = translate_src(&format!(
            "(declare-fun a () (_ BitVec 256))\n(declare-fun b () (_ BitVec 256))\n(declare-fun s () (_ BitVec 256))\n\
             (assert (bvule s (_ bv1000 256)))\n\
             (assert (bvule (bvadd b (bvmul {NEG1} a)) b))\n\
             (assert (bvule (bvadd b (bvmul {NEG1} a)) (_ bv1000 256)))\n\
             (assert (= (bvmul s (bvadd (_ bv1 256) b (bvmul {NEG1} a))) (_ bv5 256)))"
        ));
        assert!(!t.script.contains("(mod (+ 1 b"), "{}", t.script);
        assert!(!t.script.contains("(mod (* s"), "{}", t.script);
    }

    #[test]
    fn a_difference_at_most_a_sum_of_its_terms_does_not_wrap() {
        // OpenZeppelin's outstanding shares: s + p - c, where solc checks
        // (s + p) - c <= s + p.
        let t = translate_src(&format!(
            "(declare-fun s () (_ BitVec 256))\n(declare-fun p () (_ BitVec 256))\n(declare-fun c () (_ BitVec 256))\n\
             (assert (bvule s (_ bv1000 256)))\n(assert (bvule p (_ bv1000 256)))\n\
             (assert (bvule (bvadd s p (bvmul {NEG1} c)) (bvadd s p)))\n\
             (assert (= (bvadd s p (bvmul {NEG1} c)) (_ bv5 256)))"
        ));
        assert!(t.script.contains("(- (+ s p) c)"), "{}", t.script);
    }

    #[test]
    fn a_difference_from_its_own_check_keeps_its_range() {
        // x - y <= x is what justifies writing x - y without mod; written that
        // way, the check alone would allow y > x. The range assertion keeps the
        // integer query to the bit-vector one's models.
        let t = translate_src(&format!(
            "(declare-fun x () (_ BitVec 256))\n(declare-fun y () (_ BitVec 256))\n\
             (assert (bvule (bvadd x (bvmul {NEG1} y)) x))\n\
             (assert (bvult x y))"
        ));
        let n = t
            .script
            .lines()
            .find(|l| l.contains("Int (- x y)"))
            .and_then(|l| l.split_whitespace().nth(1))
            .expect("x - y")
            .to_string();
        assert!(
            t.script
                .contains(&format!("(assert (and (<= 0 {n}) (<= {n} ")),
            "{}",
            t.script
        );
    }

    #[test]
    fn unordered_subtraction_keeps_its_mod() {
        let t = translate_src(&format!(
            "(declare-fun x () (_ BitVec 256))\n(declare-fun y () (_ BitVec 256))\n\
             (assert (= (bvadd x (bvmul {NEG1} y)) (_ bv3 256)))"
        ));
        assert!(!t.script.contains("(- x y)"), "{}", t.script);
        assert!(t.script.contains("mod"), "{}", t.script);
    }

    #[test]
    fn orderings_chain_through_equalities() {
        // owed = s and owed <= x: s <= x.
        let t = translate_src(&format!(
            "(declare-fun x () (_ BitVec 256))\n(declare-fun s () (_ BitVec 256))\n(declare-fun owed () (_ BitVec 256))\n\
             (assert (bvule x (_ bv1000 256)))\n\
             (assert (= s owed))\n(assert (bvule owed x))\n\
             (assert (= (bvadd (_ bv1 256) x (bvmul {NEG1} s)) (_ bv3 256)))"
        ));
        assert!(t.script.contains("(- (+ 1 x) s)"), "{}", t.script);
        // 1 + x with x unbounded may wrap on its own: the mod stays.
        let u = translate_src(&format!(
            "(declare-fun x () (_ BitVec 256))\n(declare-fun s () (_ BitVec 256))\n(declare-fun owed () (_ BitVec 256))\n\
             (assert (= s owed))\n(assert (bvule owed x))\n\
             (assert (= (bvadd (_ bv1 256) x (bvmul {NEG1} s)) (_ bv3 256)))"
        ));
        assert!(!u.script.contains("(- (+ 1 x) s)"), "{}", u.script);
    }

    #[test]
    fn a_checked_sum_orders_the_terms_it_names() {
        // a + b <= c, as a solvency check asserts, gives c - a - b >= 0.
        let t = translate_src(&format!(
            "(declare-fun a () (_ BitVec 256))\n(declare-fun b () (_ BitVec 256))\n(declare-fun c () (_ BitVec 256))\n\
             (assert (bvule a (_ bv1000 256)))\n(assert (bvule b (_ bv1000 256)))\n\
             (assert (bvule (bvadd a b) c))\n\
             (assert (= (bvadd c (bvmul {NEG1} a) (bvmul {NEG1} b)) (_ bv5 256)))"
        ));
        assert!(t.script.contains("(- c (+ a b))"), "{}", t.script);
        // Without the bounds, a + b might wrap, and the ordering says nothing.
        let u = translate_src(&format!(
            "(declare-fun a () (_ BitVec 256))\n(declare-fun b () (_ BitVec 256))\n(declare-fun c () (_ BitVec 256))\n\
             (assert (bvule (bvadd a b) c))\n\
             (assert (= (bvadd c (bvmul {NEG1} a) (bvmul {NEG1} b)) (_ bv5 256)))"
        ));
        assert!(!u.script.contains("(- c (+ a b))"), "{}", u.script);
    }

    #[test]
    fn split_bound_checks_bound_the_word() {
        let t = translate_src(
            "(declare-fun x () (_ BitVec 256))\n(declare-fun y () (_ BitVec 256))\n\
             (assert (and (= ((_ extract 255 97) x) (_ bv0 159)) (bvule ((_ extract 96 0) x) (_ bv1000 97))))\n\
             (assert (and (= ((_ extract 255 97) y) (_ bv0 159)) (bvule ((_ extract 96 0) y) (_ bv1000 97))))\n\
             (assert (= (bvmul x y) (_ bv7 256)))",
        );
        assert!(!t.script.contains("(mod (* x y)"), "{}", t.script);
    }

    #[test]
    fn bounds_follow_asserted_orderings() {
        let t = translate_src(
            "(declare-fun x () (_ BitVec 256))\n(declare-fun b () (_ BitVec 256))\n(declare-fun y () (_ BitVec 256))\n\
             (assert (bvule b (_ bv1000 256)))\n(assert (not (bvult b x)))\n(assert (bvule y (_ bv1000 256)))\n\
             (assert (= (bvmul x y) (_ bv7 256)))",
        );
        assert!(!t.script.contains("(mod (* x y)"), "{}", t.script);
    }

    #[test]
    fn evm_division_by_zero_is_zero() {
        let t = translate_src(
            "(declare-fun f_evm_bvudiv_256 ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))\n\
             (declare-fun x () (_ BitVec 256))\n(assert (= (f_evm_bvudiv_256 x (_ bv0 256)) (_ bv0 256)))",
        );
        assert!(
            t.script.contains("(ite (= 0 0) 0 (div x 0))"),
            "{}",
            t.script
        );
        assert!(!t.script.contains("declare-fun f_evm"), "{}", t.script);
    }

    #[test]
    fn masks_and_flags_are_exact() {
        let t = translate_src(
            "(declare-fun x () (_ BitVec 256))\n\
             (assert (= ((_ extract 159 0) (bvand x #x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff)) (_ bv1 160)))",
        );
        assert!(!t.abstracted, "{}", t.script);
        let t = translate_src(
            "(declare-fun a () (_ BitVec 256))\n(declare-fun b () (_ BitVec 256))\n\
             (assert (= (bvand a b) (_ bv1 256)))",
        );
        assert!(t.abstracted);
    }

    #[test]
    fn let_bindings_and_macros_expand() {
        let t = translate_src(
            "(declare-fun x () (_ BitVec 8))\n\
             (define-fun inc ((v (_ BitVec 8))) (_ BitVec 8) (bvadd v (_ bv1 8)))\n\
             (assert (let ((?a (inc x))) (= ?a (_ bv2 8))))",
        );
        assert!(t.script.contains("(mod (+ x 1) 256)"), "{}", t.script);
    }

    #[test]
    fn renders_models_for_halmos() {
        let s = render(
            &Answer::Sat(vec![("p_i_uint256_a_00".into(), 256, BigUint::from(2u32))]),
            None,
        );
        assert!(s.starts_with("sat\n"));
        assert!(s.contains("(define-fun p_i_uint256_a_00 () (_ BitVec 256) #x0000000000000000000000000000000000000000000000000000000000000002)"));
    }
}
