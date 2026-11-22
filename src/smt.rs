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
//!
//! Exactness is a claim about this code, so since 0.8.0 (Step 17) answers are
//! checked against the original query. Every `sat` model is plugged back into
//! it, and Halmos gets only a model that checks out; a sample of the rewrite's
//! `unsat` answers, or all of them, goes to a bit-vector solver. A
//! disagreement is saved, and Halmos gets the bit-vector answer once its model
//! checks out, or `unknown`.

use anyhow::{Context, Result, anyhow, bail};
use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

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
                        if hi < m || injected("wraparound") {
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
                if is_halmos_name(name) {
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

/// Runs a checker, stopping it and everything it started at `deadline`,
/// whatever its own time limit says. None if it was stopped.
fn run_until(cmd: &[String], file: &Path, deadline: Instant) -> Result<Option<String>> {
    use std::io::Read;
    use std::process::Stdio;
    let mut c = Command::new(&cmd[0]);
    c.args(&cmd[1..])
        .arg(file)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null());
    // A checker may be a script around the real solver: run it in a group of
    // its own, so stopping it stops the solver too.
    crate::prove::own_group(&mut c);
    let mut child = c.spawn().with_context(|| format!("running {}", cmd[0]))?;
    let mut stdout = child.stdout.take().context("reading the checker")?;
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let mut out = Vec::new();
        let _ = stdout.read_to_end(&mut out);
        let _ = tx.send(out);
    });
    let out = rx.recv_timeout(deadline.saturating_duration_since(Instant::now()));
    // Finished or not, it stops here, with every process it started.
    crate::prove::stop_group(&mut child);
    Ok(out.ok().map(|o| String::from_utf8_lossy(&o).into_owned()))
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
                vals.insert(plain(name).to_string(), n);
            }
        }
    }
    Some(
        vars.iter()
            .map(|(n, w)| {
                let v = vals.get(plain(n)).cloned().unwrap_or_default();
                (n.clone(), *w, v)
            })
            .collect(),
    )
}

/// Where an answer came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum By {
    /// The integer rewrite.
    Rewrite,
    /// A bit-vector solver on the original query.
    BitVector,
}

/// An answer, before Step 17's checks.
struct Outcome {
    answer: Answer,
    /// For a bit-vector solver's answer, its output, passed to Halmos as is.
    passthrough: Option<String>,
    by: By,
    /// The integer solver's output, when the rewrite answered.
    rewrite_out: Option<String>,
    /// How the solver that answered was run.
    run: Option<SolverRun>,
}

struct SolverRun {
    command: Vec<String>,
    /// The query it read.
    input: PathBuf,
    budget: Duration,
    took: Duration,
}

/// A bit-vector solver's answer to the original query, its output, and the
/// command.
fn bit_vector(
    file: &Path,
    budget: Duration,
    incremental: bool,
) -> Result<(Answer, Option<String>, Option<Vec<String>>)> {
    match bv_solver(budget, incremental) {
        Some(cmd) => {
            let mut out = run(&cmd, file)?;
            if injected("bad-fallback-model") {
                out = corrupt_values(&out);
            }
            let a = match first_line(&out) {
                "unsat" => Answer::Unsat,
                "sat" => Answer::Sat(Vec::new()),
                _ => Answer::Unknown,
            };
            Ok((a, Some(out), Some(cmd)))
        }
        None => Ok((Answer::Unknown, None, None)),
    }
}

fn first_line(out: &str) -> &str {
    out.lines().next().unwrap_or("").trim()
}

/// Solves a Halmos query file, then checks the answer (Step 17). Returns the
/// answer and, for a bit-vector solver's answer, its own output to pass on.
pub fn solve(file: &Path, timeout: Duration) -> Result<(Answer, Option<String>)> {
    let mode = CheckMode::from_env();
    let deadline = Instant::now() + timeout;
    let o = solve_unchecked(file, timeout)?;
    // The checks of an answer share at most `AUSWEG_CHECK_TIMEOUT` seconds (10
    // by default), within the query's time: the checker is a bit-blasting
    // solver, slow on exactly the queries the rewrite is for, and an
    // inconclusive check costs what it was given.
    let cap = Duration::from_secs(
        std::env::var("AUSWEG_CHECK_TIMEOUT")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(10),
    );
    let src = std::fs::read_to_string(file).unwrap_or_default();
    let mut rec = Record {
        query: format!("{:016x}", fnv1a(0, &src)),
        by: match o.by {
            By::Rewrite => "rewrite",
            By::BitVector => "bit-vector",
        }
        .into(),
        check: "none".into(),
        ..Default::default()
    };
    let (answer, passthrough) = if mode == CheckMode::Off {
        (o.answer, o.passthrough)
    } else {
        checked(file, &src, mode, o, timeout, cap, deadline, &mut rec)?
    };
    rec.answer = match &answer {
        Answer::Unsat => "unsat",
        Answer::Sat(_) => "sat",
        Answer::Unknown => "unknown",
    }
    .into();
    record(&rec);
    Ok((answer, passthrough))
}

fn solve_unchecked(file: &Path, timeout: Duration) -> Result<Outcome> {
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
    let deadline = Instant::now() + timeout;
    let remaining = || {
        deadline
            .saturating_duration_since(Instant::now())
            .max(Duration::from_secs(1))
    };
    let fallback = || -> Result<Outcome> {
        let (budget, started) = (remaining(), Instant::now());
        let (answer, passthrough, command) = bit_vector(file, budget, incremental)?;
        Ok(Outcome {
            answer,
            passthrough,
            by: By::BitVector,
            rewrite_out: None,
            run: command.map(|command| SolverRun {
                command,
                input: file.to_path_buf(),
                budget,
                took: started.elapsed(),
            }),
        })
    };
    let rewrite = |answer: Answer, out: String, run: SolverRun| Outcome {
        answer,
        passthrough: None,
        by: By::Rewrite,
        rewrite_out: Some(out),
        run: Some(run),
    };
    let Ok(t) = translated else {
        return fallback();
    };
    let int_file = file.with_extension("int.smt2");
    std::fs::write(&int_file, &t.script)?;
    if int_solver(timeout).is_none() {
        return fallback();
    }
    // Paths through code ausweg abstracts (OpenZeppelin's 512-bit mulDiv branch)
    // are usually infeasible for reasons that do not need that code: try the
    // query without it first.
    if let Some(relaxed) = &t.relaxed {
        let quick = Duration::from_secs((timeout.as_secs() / 3).max(1));
        let rel_file = file.with_extension("relaxed.smt2");
        std::fs::write(&rel_file, staged(relaxed, quick))?;
        let (command, started) = (int_solver(quick).unwrap(), Instant::now());
        let out = run(&command, &rel_file)?;
        if first_line(&out) == "unsat" {
            let took = started.elapsed();
            let input = rel_file.clone();
            let solved = SolverRun {
                command,
                input,
                budget: quick,
                took,
            };
            return Ok(rewrite(Answer::Unsat, out, solved));
        }
    }
    let left = remaining();
    std::fs::write(&int_file, staged(&t.script, left))?;
    let (command, started) = (int_solver(left).unwrap(), Instant::now());
    let out = run(&command, &int_file)?;
    let took = started.elapsed();
    let solved = SolverRun {
        command,
        input: int_file.clone(),
        budget: left,
        took,
    };
    match first_line(&out) {
        "unsat" => Ok(rewrite(Answer::Unsat, out, solved)),
        "sat" if !t.abstracted => match parse_values(&out, &t.model_vars) {
            Some(mut v) => {
                if injected("bad-model") {
                    for (_, w, x) in v.iter_mut() {
                        *x = (&*x + 1u32) % pow2(*w);
                    }
                }
                Ok(rewrite(Answer::Sat(v), out, solved))
            }
            None => fallback(),
        },
        // The model may use an abstracted operation wrongly: let a bit-vector
        // solver decide.
        "sat" => fallback(),
        // Out of time: a bit-vector solver would not do better.
        _ => Ok(rewrite(Answer::Unknown, out, solved)),
    }
}

// ---------------------------------------------------------------- Step 17: checking answers

/// Which answers to check against the original bit-vector query.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheckMode {
    /// No checks.
    Off,
    /// Every `sat` model, and the rewrite's `unsat` answers that a keyed hash
    /// of the query picks: one in `every`, the same ones whenever the seed is
    /// the same. An `unsat` the check cannot settle stays `unsat`.
    Sample { every: u64, seed: u64 },
    /// Every `sat` model and every `unsat` from the rewrite. An `unsat` the
    /// check cannot settle becomes `unknown`.
    All,
}

impl CheckMode {
    pub const DEFAULT: CheckMode = CheckMode::Sample { every: 16, seed: 0 };

    /// The value of `AUSWEG_CHECK`, which `ausweg prove` passes to `ausweg smt`.
    pub fn to_env(self) -> String {
        match self {
            CheckMode::Off => "off".into(),
            CheckMode::All => "all".into(),
            CheckMode::Sample { every, seed } => format!("sample:{every}:{seed}"),
        }
    }

    pub fn from_env_value(v: &str) -> Option<CheckMode> {
        match v {
            "off" => Some(CheckMode::Off),
            "all" => Some(CheckMode::All),
            _ => {
                let mut parts = v.strip_prefix("sample:")?.split(':');
                let every = parts.next()?.parse().ok().filter(|&e: &u64| e > 0)?;
                let seed = parts.next()?.parse().ok()?;
                parts
                    .next()
                    .is_none()
                    .then_some(CheckMode::Sample { every, seed })
            }
        }
    }

    fn from_env() -> CheckMode {
        std::env::var("AUSWEG_CHECK")
            .ok()
            .and_then(|v| Self::from_env_value(&v))
            .unwrap_or(Self::DEFAULT)
    }

    /// Whether to check the rewrite's `unsat` answer to this query.
    fn picks(self, query: &str) -> bool {
        match self {
            CheckMode::Off => false,
            CheckMode::All => true,
            CheckMode::Sample { every, seed } => {
                let h = fnv1a(seed, query);
                (h ^ (h >> 32)).is_multiple_of(every)
            }
        }
    }

    pub fn describe(self) -> String {
        match self {
            CheckMode::Off => "off".into(),
            CheckMode::All => "every answer".into(),
            CheckMode::Sample { every, seed } => format!("1 in {every}, seed {seed}"),
        }
    }
}

/// 64-bit FNV-1a over the seed and the query, with Halmos's per-run symbol ids
/// left out: the same query hashes the same on every run, machine and build.
fn fnv1a(seed: u64, text: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in seed
        .to_le_bytes()
        .iter()
        .chain(without_run_ids(text).as_bytes())
    {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// The query without the random part of Halmos's symbol names: Halmos names a
/// symbol `p_x_uint256_<7 hex digits>_00`, the digits fresh on every run.
fn without_run_ids(text: &str) -> String {
    let b = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    while i < b.len() {
        let id = b[i] == b'_'
            && i + 10 <= b.len()
            && b[i + 1..i + 8]
                .iter()
                .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(c))
            && b[i + 8] == b'_'
            && b[i + 9].is_ascii_digit();
        if id {
            i += 8;
        } else {
            out.push(b[i] as char);
            i += 1;
        }
    }
    out
}

/// Faults to plant, for testing the checks: `AUSWEG_SMT_INJECT`, a comma-separated
/// list of `wraparound` (a sum that can overflow loses its `mod 2^n`), `bad-model`
/// (every value in the rewrite's model is changed) and `bad-fallback-model` (so
/// is every value in the bit-vector solver's). Only in builds with the `fault-injection` feature.
fn injected(fault: &str) -> bool {
    #[cfg(feature = "fault-injection")]
    {
        std::env::var("AUSWEG_SMT_INJECT").is_ok_and(|v| v.split(',').any(|f| f.trim() == fault))
    }
    #[cfg(not(feature = "fault-injection"))]
    {
        let _ = fault;
        false
    }
}

/// The solver output with every value Halmos reads changed: `(_ bvK n)` becomes
/// `(_ bvK+1 n)`, mod 2^n, and a `#x`/`#b` literal gets its last digit changed.
fn corrupt_values(out: &str) -> String {
    let change = |line: &str| -> String {
        let reads = [
            "(define-fun p_",
            "(define-fun halmos_",
            "(define-fun |p_",
            "(define-fun |halmos_",
        ];
        if !reads.iter().any(|r| line.contains(r)) {
            return line.to_string();
        }
        if let Some(i) = line.find("(_ bv") {
            let digits: String = line[i + 5..]
                .chars()
                .take_while(|c| c.is_ascii_digit())
                .collect();
            let tail = &line[i + 5 + digits.len()..];
            let width: u32 = tail
                .trim_start()
                .chars()
                .take_while(|c| c.is_ascii_digit())
                .collect::<String>()
                .parse()
                .unwrap_or(256);
            let k: BigUint = digits.parse().unwrap_or_default();
            format!("{}(_ bv{}{tail}", &line[..i], (k + 1u32) % pow2(width))
        } else if let Some(i) = line.rfind(|c: char| c.is_ascii_hexdigit()) {
            let c = line.as_bytes()[i] as char;
            let flipped = if c == '0' { '1' } else { '0' };
            format!("{}{flipped}{}", &line[..i], &line[i + 1..])
        } else {
            line.to_string()
        }
    };
    let mut s: String = out.lines().map(change).collect::<Vec<_>>().join("\n");
    if out.ends_with('\n') {
        s.push('\n');
    }
    s
}

#[cfg(test)]
thread_local! {
    /// A checker command for this test thread only.
    static TEST_CHECKER: std::cell::RefCell<Option<Vec<String>>> = const { std::cell::RefCell::new(None) };
    /// Where this test thread saves disagreements.
    static TEST_SAVE_DIR: std::cell::RefCell<Option<PathBuf>> = const { std::cell::RefCell::new(None) };
}

/// The bit-vector solver that checks answers: `AUSWEG_SMT_CHECKER`, else yices,
/// else bitwuzla, else z3.
fn checker(budget: Duration) -> Option<Vec<String>> {
    #[cfg(test)]
    if let Some(c) = TEST_CHECKER.with(|c| c.borrow().clone()) {
        return Some(c);
    }
    if let Ok(cmd) = std::env::var("AUSWEG_SMT_CHECKER") {
        return Some(cmd.split_whitespace().map(String::from).collect());
    }
    // Its own limit, in whole seconds, is rounded up: `run_until` stops it on
    // time.
    let secs = (budget.as_millis().div_ceil(1000) as u64).max(1);
    if let Some(y) = find_on_path("yices-smt2").or_else(|| halmos_solver("yices-smt2")) {
        return Some(yices(&y, secs, false));
    }
    if let Some(b) = find_on_path("bitwuzla").or_else(|| halmos_solver("bitwuzla")) {
        return Some(vec![
            b.display().to_string(),
            "--produce-models".into(),
            format!("--time-limit={}", secs * 1000),
        ]);
    }
    let z3 = find_on_path("z3")?;
    Some(vec![
        z3.display().to_string(),
        "-smt2".into(),
        format!("-T:{secs}"),
    ])
}

/// A symbol without its `|...|` quotes.
fn plain(sym: &str) -> &str {
    sym.strip_prefix('|')
        .and_then(|s| s.strip_suffix('|'))
        .unwrap_or(sym)
}

/// A name Halmos reads back from a model, by its pattern
/// `\|?((?:halmos_|p_)[^ |]+)\|?`: `halmos_*` or `p_*`, quoted or not.
fn is_halmos_name(sym: &str) -> bool {
    let p = plain(sym);
    p.strip_prefix("halmos_")
        .or_else(|| p.strip_prefix("p_"))
        .is_some_and(|rest| !rest.is_empty() && !rest.contains([' ', '|']))
}

/// Model values the way Halmos reads them: `(define-fun <halmos_* or p_*> ()
/// (_ BitVec n) v)`, the name possibly in `|...|`, with v a `#x` or `#b`
/// literal or `(_ bvK n)`. Names come back without quotes.
fn read_model(out: &str) -> Vec<(String, u32, BigUint)> {
    fn walk(s: &Sexp, acc: &mut Vec<(String, u32, BigUint)>) {
        let Some(l) = s.list() else { return };
        if let [Sexp::Atom(df), Sexp::Atom(name), Sexp::List(ps), sort, v] = l
            && df == "define-fun"
            && ps.is_empty()
            && is_halmos_name(name)
            && let Some([Sexp::Atom(u), Sexp::Atom(bv), Sexp::Atom(w)]) = sort.list()
            && u == "_"
            && bv == "BitVec"
            && let Ok(w) = w.parse::<u32>()
        {
            let value = match v {
                Sexp::Atom(a) => parse_literal(a).map(|(x, _)| x),
                Sexp::List(t) => match t.as_slice() {
                    [Sexp::Atom(u), Sexp::Atom(k), Sexp::Atom(_)] if u == "_" => {
                        k.strip_prefix("bv").and_then(|d| d.parse().ok())
                    }
                    _ => None,
                },
            };
            if let Some(x) = value {
                acc.push((plain(name).to_string(), w, x));
            }
            return;
        }
        for c in l {
            walk(c, acc);
        }
    }
    let mut acc = Vec::new();
    let body = out.trim_start().strip_prefix("sat").unwrap_or(out);
    for s in parse_sexps(body).unwrap_or_default() {
        walk(&s, &mut acc);
    }
    acc
}

/// The Halmos bit-vector variables a query declares: (name without quotes,
/// the symbol as the query writes it).
fn halmos_vars(cmds: &[Sexp]) -> Vec<(String, String)> {
    cmds.iter()
        .filter_map(|c| {
            let l = c.list()?;
            let (name, sort) = match l {
                [Sexp::Atom(d), Sexp::Atom(n), Sexp::List(ps), sort]
                    if d == "declare-fun" && ps.is_empty() =>
                {
                    (n, sort)
                }
                [Sexp::Atom(d), Sexp::Atom(n), sort] if d == "declare-const" => (n, sort),
                _ => return None,
            };
            let is_bv = matches!(sort.list(), Some([Sexp::Atom(u), Sexp::Atom(b), _]) if u == "_" && b == "BitVec");
            (is_bv && is_halmos_name(name)).then(|| (plain(name).to_string(), name.clone()))
        })
        .collect()
}

/// The query with the model's values asserted, ending at its first
/// `check-sat`. Values for names the query does not declare are left out.
fn with_values(
    src: &str,
    vals: &[(String, u32, BigUint)],
    declared: &[(String, String)],
) -> Option<String> {
    let at = src.find("(check-sat)")?;
    let mut s = src[..at].to_string();
    for (n, w, v) in vals {
        if let Some((_, sym)) = declared.iter().find(|(p, _)| p == n) {
            let _ = writeln!(s, "(assert (= {sym} (_ bv{v} {w})))");
        }
    }
    s.push_str("(check-sat)\n");
    Some(s)
}

/// Halmos's own refinement: the EVM operations it declares as uninterpreted
/// functions (`f_evm_bvmul_256` and the divisions) get their EVM meaning, as in
/// Halmos's `refine`. The rewrite gives them that meaning too, so this is the
/// query its answer is about. Halmos itself asks the abstract query first, and
/// the refined one only when a model mentions `f_evm_`.
fn refine(src: &str) -> String {
    let mut s = src.to_string();
    for op in ["bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem"] {
        let prefix = format!("(declare-fun f_evm_{op}_");
        while let Some(i) = s.find(&prefix) {
            let w: String = s[i + prefix.len()..]
                .chars()
                .take_while(|c| c.is_ascii_digit())
                .collect();
            let decl = format!(
                "(declare-fun f_evm_{op}_{w} ((_ BitVec {w}) (_ BitVec {w})) (_ BitVec {w}))"
            );
            if !s[i..].starts_with(&decl) {
                break;
            }
            let body = if op == "bvmul" {
                format!("({op} x y)")
            } else {
                format!("(ite (= y (_ bv0 {w})) (_ bv0 {w}) ({op} x y))")
            };
            let def = format!(
                "(define-fun f_evm_{op}_{w} ((x (_ BitVec {w})) (y (_ BitVec {w}))) (_ BitVec {w}) {body})"
            );
            s.replace_range(i..i + decl.len(), &def);
        }
    }
    s
}

#[derive(Debug, PartialEq)]
enum ModelCheck {
    /// The values satisfy the refined query.
    Valid,
    Invalid(String),
    /// Not settled: out of time, no checker, or a query with scopes.
    Inconclusive,
    /// The model mentions `f_evm_`: Halmos discards such a model and refines
    /// the query itself.
    Discarded,
}

impl ModelCheck {
    fn label(&self) -> &'static str {
        match self {
            ModelCheck::Valid => "valid",
            ModelCheck::Invalid(_) => "invalid",
            ModelCheck::Inconclusive => "inconclusive",
            ModelCheck::Discarded => "discarded",
        }
    }
}

/// What a disagreement keeps: files, and how each solver run went.
#[derive(Default)]
struct Evidence {
    /// (name, contents)
    files: Vec<(String, String)>,
    runs: Vec<serde_json::Value>,
}

impl Evidence {
    fn file(&mut self, name: &str, contents: String) {
        self.files.push((name.to_string(), contents));
    }

    fn extend(&mut self, other: Evidence) {
        self.files.extend(other.files);
        self.runs.extend(other.runs);
    }
}

fn secs(d: Duration) -> f64 {
    (d.as_secs_f64() * 100.0).round() / 100.0
}

/// A checker's output file, when the check's time ran out first.
const STOPPED: &str = "(stopped: the check's time ran out)\n";

/// Asks the checker about the query in `f` (saved as `input`) for at most
/// `budget` (None: no time left), keeping its answer in `ev` as `name`. None
/// if it did not answer in time, or there is no checker.
fn ask_checker(
    f: &Path,
    input: &str,
    budget: Option<Duration>,
    name: &str,
    ev: &mut Evidence,
) -> Result<Option<String>> {
    let Some((budget, cmd)) = budget.and_then(|b| checker(b).map(|c| (b, c))) else {
        return Ok(None);
    };
    let started = Instant::now();
    let out = run_until(&cmd, f, started + budget)?;
    ev.runs.push(serde_json::json!({
        "run": "checker",
        "command": cmd.join(" "),
        "input": input,
        "output": name,
        "budget_seconds": secs(budget),
        "seconds": secs(started.elapsed()),
        "stopped": out.is_none(),
    }));
    ev.file(name, out.clone().unwrap_or_else(|| STOPPED.into()));
    Ok(out)
}

/// Plugs a model, as Halmos would read it from `text`, into the refined query,
/// and asks the checker for at most `budget`. Returns what it found, with the
/// query and the checker's answer as `<tag>.smt2` and `<tag>.out`.
fn check_model(
    file: &Path,
    src: &str,
    text: &str,
    budget: Option<Duration>,
    tag: &str,
) -> Result<(ModelCheck, Evidence)> {
    let none = Evidence::default;
    let Ok(cmds) = parse_sexps(src) else {
        return Ok((ModelCheck::Inconclusive, none()));
    };
    if needs_incremental(&cmds) {
        return Ok((ModelCheck::Inconclusive, none()));
    }
    if text.contains("f_evm_") {
        return Ok((ModelCheck::Discarded, none()));
    }
    let declared = halmos_vars(&cmds);
    let vals = read_model(text);
    let invalid = |why: String| Ok((ModelCheck::Invalid(why), none()));
    if vals.is_empty() && !declared.is_empty() {
        return invalid("the model gives no value Halmos can read".into());
    }
    if let Some((n, w, _)) = vals.iter().find(|(_, w, v)| *v >= pow2(*w)) {
        return invalid(format!("the value of {n} does not fit in {w} bits"));
    }
    if let Some((n, _, _)) = vals
        .iter()
        .find(|(n, _, _)| !declared.iter().any(|(p, _)| p == n))
    {
        return invalid(format!(
            "it gives a value to {n}, which the query does not declare"
        ));
    }
    let Some(q) = with_values(&refine(src), &vals, &declared) else {
        return Ok((ModelCheck::Inconclusive, none()));
    };
    let f = file.with_extension(format!("{tag}.smt2"));
    std::fs::write(&f, &q)?;
    let mut ev = none();
    ev.file(&format!("{tag}.smt2"), q);
    let out = ask_checker(
        &f,
        &format!("{tag}.smt2"),
        budget,
        &format!("{tag}.out"),
        &mut ev,
    )?;
    let check = match out.as_deref().map(first_line) {
        Some("sat") => ModelCheck::Valid,
        Some("unsat") => ModelCheck::Invalid("its values do not satisfy the query".into()),
        _ => ModelCheck::Inconclusive,
    };
    Ok((check, ev))
}

enum UnsatCheck {
    Confirmed,
    /// The checker found a model: its output.
    Contradicted(String),
    Inconclusive,
}

/// Asks the checker the original query: the abstract one first, since if even
/// it is unsat so is the refined one, and it is the easier of the two; then, if
/// it has abstract EVM operations, the refined one, which is what the rewrite
/// answered. The two share one budget: `budget()` is what is left of it, None
/// once it is spent. Returns what it found, with the checker's answers and the
/// refined query.
fn check_unsat(
    file: &Path,
    src: &str,
    budget: &dyn Fn() -> Option<Duration>,
) -> Result<(UnsatCheck, Evidence)> {
    let mut ev = Evidence::default();
    let Some(out) = ask_checker(file, "original.smt2", budget(), "checker.out", &mut ev)? else {
        return Ok((UnsatCheck::Inconclusive, ev));
    };
    if first_line(&out) == "unsat" {
        return Ok((UnsatCheck::Confirmed, ev));
    }
    let refined = refine(src);
    let out = if refined == src {
        out
    } else {
        let f = file.with_extension("refined.smt2");
        std::fs::write(&f, &refined)?;
        ev.file("refined.smt2", refined);
        let Some(out) = ask_checker(&f, "refined.smt2", budget(), "checker-refined.out", &mut ev)?
        else {
            return Ok((UnsatCheck::Inconclusive, ev));
        };
        out
    };
    let c = match first_line(&out) {
        "unsat" => UnsatCheck::Confirmed,
        "sat" => UnsatCheck::Contradicted(out),
        _ => UnsatCheck::Inconclusive,
    };
    Ok((c, ev))
}

/// What Halmos gets for the rewrite's `unsat` when the check cannot settle it:
/// `unknown` when every answer must be confirmed, else the `unsat`, as for the
/// answers the sample did not pick.
fn unconfirmed_unsat(mode: CheckMode) -> Answer {
    if mode == CheckMode::All {
        Answer::Unknown
    } else {
        Answer::Unsat
    }
}

/// What Halmos gets for a `sat` answer, given its model's check, in every
/// mode: the answer when the model is valid, or is one Halmos discards and
/// refines itself; else `unknown`. Every model is checked, so sampling, which
/// is for `unsat` answers, never lets an unconfirmed one through.
fn settle_sat(
    m: &ModelCheck,
    answer: Answer,
    passthrough: Option<String>,
) -> (Answer, Option<String>) {
    match m {
        ModelCheck::Valid | ModelCheck::Discarded => (answer, passthrough),
        ModelCheck::Invalid(_) | ModelCheck::Inconclusive => (Answer::Unknown, None),
    }
}

fn answer_label(a: &Answer) -> &'static str {
    match a {
        Answer::Unsat => "unsat",
        Answer::Sat(_) => "sat",
        Answer::Unknown => "unknown",
    }
}

/// What a saved disagreement says about itself, in `about.json`.
struct About {
    what: String,
    /// The answer Halmos got in the end.
    halmos_got: &'static str,
    mode: CheckMode,
    timeout: Duration,
    /// `--check-timeout`.
    check_timeout: Duration,
    /// What the checks of the answer had: `--check-timeout`, or less when the
    /// query had less time left.
    check_budget: Duration,
}

/// Applies the checks to an answer, and says what they found in `rec`.
///
/// The checks of the answer share one budget, `cap` (`--check-timeout`), within
/// the query's own time, which ends at `deadline`: once it is spent no check
/// starts, and a running one is stopped. Replacing a wrong answer, which means
/// finding a bit-vector answer and checking its model, may use the rest of the
/// query's time.
#[allow(clippy::too_many_arguments)]
fn checked(
    file: &Path,
    src: &str,
    mode: CheckMode,
    o: Outcome,
    timeout: Duration,
    cap: Duration,
    deadline: Instant,
    rec: &mut Record,
) -> Result<(Answer, Option<String>)> {
    let start = Instant::now();
    let check_deadline = deadline.min(start + cap);
    let check_left = || {
        let d = check_deadline.saturating_duration_since(Instant::now());
        (!d.is_zero()).then_some(d)
    };
    // As for the rewrite, a solver gets at least a second.
    let left = || {
        deadline
            .saturating_duration_since(Instant::now())
            .max(Duration::from_secs(1))
    };
    let about = |what: &str, got: &Answer| About {
        what: what.to_string(),
        halmos_got: answer_label(got),
        mode,
        timeout,
        check_timeout: cap,
        check_budget: check_deadline.saturating_duration_since(start),
    };
    match (&o.answer, o.by) {
        (Answer::Unsat, By::Rewrite) => {
            if !mode.picks(src) {
                rec.check = "unchecked".into();
                return Ok((Answer::Unsat, None));
            }
            let (c, mut ev) = check_unsat(file, src, &check_left)?;
            match c {
                UnsatCheck::Confirmed => {
                    rec.check = "confirmed".into();
                    Ok((Answer::Unsat, None))
                }
                UnsatCheck::Contradicted(model) => {
                    // The checker's answer replaces the rewrite's, once its
                    // model is checked too.
                    rec.check = "contradicted".into();
                    let (m, model_ev) =
                        check_model(file, src, &model, Some(left()), "model-check")?;
                    ev.extend(model_ev);
                    rec.model = Some(m.label().into());
                    let (a, p) = settle_sat(&m, Answer::Sat(Vec::new()), Some(model));
                    let what = "the rewrite answered unsat; the checker found a model";
                    rec.saved = save(src, &o, &ev, &about(what, &a));
                    Ok((a, p))
                }
                UnsatCheck::Inconclusive => {
                    rec.check = "inconclusive".into();
                    Ok((unconfirmed_unsat(mode), None))
                }
            }
        }
        (Answer::Sat(_), by) => {
            let text = render(&o.answer, o.passthrough.as_deref());
            let (m, model_ev) = check_model(file, src, &text, check_left(), "model-check")?;
            rec.model = Some(m.label().into());
            let ModelCheck::Invalid(why) = &m else {
                return Ok(settle_sat(&m, o.answer, o.passthrough));
            };
            let what = format!("a sat model was wrong: {why}");
            let mut ev = Evidence::default();
            ev.file("candidate.out", text);
            ev.extend(model_ev);
            let (a, p) = if by == By::BitVector {
                (Answer::Unknown, None)
            } else {
                // The rewrite's model is wrong: a bit-vector solver answers
                // instead, and its model is checked too.
                let incremental = parse_sexps(src).is_ok_and(|c| needs_incremental(&c));
                let (budget, started) = (left(), Instant::now());
                let (a, p, cmd) = bit_vector(file, budget, incremental)?;
                ev.runs.push(serde_json::json!({
                    "run": "replacement",
                    "command": cmd.map(|c| c.join(" ")),
                    "input": "original.smt2",
                    "output": "replacement.out",
                    "budget_seconds": secs(budget),
                    "seconds": secs(started.elapsed()),
                }));
                ev.file("replacement.out", p.clone().unwrap_or_default());
                if matches!(a, Answer::Sat(_)) {
                    let again = render(&a, p.as_deref());
                    let (m2, again_ev) =
                        check_model(file, src, &again, Some(left()), "replacement-check")?;
                    ev.extend(again_ev);
                    rec.replacement = Some(m2.label().into());
                    settle_sat(&m2, a, p)
                } else {
                    rec.replacement = Some(answer_label(&a).into());
                    (a, p)
                }
            };
            rec.saved = save(src, &o, &ev, &about(&what, &a));
            Ok((a, p))
        }
        _ => Ok((o.answer, o.passthrough)),
    }
}

/// Where disagreements are saved: `AUSWEG_SMT_SAVE_DIR`, else the temp
/// directory.
fn save_dir() -> PathBuf {
    #[cfg(test)]
    if let Some(d) = TEST_SAVE_DIR.with(|d| d.borrow().clone()) {
        return d;
    }
    std::env::var_os("AUSWEG_SMT_SAVE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::env::temp_dir().join("ausweg-rewrite-checks"))
}

/// Keeps everything needed to reproduce a disagreement: the original and
/// translated queries, the answer and every check of it, with the queries the
/// checks asked, any replacement and its check, and the versions, settings and
/// budgets. Returns the directory.
fn save(src: &str, o: &Outcome, evidence: &Evidence, about: &About) -> Option<String> {
    let dir = save_dir().join(format!("{:016x}", fnv1a(0, src)));
    // Only this disagreement's files: none left from an earlier run.
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).ok()?;
    let mut files = vec![("original.smt2".to_string(), src.to_string())];
    // The answer being checked, and the run that gave it.
    let (input, output) = match o.by {
        By::Rewrite => ("translated.smt2", "rewrite.out"),
        By::BitVector => ("original.smt2", "bit-vector.out"),
    };
    if o.by == By::Rewrite
        && let Some(t) = o
            .run
            .as_ref()
            .and_then(|r| std::fs::read_to_string(&r.input).ok())
    {
        files.push((input.into(), t));
    }
    if let Some(out) = o.rewrite_out.as_ref().or(o.passthrough.as_ref()) {
        files.push((output.into(), out.clone()));
    }
    let mut runs = vec![serde_json::json!({
        "run": match o.by {
            By::Rewrite => "rewrite",
            By::BitVector => "bit-vector",
        },
        "command": o.run.as_ref().map(|r| r.command.join(" ")),
        "input": input,
        "output": output,
        "budget_seconds": o.run.as_ref().map(|r| secs(r.budget)),
        "seconds": o.run.as_ref().map(|r| secs(r.took)),
    })];
    runs.extend(evidence.runs.iter().cloned());
    files.extend(evidence.files.iter().cloned());
    for (name, contents) in &files {
        std::fs::write(dir.join(name), contents).ok()?;
    }
    let version = |cmd: Option<Vec<String>>| -> String {
        cmd.and_then(|c| Command::new(&c[0]).arg("--version").output().ok())
            .map(|o| {
                String::from_utf8_lossy(&o.stdout)
                    .lines()
                    .next()
                    .unwrap_or("")
                    .to_string()
            })
            .unwrap_or_default()
    };
    let timeout = about.timeout;
    let json = serde_json::json!({
        "what": about.what,
        "halmos_got": about.halmos_got,
        "ausweg": env!("CARGO_PKG_VERSION"),
        "check": about.mode.to_env(),
        "timeout_seconds": timeout.as_secs(),
        "check_timeout_seconds": about.check_timeout.as_secs(),
        "check_budget_seconds": secs(about.check_budget),
        "integer_solver": int_solver(timeout).map(|c| c.join(" ")),
        "integer_solver_version": version(int_solver(timeout)),
        "checker": checker(about.check_timeout).map(|c| c.join(" ")),
        "checker_version": version(checker(about.check_timeout)),
        "fallback": bv_solver(timeout, false).map(|c| c.join(" ")),
        "fallback_version": version(bv_solver(timeout, false)),
        "files": files.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
        "runs": runs,
    });
    std::fs::write(
        dir.join("about.json"),
        serde_json::to_string_pretty(&json).ok()?,
    )
    .ok()?;
    Some(dir.display().to_string())
}

/// What `ausweg smt` did with one query, as one line of `AUSWEG_SMT_LOG`.
#[derive(Debug, Default, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Record {
    /// FNV-1a hash of the query text.
    pub query: String,
    /// What Halmos got: `sat`, `unsat` or `unknown`.
    pub answer: String,
    /// `rewrite` or `bit-vector`: who answered before the checks.
    pub by: String,
    /// For the rewrite's `unsat`: `unchecked`, `confirmed`, `contradicted` or
    /// `inconclusive`; else `none`.
    pub check: String,
    /// For a `sat` model: `valid`, `invalid`, `inconclusive`, or `discarded`
    /// (it mentions `f_evm_`, so Halmos discards it and refines the query).
    /// For a contradicted `unsat`, this is the checker's model.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model: Option<String>,
    /// Where a disagreement was saved.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub saved: Option<String>,
    /// For a wrong rewrite model, what replaced it: its model's check, as for
    /// `model`, or `unsat` or `unknown`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replacement: Option<String>,
}

fn record(rec: &Record) {
    let Some(path) = std::env::var_os("AUSWEG_SMT_LOG") else {
        return;
    };
    let Ok(line) = serde_json::to_string(rec) else {
        return;
    };
    // One short write with O_APPEND: lines from parallel queries do not interleave.
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        use std::io::Write as _;
        let _ = f.write_all(format!("{line}\n").as_bytes());
    }
}

/// What the checks found over a run: the counts behind `rewrite check:`.
#[derive(Debug, Default, Clone, PartialEq, serde::Serialize)]
pub struct RewriteCheck {
    /// `AUSWEG_CHECK`: `off`, `all`, or `sample:<every>:<seed>`.
    pub mode: String,
    /// Queries answered.
    pub queries: u64,
    /// `unsat` answers from the rewrite.
    pub rewrite_unsat: u64,
    /// Of those, checked against the original query.
    pub checked: u64,
    pub confirmed: u64,
    pub inconclusive: u64,
    pub contradicted: u64,
    /// `sat` models plugged into the original query, whoever produced them:
    /// the rewrite, a bit-vector solver, a replacement, or the checker.
    pub models_checked: u64,
    pub models_invalid: u64,
    pub models_inconclusive: u64,
    /// Models that mention `f_evm_`: Halmos discards them and refines the
    /// query itself, so they are passed on unchecked.
    pub models_discarded: u64,
    /// Answers Halmos got as `unknown` because of a check: it could not confirm
    /// them, or found them wrong with no confirmed answer to replace them.
    pub made_unknown: u64,
    /// Answers a bit-vector solver gave on its own, with no rewrite involved.
    pub bit_vector: u64,
    /// Where disagreements were saved.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub saved: Vec<String>,
}

impl RewriteCheck {
    pub fn from_log(mode: CheckMode, log: &str) -> RewriteCheck {
        let mut r = RewriteCheck {
            mode: mode.to_env(),
            ..Default::default()
        };
        for rec in log
            .lines()
            .filter_map(|l| serde_json::from_str::<Record>(l).ok())
        {
            r.queries += 1;
            if rec.by == "bit-vector" {
                r.bit_vector += 1;
            }
            match rec.check.as_str() {
                "unchecked" => r.rewrite_unsat += 1,
                "confirmed" => {
                    r.rewrite_unsat += 1;
                    r.checked += 1;
                    r.confirmed += 1;
                }
                "inconclusive" => {
                    r.rewrite_unsat += 1;
                    r.checked += 1;
                    r.inconclusive += 1;
                }
                "contradicted" => {
                    r.rewrite_unsat += 1;
                    r.checked += 1;
                    r.contradicted += 1;
                }
                _ => {}
            }
            for model in [rec.model.as_deref(), rec.replacement.as_deref()] {
                match model {
                    Some("valid") => r.models_checked += 1,
                    Some("invalid") => {
                        r.models_checked += 1;
                        r.models_invalid += 1;
                    }
                    Some("inconclusive") => {
                        r.models_checked += 1;
                        r.models_inconclusive += 1;
                    }
                    Some("discarded") => r.models_discarded += 1,
                    _ => {}
                }
            }
            let checks_decided = matches!(rec.check.as_str(), "inconclusive" | "contradicted")
                || matches!(rec.model.as_deref(), Some("invalid" | "inconclusive"));
            if rec.answer == "unknown" && checks_decided {
                r.made_unknown += 1;
            }
            if let Some(s) = rec.saved
                && !r.saved.contains(&s)
            {
                r.saved.push(s);
            }
        }
        r
    }

    /// Answers that disagreed with the original query.
    pub fn disagreements(&self) -> u64 {
        self.contradicted + self.models_invalid
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

    // ------------------------------------------------------------ Step 17

    #[test]
    fn check_modes_round_trip_and_sample_reproducibly() {
        for m in [
            CheckMode::Off,
            CheckMode::All,
            CheckMode::Sample { every: 16, seed: 7 },
        ] {
            assert_eq!(CheckMode::from_env_value(&m.to_env()), Some(m));
        }
        assert_eq!(CheckMode::from_env_value("sample:0:1"), None);
        assert_eq!(CheckMode::from_env_value("sample:16"), None);
        let queries: Vec<String> = (0..1600)
            .map(|i| format!("(assert (= p_x #x{i:04x}))"))
            .collect();
        let picked = |m: CheckMode| -> Vec<usize> {
            (0..queries.len())
                .filter(|&i| m.picks(&queries[i]))
                .collect()
        };
        let a = picked(CheckMode::Sample { every: 16, seed: 0 });
        // The same seed picks the same queries; about 1 in 16 of them.
        assert_eq!(a, picked(CheckMode::Sample { every: 16, seed: 0 }));
        assert!((60..140).contains(&a.len()), "{} picked", a.len());
        assert_ne!(a, picked(CheckMode::Sample { every: 16, seed: 1 }));
        assert_eq!(picked(CheckMode::Sample { every: 1, seed: 0 }).len(), 1600);
        assert_eq!(picked(CheckMode::All).len(), 1600);
        assert!(picked(CheckMode::Off).is_empty());
    }

    #[test]
    fn a_query_hashes_the_same_on_every_run() {
        let a = "(declare-fun p_x_uint256_ec447be_00 () (_ BitVec 256))\n(assert (= p_x_uint256_ec447be_00 balance_fadc0a7_01))";
        let b = "(declare-fun p_x_uint256_3b7ca34_00 () (_ BitVec 256))\n(assert (= p_x_uint256_3b7ca34_00 balance_0e1d2c3_01))";
        assert_eq!(fnv1a(0, a), fnv1a(0, b));
        assert_ne!(fnv1a(0, a), fnv1a(0, &a.replace("_00", "_01")));
        assert_ne!(fnv1a(0, a), fnv1a(1, a));
        // Only a seven-digit id between underscores, before the counter, goes.
        assert_eq!(without_run_ids("p_x_uint256_ec447be_00"), "p_x_uint256_00");
        assert_eq!(without_run_ids("f_evm_bvmul_256"), "f_evm_bvmul_256");
        assert_eq!(
            without_run_ids("storage_aaaa0001_1_0_0_cafe123_02"),
            "storage_aaaa0001_1_0_0_02"
        );
    }

    #[test]
    fn an_unconfirmed_unsat_is_unknown_only_when_checking_every_answer() {
        assert_eq!(unconfirmed_unsat(CheckMode::All), Answer::Unknown);
        assert_eq!(unconfirmed_unsat(CheckMode::DEFAULT), Answer::Unsat);
    }

    #[test]
    fn reads_models_the_way_halmos_does() {
        let out = "sat\n(\n  (define-fun p_x () (_ BitVec 8) #xff)\n  (define-fun halmos_y () (_ BitVec 3) #b101)\n  (define-fun p_z () (_ BitVec 256) (_ bv12 256))\n  (define-fun other () (_ BitVec 8) #x01)\n  (define-fun p_f ((a (_ BitVec 8))) (_ BitVec 8) a)\n)\n";
        let got = read_model(out);
        let names: Vec<(&str, u32, u32)> = got
            .iter()
            .map(|(n, w, v)| (n.as_str(), *w, v.to_u32().unwrap()))
            .collect();
        assert_eq!(
            names,
            vec![("p_x", 8, 255), ("halmos_y", 3, 5), ("p_z", 256, 12)]
        );
        // yices's own model format, which Halmos does not read.
        assert!(read_model("sat\n(= p_x #b11111111)\n").is_empty());
        // What render writes, read back.
        let vals = vec![("p_a".to_string(), 8, BigUint::from(7u32))];
        assert_eq!(read_model(&render(&Answer::Sat(vals.clone()), None)), vals);
    }

    #[test]
    fn corrupts_every_value_halmos_reads() {
        // The changed value stays in range: 255 + 1 wraps to 0.
        let max = "sat\n((define-fun p_x () (_ BitVec 8) (_ bv255 8)))\n";
        assert_eq!(read_model(&corrupt_values(max))[0].2, BigUint::from(0u32));
        let dec = "sat\n((define-fun p_x () (_ BitVec 8) (_ bv12 8))\n (define-fun p_y () (_ BitVec 8) (_ bv1 8)))\n";
        let changed = read_model(&corrupt_values(dec));
        assert_eq!(changed[0].2, BigUint::from(13u32));
        assert_eq!(changed[1].2, BigUint::from(2u32));
        for lit in ["#x0f", "#x00", "#b1", "#b0"] {
            let out = format!("sat\n((define-fun p_x () (_ BitVec 8) {lit}))\n");
            assert_ne!(read_model(&out), read_model(&corrupt_values(&out)), "{lit}");
        }
    }

    #[test]
    fn the_log_counts_what_the_checks_found() {
        let lines = [
            r#"{"query":"a","answer":"unsat","by":"rewrite","check":"unchecked"}"#,
            r#"{"query":"b","answer":"unsat","by":"rewrite","check":"confirmed"}"#,
            r#"{"query":"c","answer":"unsat","by":"rewrite","check":"inconclusive"}"#,
            r#"{"query":"d","answer":"sat","by":"rewrite","check":"contradicted","model":"valid","saved":"/x/d"}"#,
            r#"{"query":"e","answer":"sat","by":"rewrite","check":"none","model":"valid"}"#,
            r#"{"query":"f","answer":"unknown","by":"bit-vector","check":"none","model":"invalid","saved":"/x/f"}"#,
            r#"{"query":"g","answer":"unknown","by":"rewrite","check":"none"}"#,
            r#"{"query":"h","answer":"sat","by":"bit-vector","check":"none","model":"discarded"}"#,
            r#"{"query":"i","answer":"unknown","by":"rewrite","check":"inconclusive"}"#,
            r#"{"query":"j","answer":"unknown","by":"rewrite","check":"none","model":"inconclusive"}"#,
            r#"{"query":"k","answer":"sat","by":"rewrite","check":"none","model":"invalid","saved":"/x/k","replacement":"discarded"}"#,
            r#"{"query":"l","answer":"unknown","by":"rewrite","check":"none","model":"invalid","saved":"/x/l","replacement":"unknown"}"#,
            "not json",
        ];
        let c = RewriteCheck::from_log(CheckMode::DEFAULT, &lines.join("\n"));
        assert_eq!(c.mode, "sample:16:0");
        assert_eq!((c.queries, c.rewrite_unsat, c.checked), (12, 5, 4));
        assert_eq!((c.confirmed, c.inconclusive, c.contradicted), (1, 2, 1));
        // Every model checked: d's is the checker's, k's replacement is discarded.
        assert_eq!(
            (c.models_checked, c.models_invalid, c.models_inconclusive),
            (6, 3, 1)
        );
        assert_eq!(
            (c.models_discarded, c.bit_vector, c.disagreements()),
            (2, 2, 4)
        );
        // f, i, j and l; g's unknown was the solver's own.
        assert_eq!(c.made_unknown, 4);
        assert_eq!(c.saved, vec!["/x/d", "/x/f", "/x/k", "/x/l"]);
    }

    /// A query file in its own directory, for the tests that call solvers.
    fn query_file(name: &str, src: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("ausweg-test-{name}-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("query.smt2");
        std::fs::write(&f, src).unwrap();
        f
    }

    fn have_yices() -> bool {
        let found = find_on_path("yices-smt2").is_some();
        if !found {
            eprintln!("skipped: yices-smt2 is not installed");
        }
        found
    }

    // x + 1 == 0 holds for x = 255 only.
    const WRAPS: &str = "(set-logic QF_AUFBV)\n(declare-fun p_x () (_ BitVec 8))\n(assert (= (bvadd p_x #x01) #x00))\n(check-sat)\n(get-model)\n";

    #[test]
    fn a_wrong_or_unreadable_model_is_caught() {
        if !have_yices() {
            return;
        }
        let f = query_file("model", WRAPS);
        let budget = Duration::from_secs(10);
        let model = |x: u32| {
            render(
                &Answer::Sat(vec![("p_x".into(), 8, BigUint::from(x))]),
                None,
            )
        };
        assert_eq!(
            check_model(&f, WRAPS, &model(255), Some(budget), "t")
                .unwrap()
                .0,
            ModelCheck::Valid
        );
        assert!(matches!(
            check_model(&f, WRAPS, &model(0), Some(budget), "t")
                .unwrap()
                .0,
            ModelCheck::Invalid(_)
        ));
        // A literal too wide for its variable.
        let wide = "sat\n((define-fun p_x () (_ BitVec 8) (_ bv256 8)))\n";
        assert!(matches!(
            check_model(&f, WRAPS, wide, Some(budget), "t").unwrap().0,
            ModelCheck::Invalid(_)
        ));
        // The 0.7.0 bug: a model Halmos could not read at all.
        assert!(matches!(
            check_model(&f, WRAPS, "sat\n(= p_x #b11111111)\n", Some(budget), "t")
                .unwrap()
                .0,
            ModelCheck::Invalid(_)
        ));
    }

    #[test]
    fn a_wrong_model_from_the_rewrite_is_replaced_by_the_bit_vector_answer() {
        if !have_yices() {
            return;
        }
        saving_to("replace");
        let f = query_file("replace", WRAPS);
        let o = Outcome {
            answer: Answer::Sat(vec![("p_x".into(), 8, BigUint::from(0u32))]),
            passthrough: None,
            by: By::Rewrite,
            rewrite_out: Some("sat\n((p_x 0))\n".into()),
            run: Some(SolverRun {
                command: vec!["z3".into(), "-T:10".into()],
                input: f.clone(),
                budget: Duration::from_secs(10),
                took: Duration::from_millis(30),
            }),
        };
        let mut rec = Record::default();
        let deadline = || Instant::now() + Duration::from_secs(10);
        let (a, p) = checked(
            &f,
            WRAPS,
            CheckMode::DEFAULT,
            o,
            Duration::from_secs(10),
            Duration::from_secs(10),
            deadline(),
            &mut rec,
        )
        .unwrap();
        assert_eq!(a, Answer::Sat(Vec::new()));
        assert_eq!(
            read_model(p.as_deref().unwrap())[0].2,
            BigUint::from(255u32)
        );
        assert_eq!(rec.model.as_deref(), Some("invalid"));
        assert_eq!(rec.replacement.as_deref(), Some("valid"));
        // Everything to reproduce it: the rejected model, the validator's
        // answer to it, the replacement and its check, and the budgets.
        let saved = PathBuf::from(rec.saved.unwrap());
        let read = |name: &str| std::fs::read_to_string(saved.join(name)).unwrap_or_default();
        assert!(read("candidate.out").contains("(define-fun p_x () (_ BitVec 8) #x00)"));
        assert!(read("model-check.smt2").contains("(assert (= p_x (_ bv0 8)))"));
        assert_eq!(first_line(&read("model-check.out")), "unsat");
        assert_eq!(first_line(&read("replacement.out")), "sat");
        assert_eq!(first_line(&read("replacement-check.out")), "sat");
        let about: serde_json::Value = serde_json::from_str(&read("about.json")).unwrap();
        assert_eq!(about["halmos_got"], "sat");
        assert_eq!(about["check_timeout_seconds"], 10);
        assert!(about["check_budget_seconds"].as_f64().unwrap() > 9.0);
        // Every run: the rewrite's, the check of its model, the replacement and
        // the replacement's check, each with the command it ran.
        let runs: Vec<&str> = about["runs"]
            .as_array()
            .unwrap()
            .iter()
            .map(|r| r["output"].as_str().unwrap())
            .collect();
        assert_eq!(
            runs,
            [
                "rewrite.out",
                "model-check.out",
                "replacement.out",
                "replacement-check.out"
            ]
        );
        // Every run with its budget and time; a check also says whether it was
        // stopped.
        for r in about["runs"].as_array().unwrap() {
            assert!(
                r["budget_seconds"].as_f64().is_some() && r["seconds"].as_f64().is_some(),
                "{r}"
            );
        }
        assert_eq!(about["runs"][0]["budget_seconds"], 10.0);
        let check = &about["runs"][1];
        assert!(
            check["command"].as_str().unwrap().contains("--timeout=10"),
            "{check}"
        );
        assert_eq!(check["stopped"], false);
        assert!(
            about["fallback_version"]
                .as_str()
                .unwrap()
                .contains("Yices")
        );
    }

    // The example from Step 17: x + y < x needs the sum to wrap.
    const OVERFLOWS: &str = "(set-logic QF_AUFBV)\n(declare-fun p_x () (_ BitVec 256))\n(declare-fun p_y () (_ BitVec 256))\n(assert (bvult (bvadd p_x p_y) p_x))\n(check-sat)\n(get-model)\n";

    #[test]
    fn a_false_unsat_is_contradicted_and_halmos_gets_the_real_model() {
        if !have_yices() {
            return;
        }
        saving_to("unsat");
        let f = query_file("unsat", OVERFLOWS);
        // A rewrite that forgot the wraparound would answer unsat.
        let wrong = || Outcome {
            answer: Answer::Unsat,
            passthrough: None,
            by: By::Rewrite,
            rewrite_out: Some("unsat\n".into()),
            run: None,
        };
        let deadline = || Instant::now() + Duration::from_secs(20);
        for mode in [CheckMode::All, CheckMode::Sample { every: 1, seed: 0 }] {
            let mut rec = Record::default();
            let (a, p) = checked(
                &f,
                OVERFLOWS,
                mode,
                wrong(),
                Duration::from_secs(10),
                Duration::from_secs(10),
                deadline(),
                &mut rec,
            )
            .unwrap();
            assert_eq!(a, Answer::Sat(Vec::new()));
            assert_eq!(rec.check, "contradicted");
            assert_eq!(rec.model.as_deref(), Some("valid"));
            let saved = PathBuf::from(rec.saved.unwrap());
            for file in ["original.smt2", "rewrite.out", "checker.out", "about.json"] {
                assert!(saved.join(file).is_file(), "{file}");
            }
            // Halmos reads x and y from the output, and they do overflow.
            let m = read_model(p.as_deref().unwrap());
            let (x, y) = (&m[0].2, &m[1].2);
            assert!((x + y) % pow2(256) < *x);
        }
        // Not picked by the sample: the rewrite's answer stands.
        let mut rec = Record::default();
        let never = CheckMode::Sample {
            every: u64::MAX,
            seed: 3,
        };
        if !never.picks(OVERFLOWS) {
            let (a, _) = checked(
                &f,
                OVERFLOWS,
                never,
                wrong(),
                Duration::from_secs(10),
                Duration::from_secs(10),
                deadline(),
                &mut rec,
            )
            .unwrap();
            assert_eq!((a, rec.check.as_str()), (Answer::Unsat, "unchecked"));
        }
    }

    // x / 2 > x is impossible for division, but an uninterpreted f_evm_bvudiv
    // can return anything: the abstract query is sat, the refined one unsat.
    const HALVES: &str = "(set-logic QF_AUFBV)\n(declare-fun f_evm_bvudiv_256 ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))\n(declare-fun p_x () (_ BitVec 256))\n(assert (bvugt (f_evm_bvudiv_256 p_x (_ bv2 256)) p_x))\n(check-sat)\n(get-model)\n";

    #[test]
    fn refines_like_halmos() {
        let r = refine(HALVES);
        assert!(r.contains("(define-fun f_evm_bvudiv_256 ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256) (ite (= y (_ bv0 256)) (_ bv0 256) (bvudiv x y)))"));
        assert!(!r.contains("declare-fun f_evm_"));
        let mul = "(declare-fun f_evm_bvmul_512 ((_ BitVec 512) (_ BitVec 512)) (_ BitVec 512))";
        assert_eq!(
            refine(mul),
            "(define-fun f_evm_bvmul_512 ((x (_ BitVec 512)) (y (_ BitVec 512))) (_ BitVec 512) (bvmul x y))"
        );
        assert_eq!(refine(WRAPS), WRAPS);
    }

    #[test]
    fn an_unsat_about_evm_division_is_checked_against_its_meaning() {
        if !have_yices() {
            return;
        }
        let f = query_file("refine", HALVES);
        let left = || Some(Duration::from_secs(20));
        let (c, _) = check_unsat(&f, HALVES, &left).unwrap();
        assert!(matches!(c, UnsatCheck::Confirmed));
    }

    /// This test thread's checker: `sh -c <script> -- <query file>`.
    fn fake_checker(script: &str) {
        TEST_CHECKER.with(|c| {
            *c.borrow_mut() = Some(vec!["sh".into(), "-c".into(), script.into(), "--".into()])
        });
    }

    /// Where this test thread saves disagreements: a new directory.
    fn saving_to(name: &str) -> PathBuf {
        let d =
            std::env::temp_dir().join(format!("ausweg-test-saved-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        TEST_SAVE_DIR.with(|s| *s.borrow_mut() = Some(d.clone()));
        d
    }

    /// The rewrite's answer x = 0 to WRAPS, which needs x = 255.
    fn wrong_rewrite_model() -> Outcome {
        Outcome {
            answer: Answer::Sat(vec![("p_x".into(), 8, BigUint::from(0u32))]),
            passthrough: None,
            by: By::Rewrite,
            rewrite_out: Some("sat\n((p_x 0))\n".into()),
            run: None,
        }
    }

    #[test]
    fn an_unconfirmed_model_is_unknown_in_every_mode() {
        // A checker that settles nothing: x = 0 is neither confirmed nor refuted.
        fake_checker("echo unknown");
        let f = query_file("unconfirmed", WRAPS);
        let ten = Duration::from_secs(10);
        let run = |mode| {
            let mut rec = Record::default();
            let (a, _) = checked(
                &f,
                WRAPS,
                mode,
                wrong_rewrite_model(),
                ten,
                ten,
                Instant::now() + ten,
                &mut rec,
            )
            .unwrap();
            (a, rec.model)
        };
        // GPT's case: Halmos would read x = 0 as a counterexample. Sampling is
        // for unsat answers only: a model is confirmed in every mode.
        for mode in [CheckMode::All, CheckMode::DEFAULT] {
            assert_eq!(run(mode), (Answer::Unknown, Some("inconclusive".into())));
        }
    }

    #[test]
    fn an_unconfirmed_replacement_is_unknown_in_every_mode() {
        if !have_yices() {
            return;
        }
        // The checker refutes the rewrite's x = 0, then cannot settle the
        // bit-vector solver's x = 255.
        fake_checker(r#"case "$1" in *replacement-check*) echo unknown;; *) echo unsat;; esac"#);
        saving_to("unconfirmed-swap");
        let f = query_file("unconfirmed-swap", WRAPS);
        let ten = Duration::from_secs(10);
        let run = |mode| {
            let mut rec = Record::default();
            let (a, p) = checked(
                &f,
                WRAPS,
                mode,
                wrong_rewrite_model(),
                ten,
                ten,
                Instant::now() + ten,
                &mut rec,
            )
            .unwrap();
            (a, p, rec)
        };
        for mode in [CheckMode::All, CheckMode::DEFAULT] {
            let (a, p, rec) = run(mode);
            assert_eq!(
                (a, p, rec.model.as_deref()),
                (Answer::Unknown, None, Some("invalid"))
            );
            assert_eq!(rec.replacement.as_deref(), Some("inconclusive"));
            let saved = PathBuf::from(rec.saved.unwrap());
            let read = |name: &str| std::fs::read_to_string(saved.join(name)).unwrap();
            let about: serde_json::Value = serde_json::from_str(&read("about.json")).unwrap();
            assert_eq!(about["halmos_got"], "unknown");
            assert_eq!(first_line(&read("replacement-check.out")), "unknown");
        }
    }

    #[test]
    fn a_model_from_the_checker_is_checked_like_any_other() {
        // The checker contradicts the rewrite's unsat with a model it cannot
        // then confirm: Halmos gets unknown, sampling or not.
        fake_checker(
            r#"case "$1" in *model-check*) echo unknown;; *) printf 'sat\n((define-fun p_x () (_ BitVec 8) #xff))\n';; esac"#,
        );
        saving_to("contradicted-unconfirmed");
        let f = query_file("contradicted-unconfirmed", WRAPS);
        let ten = Duration::from_secs(10);
        for mode in [CheckMode::All, CheckMode::Sample { every: 1, seed: 0 }] {
            let o = Outcome {
                answer: Answer::Unsat,
                passthrough: None,
                by: By::Rewrite,
                rewrite_out: Some("unsat\n".into()),
                run: None,
            };
            let mut rec = Record::default();
            let (a, _) =
                checked(&f, WRAPS, mode, o, ten, ten, Instant::now() + ten, &mut rec).unwrap();
            assert_eq!(
                (a, rec.check.as_str(), rec.model.as_deref()),
                (Answer::Unknown, "contradicted", Some("inconclusive"))
            );
        }
    }

    // Names in |...|, as Halmos may quote them: one that does not need the
    // quotes, one that does.
    const QUOTED: &str = "(set-logic QF_AUFBV)\n(declare-fun |p_y_uint8_abc1234_00| () (_ BitVec 8))\n(declare-fun |p_z[0]_uint8_abc1234_01| () (_ BitVec 8))\n(assert (= (bvadd |p_y_uint8_abc1234_00| #x01) #x00))\n(assert (= |p_z[0]_uint8_abc1234_01| #x07))\n(check-sat)\n(get-model)\n";

    #[test]
    fn quoted_names_are_read_and_checked() {
        let mut g = Graph::default();
        for c in &parse_sexps(QUOTED).unwrap() {
            g.command(c).unwrap();
        }
        assert_eq!(translate(&g).model_vars.len(), 2);
        if !have_yices() {
            return;
        }
        let f = query_file("quoted", QUOTED);
        let model = |y: &str, z: &str| {
            format!(
                "sat\n((define-fun |p_y_uint8_abc1234_00| () (_ BitVec 8) {y})\n (define-fun |p_z[0]_uint8_abc1234_01| () (_ BitVec 8) {z}))\n"
            )
        };
        let check = |text: &str| {
            check_model(&f, QUOTED, text, Some(Duration::from_secs(10)), "t")
                .unwrap()
                .0
        };
        assert_eq!(check(&model("#xff", "#x07")), ModelCheck::Valid);
        assert!(matches!(
            check(&model("#x00", "#x07")),
            ModelCheck::Invalid(_)
        ));
        assert!(matches!(
            check(&model("#xff", "#x00")),
            ModelCheck::Invalid(_)
        ));
        // GPT's case: one name quoted and one not, the quoted one wrong.
        let mixed = "sat\n((define-fun |p_y_uint8_abc1234_00| () (_ BitVec 8) #x00)\n (define-fun p_z[0]_uint8_abc1234_01 () (_ BitVec 8) #x07))\n";
        assert!(matches!(check(mixed), ModelCheck::Invalid(_)));
        // A value for a name the query does not declare.
        let extra = "sat\n((define-fun |p_y_uint8_abc1234_00| () (_ BitVec 8) #xff)\n (define-fun |p_z[0]_uint8_abc1234_01| () (_ BitVec 8) #x07)\n (define-fun p_w_uint8_abc1234_02 () (_ BitVec 8) #x00))\n";
        assert!(matches!(check(extra), ModelCheck::Invalid(_)));
        // The rewrite reads quoted names back from the integer solver, which
        // writes the quotes only where they are needed.
        if find_on_path("z3").is_some() {
            let o = solve_unchecked(&f, Duration::from_secs(20)).unwrap();
            assert_eq!(o.by, By::Rewrite);
            let Answer::Sat(v) = &o.answer else {
                panic!("not sat: {:?}", o.answer)
            };
            let mut vals: Vec<_> = v
                .iter()
                .map(|(n, _, x)| (n.as_str(), x.to_u32().unwrap()))
                .collect();
            vals.sort();
            assert_eq!(
                vals,
                [
                    ("|p_y_uint8_abc1234_00|", 255),
                    ("|p_z[0]_uint8_abc1234_01|", 7)
                ]
            );
            assert_eq!(check(&render(&o.answer, None)), ModelCheck::Valid);
        }
    }

    /// What Halmos's own parser (`halmos.solve.parse_model_str`) reads from a
    /// solver's output: (name, width, value). None without Halmos's Python.
    fn halmos_reads(out: &str) -> Option<Vec<(String, u32, BigUint)>> {
        use std::io::Write;
        const PARSE: &str = "import json, sys\nfrom halmos.solve import parse_model_str\nm = parse_model_str(sys.stdin.read())\nprint(json.dumps({k: [v.size_bits, str(v.value)] for k, v in m.items()}))";
        // The Python the `halmos` command runs on, else python3.
        let shebang = find_on_path("halmos")
            .and_then(|h| std::fs::read_to_string(h).ok())
            .and_then(|s| Some(s.lines().next()?.strip_prefix("#!")?.to_string()));
        let mut cmd: Vec<String> = shebang
            .as_deref()
            .unwrap_or("python3")
            .split_whitespace()
            .map(String::from)
            .collect();
        cmd.extend(["-c".to_string(), PARSE.to_string()]);
        let mut child = Command::new(&cmd[0])
            .args(&cmd[1..])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .spawn()
            .ok()?;
        child.stdin.take()?.write_all(out.as_bytes()).ok()?;
        let o = child.wait_with_output().ok()?;
        if !o.status.success() {
            return None;
        }
        let m: std::collections::BTreeMap<String, (u32, String)> =
            serde_json::from_slice(&o.stdout).ok()?;
        Some(
            m.into_iter()
                .map(|(n, (w, v))| (n, w, v.parse().unwrap()))
                .collect(),
        )
    }

    #[test]
    fn reads_what_halmos_reads() {
        // Models as yices, z3 and bitwuzla write them, names quoted or not.
        let outputs = [
            "sat\n(define-fun p_x_uint8_abc1234_00 () (_ BitVec 8) #b11111111)\n(define-fun |p_y_uint8_abc1234_01| () (_ BitVec 8) #x07)\n",
            "sat\n(\n  (define-fun |p_z[0]_uint256_abc1234_02| () (_ BitVec 256)\n    #x00000000000000000000000000000000000000000000000000000000000000ff)\n  (define-fun p_x_uint8_abc1234_00 () (_ BitVec 8)\n    #xFE)\n  (define-fun f_g ((x (_ BitVec 8))) (_ BitVec 8) x)\n  (define-fun p_b_bool_abc1234_03 () Bool true)\n)\n",
            "sat\n(\n  (define-fun halmos_block_timestamp_depth1_abc1234 () (_ BitVec 64) (_ bv1700000000 64))\n  (define-fun |p_y_uint8_abc1234_01| () (_ BitVec 8) (_ bv256 8))\n  (define-fun other_uint8_abc1234_04 () (_ BitVec 8) #x01)\n)\n",
        ];
        let expected: [&[(&str, u32, u64)]; 3] = [
            &[
                ("p_x_uint8_abc1234_00", 8, 255),
                ("p_y_uint8_abc1234_01", 8, 7),
            ],
            &[
                ("p_x_uint8_abc1234_00", 8, 254),
                ("p_z[0]_uint256_abc1234_02", 256, 255),
            ],
            &[
                ("halmos_block_timestamp_depth1_abc1234", 64, 1_700_000_000),
                ("p_y_uint8_abc1234_01", 8, 256),
            ],
        ];
        let mut compared = 0;
        for (out, want) in outputs.iter().zip(expected) {
            let mut ours = read_model(out);
            ours.sort();
            let want: Vec<_> = want
                .iter()
                .map(|(n, w, v)| (n.to_string(), *w, BigUint::from(*v)))
                .collect();
            assert_eq!(ours, want, "{out}");
            if let Some(mut theirs) = halmos_reads(out) {
                theirs.sort();
                assert_eq!(ours, theirs, "Halmos reads {out} differently");
                compared += 1;
            }
        }
        if compared == 0 {
            eprintln!("not compared with Halmos's parser: Halmos's Python was not found");
        }
    }

    #[test]
    fn the_checks_of_one_answer_share_one_budget() {
        // HALVES has an abstract division, so its unsat is checked twice: the
        // abstract query (0.6 s here, sat), then the refined one, which this
        // checker never answers. With 1 s for both, the refined query gets the
        // 0.4 s left, and is stopped then.
        fake_checker(r#"case "$1" in *refined*) exec sleep 10;; *) sleep 0.6; echo sat;; esac"#);
        let f = query_file("budget", HALVES);
        let o = Outcome {
            answer: Answer::Unsat,
            passthrough: None,
            by: By::Rewrite,
            rewrite_out: Some("unsat\n".into()),
            run: None,
        };
        let twenty = Duration::from_secs(20);
        let started = Instant::now();
        let mut rec = Record::default();
        let (a, _) = checked(
            &f,
            HALVES,
            CheckMode::All,
            o,
            twenty,
            Duration::from_secs(1),
            started + twenty,
            &mut rec,
        )
        .unwrap();
        let took = started.elapsed();
        assert!(
            took >= Duration::from_millis(900) && took < Duration::from_millis(1400),
            "{took:?}"
        );
        assert_eq!((a, rec.check.as_str()), (Answer::Unknown, "inconclusive"));
        // A query with no time left gets no check at all.
        let mut rec = Record::default();
        let o = Outcome {
            answer: Answer::Unsat,
            passthrough: None,
            by: By::Rewrite,
            rewrite_out: Some("unsat\n".into()),
            run: None,
        };
        let started = Instant::now();
        let (a, _) = checked(
            &f,
            HALVES,
            CheckMode::All,
            o,
            twenty,
            twenty,
            started,
            &mut rec,
        )
        .unwrap();
        assert!(started.elapsed() < Duration::from_millis(100));
        assert_eq!((a, rec.check.as_str()), (Answer::Unknown, "inconclusive"));
    }

    #[test]
    fn a_stopped_checker_stops_what_it_started() {
        // A checker that is a script around the real work, here a sleep that
        // ignores every time limit: the script waits for it, as a wrapper
        // waits for its solver.
        let dir = std::env::temp_dir().join(format!("ausweg-test-group-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let pid_file = dir.join("pid");
        let _ = std::fs::remove_file(&pid_file);
        let script = format!("sleep 30 & echo $! > '{}'; wait", pid_file.display());
        let cmd = vec!["sh".to_string(), "-c".to_string(), script, "--".to_string()];
        let f = query_file("group", WRAPS);
        let started = Instant::now();
        let out = run_until(&cmd, &f, started + Duration::from_secs(1)).unwrap();
        assert_eq!(out, None);
        assert!(started.elapsed() < Duration::from_millis(1500));
        let pid = std::fs::read_to_string(&pid_file)
            .unwrap()
            .trim()
            .to_string();
        // Gone, or a zombie about to be reaped: either way, no longer running.
        let running = || {
            let o = Command::new("ps")
                .args(["-o", "stat=", "-p", &pid])
                .output()
                .unwrap();
            let stat = String::from_utf8_lossy(&o.stdout).trim().to_string();
            !stat.is_empty() && !stat.starts_with('Z')
        };
        let by = Instant::now() + Duration::from_secs(2);
        while running() && Instant::now() < by {
            std::thread::sleep(Duration::from_millis(20));
        }
        let still = running();
        if still {
            let _ = Command::new("kill").args(["-9", &pid]).status();
        }
        assert!(!still, "the checker's child {pid} still runs");
    }

    #[test]
    fn the_rewrite_gets_the_overflow_right() {
        if find_on_path("z3").is_none() {
            eprintln!("skipped: z3 is not installed");
            return;
        }
        let f = query_file("rewrite", OVERFLOWS);
        let o = solve_unchecked(&f, Duration::from_secs(20)).unwrap();
        assert_eq!(o.by, By::Rewrite);
        assert!(matches!(o.answer, Answer::Sat(_)));
    }
}
