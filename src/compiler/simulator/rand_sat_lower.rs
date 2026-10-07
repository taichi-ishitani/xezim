//! §18 — `randomize()` through `rand_sat`: the constraints bit-blasted onto
//! a SAT solver, for rand variables of any width.
//!
//! The interval CSP (`rand_csp`) holds values in `i128`/`u64`, so a rand set
//! with a variable wider than 64 bits never reached a solver: the trial loop
//! only re-drew, and `(x >> 8) == 0` held by chance alone (issue #261). This
//! lowers the same inputs the CSP gets — the rand scalars and 1-D arrays, the
//! enabled constraint blocks with their soft ranks — into a `rand_sat`
//! problem, solves it, and writes the values back. A shape it does not model
//! (a rand sub-object, a struct member, an assoc array, …) answers
//! `NotApplicable` and leaves the caller's other paths in charge.

use super::rand_csp::CspOutcome;
use super::rand_sat as rs;
use super::*;
use crate::ast::decl::DistWeight;
use crate::ast::{Identifier, Span};
use crate::compiler::elaborate::{is_type_real, is_type_signed, resolve_type_width};

/// When `randomize()` goes to `rand_sat` (`XEZIM_RAND_SAT`): `auto` (the
/// default) only for a rand set with a variable wider than 64 bits, `force`
/// for every set it can lower (to exercise it), `off` never.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum RandSatMode {
    Auto,
    Force,
    Off,
}

pub(super) fn rand_sat_mode() -> RandSatMode {
    static MODE: std::sync::OnceLock<RandSatMode> = std::sync::OnceLock::new();
    *MODE.get_or_init(|| match std::env::var("XEZIM_RAND_SAT").as_deref() {
        Ok("force") => RandSatMode::Force,
        Ok("off") => RandSatMode::Off,
        _ => RandSatMode::Auto,
    })
}

/// A value of the caller's evaluator as two-state bits; `None` for X/Z,
/// real, or a fill literal (`'1`), which `rand_sat` does not model.
fn bits_of(v: &Value) -> Option<rs::Bits> {
    if v.has_xz() || v.is_real || v.is_fill || v.width == 0 {
        return None;
    }
    let mut x = num_bigint::BigUint::default();
    for i in 0..v.width {
        if v.get_bit(i as usize) == LogicBit::One {
            x.set_bit(u64::from(i), true);
        }
    }
    Some(rs::Bits::new(v.width, v.is_signed, x))
}

fn value_of(b: &rs::Bits) -> Value {
    let w = b.width();
    let mut v = if w <= 64 {
        Value::from_u64(b.bits().iter_u64_digits().next().unwrap_or(0), w)
    } else {
        let mut words: Vec<u64> = b.bits().iter_u64_digits().collect();
        words.resize(w.div_ceil(64) as usize, 0);
        Value::from_words(&words, w)
    };
    v.is_signed = b.signed();
    v
}

/// What a `rand_sat` call evaluates through the simulator.
enum SatFun {
    /// A state expression that reads `foreach` indices (or a call that reads
    /// rand variables): evaluated with `binds` bound to the arguments.
    Eval {
        expr: Expression,
        binds: Vec<String>,
    },
}

struct SatFuncs<'s> {
    sim: &'s mut Simulator,
    funs: Vec<SatFun>,
}

impl rs::FuncEval for SatFuncs<'_> {
    fn call(&mut self, f: rs::FuncId, args: &[rs::Bits]) -> rs::Bits {
        let SatFun::Eval { expr, binds } = &self.funs[f.0 as usize];
        let frame: HashMap<String, Value> = binds
            .iter()
            .cloned()
            .zip(args.iter().map(value_of))
            .collect();
        self.sim.push_local_frame(frame);
        let v = self.sim.eval_expr(expr);
        self.sim.pop_local_frame();
        bits_of(&v)
            .unwrap_or_else(|| rs::Bits::new(v.width.max(1), v.is_signed, Default::default()))
    }
}

/// A rand collection as a `rand_sat` array: its id, its first index, and
/// whether a constraint reads its size.
struct SatArr {
    id: rs::ArrayId,
    lo: i64,
    kind: CollKind,
    sized: bool,
}

/// The lowering state of one `randomize()`.
struct SatTr {
    p: rs::Problem,
    scalars: HashMap<String, rs::VarId>,
    arrays: HashMap<String, SatArr>,
    /// Enclosing `foreach` indices over rand arrays: name, loop, first index.
    loops: Vec<(String, rs::LoopId, i64)>,
    /// `foreach` indices over state arrays, unrolled: name and value.
    consts: Vec<(String, Value)>,
    funs: Vec<SatFun>,
    receiver: Option<String>,
    /// Per `rand_sat` block, per item: the constraint and item it lowers.
    origins: Vec<Vec<(usize, usize)>>,
}

impl SatTr {
    fn loop_of(&self, n: &str) -> Option<(rs::LoopId, i64)> {
        self.loops
            .iter()
            .rev()
            .find(|l| l.0 == n)
            .map(|l| (l.1, l.2))
    }
}

/// Every variable outcome of the lowering.
type Lw<T> = Option<T>;

impl Simulator {
    /// Solve one `randomize()` with `rand_sat`. The arguments are those of
    /// `rand_csp_solve`; the values are written to the object on `Sat`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn rand_sat_solve(
        &mut self,
        handle: usize,
        constraints: &[ClassConstraint],
        constraint_depth: &[usize],
        rand_props: &[(String, u32)],
        signed_props: &HashSet<String>,
        enum_props: &HashMap<String, String>,
        colls: &[RandColl],
        array_enums: &HashMap<String, String>,
        conflict: &mut Vec<(usize, usize)>,
    ) -> CspOutcome {
        // Ctrl-C / SIGTERM: as the trial loop, stop and let the run shut
        // down (a `while (!o.randomize())` loop must not keep calling).
        if interrupt_requested() {
            self.sat_interrupted();
            return CspOutcome::Unsat;
        }
        let Some(tr) = self.sat_lower(
            handle,
            constraints,
            constraint_depth,
            rand_props,
            signed_props,
            enum_props,
            colls,
            array_enums,
        ) else {
            return CspOutcome::NotApplicable;
        };
        let SatTr {
            p,
            scalars,
            arrays,
            funs,
            origins,
            ..
        } = tr;
        let mut core = Vec::new();
        let p_dbg = if std::env::var_os("XEZIM_RAND_SAT_DEBUG").is_some() {
            format!("{p:?}")
        } else {
            String::new()
        };
        let mut rng = *self.cur_rng();
        let out = {
            // The wall-clock budget of this randomize() (`+xezim_rand_timeout`)
            // and a SIGTERM stop the search, as they stop the other paths.
            let limits = rs::Limits {
                deadline: self.randomize_budget_deadline,
                interrupted: interrupt_requested,
            };
            let mut funcs = SatFuncs { sim: self, funs };
            p.solve_core(&mut rng, &mut funcs, Some(limits), &mut core)
        };
        *self.cur_rng() = rng;
        if std::env::var_os("XEZIM_RAND_SAT_DEBUG").is_some() {
            eprintln!(
                "[rand_sat] {:?}\n[rand_sat] -> {:?}",
                p_dbg,
                out.as_ref().map(|_| "sat")
            );
        }
        let sol = match out {
            Ok((sol, _)) => sol,
            Err(rs::SolveError::Unsat) => {
                // The constraint items in conflict, for `XEZIM_RAND_DIAG`.
                *conflict = core
                    .iter()
                    .filter_map(|&(b, i)| origins.get(b)?.get(i).copied())
                    .collect();
                conflict.sort_unstable();
                conflict.dedup();
                return CspOutcome::Unsat;
            }
            Err(rs::SolveError::Stopped) => {
                // Out of time: the budget report of the other paths, then
                // a failed call (§18.6.1). A SIGTERM ends the run.
                if interrupt_requested() {
                    self.sat_interrupted();
                } else {
                    let cn = self
                        .heap
                        .get(handle)
                        .and_then(|o| o.as_ref())
                        .map(|i| i.class_name.clone())
                        .unwrap_or_default();
                    self.take_randomize_budget(handle, &cn, constraints);
                }
                return CspOutcome::Unsat;
            }
            Err(rs::SolveError::Unknown) => return CspOutcome::GaveUp,
        };
        for (name, v) in &scalars {
            let val = value_of(sol.var(*v));
            if let Some(Some(inst)) = self.heap.get_mut(handle) {
                inst.properties.insert(name.clone(), val);
            }
        }
        for c in colls {
            let Some(a) = arrays.get(&c.prop) else {
                continue;
            };
            let elems = sol.array(a.id);
            if a.kind == CollKind::Dyn {
                self.resize_coll(&c.scoped, elems.len() as u64);
                self.module.dynamic_arrays.insert(c.scoped.clone());
            }
            for (i, b) in elems.iter().enumerate() {
                let key = format!("{}[{}]", c.scoped, a.lo + i as i64);
                self.write_coll_elem(&key, value_of(b));
            }
        }
        // The ordinary checker has the last word, as for the CSP.
        if self.rand_items_accept(handle, constraints, colls, &mut false) {
            CspOutcome::Sat
        } else {
            CspOutcome::GaveUp
        }
    }

    /// The trial loop's response to an interrupt.
    fn sat_interrupted(&mut self) {
        acknowledge_interrupt();
        eprintln!(
            "[xezim] interrupted at time {} — finalizing waveform dumps",
            self.time
        );
        self.finished = true;
    }

    #[allow(clippy::too_many_arguments)]
    fn sat_lower(
        &mut self,
        handle: usize,
        constraints: &[ClassConstraint],
        constraint_depth: &[usize],
        rand_props: &[(String, u32)],
        signed_props: &HashSet<String>,
        enum_props: &HashMap<String, String>,
        colls: &[RandColl],
        array_enums: &HashMap<String, String>,
    ) -> Lw<SatTr> {
        let mut t = SatTr {
            p: rs::Problem::new(),
            scalars: HashMap::default(),
            arrays: HashMap::default(),
            loops: Vec::new(),
            consts: Vec::new(),
            funs: Vec::new(),
            receiver: self.rand_receiver.clone(),
            origins: Vec::new(),
        };
        // Enum members, as `inside` items of the lowest rank.
        let mut domains: Vec<rs::Item> = Vec::new();
        for c in colls {
            if c.is_object_elem || c.nested || c.kind == CollKind::Assoc || c.width == 0 {
                return None;
            }
            let signed = self.class_prop_signed_of(handle, &c.prop);
            let size = match c.kind {
                CollKind::Fixed => rs::ArraySize::Fixed((c.hi - c.lo + 1).max(0) as usize),
                _ => rs::ArraySize::Dynamic { max: 1 << 16 },
            };
            let id = t.p.array(&c.prop, c.width, signed, size);
            t.arrays.insert(
                c.prop.clone(),
                SatArr {
                    id,
                    lo: if c.kind == CollKind::Fixed { c.lo } else { 0 },
                    kind: c.kind,
                    sized: false,
                },
            );
            if let Some(set) = array_enums
                .get(&c.prop)
                .and_then(|tn| self.sat_enum_set(tn, c.width, signed))
            {
                let l = t.p.loop_var();
                domains.push(rs::build::foreach(
                    id,
                    l,
                    vec![rs::build::item(rs::build::inside(
                        rs::build::elem(id, rs::build::lp(l)),
                        set,
                    ))],
                ));
            }
        }
        for (name, w) in rand_props {
            if t.arrays.contains_key(name) {
                continue;
            }
            if *w == 0 {
                return None;
            }
            let signed = signed_props.contains(name);
            let v = t.p.var(name, *w, signed);
            t.scalars.insert(name.clone(), v);
            if let Some(set) = enum_props
                .get(name)
                .and_then(|tn| self.sat_enum_set(tn, *w, signed))
            {
                domains.push(rs::build::item(rs::build::inside(rs::build::var(v), set)));
            }
        }
        t.origins.push(Vec::new());
        t.p.constraint(0, domains);

        // §18.5.14.1 ranks, as `rand_csp` orders them: a deeper (parent)
        // class below a derived one, a later block above an earlier one, the
        // inline block above all.
        let mut order: Vec<usize> = (0..constraints.len()).collect();
        let rank = |i: usize| -> (bool, std::cmp::Reverse<usize>, usize) {
            let c = &constraints[i];
            let inline = c.name.name == "__inline__";
            let depth = constraint_depth.get(i).copied().unwrap_or(0);
            (inline, std::cmp::Reverse(depth), c.span.start)
        };
        order.sort_by_key(|&i| rank(i));
        for (prio, &i) in order.iter().enumerate() {
            let mut items = Vec::new();
            let mut from = Vec::new();
            for (ii, it) in constraints[i].items.iter().enumerate() {
                self.sat_item(&mut t, it, &mut items)?;
                from.resize(items.len(), (i, ii));
            }
            t.origins.push(from);
            t.p.constraint(prio as u32 + 1, items);
        }
        // An unconstrained dynamic array keeps its length (xezim does not
        // re-shape it; see `pick_size`).
        let fixed: Vec<(rs::ArrayId, usize)> = colls
            .iter()
            .filter_map(|c| {
                let a = t.arrays.get(&c.prop)?;
                (a.kind == CollKind::Dyn && !a.sized)
                    .then(|| (a.id, self.get_queue_size(&c.scoped) as usize))
            })
            .collect();
        for (id, n) in fixed {
            t.p.set_array_size(id, rs::ArraySize::Fixed(n));
        }
        Some(t)
    }

    fn sat_enum_set(&self, tn: &str, w: u32, signed: bool) -> Option<Vec<rs::SetItem>> {
        let members = self.module.enum_members.get(tn)?;
        if members.is_empty() {
            return None;
        }
        Some(
            members
                .iter()
                .map(|m| rs::build::val(rs::Expr::Const(rs::Bits::from_u64(w, signed, m.1))))
                .collect(),
        )
    }

    /// Lower one item into `out` (a `Block` flattens).
    fn sat_item(&mut self, t: &mut SatTr, it: &ConstraintItem, out: &mut Vec<rs::Item>) -> Lw<()> {
        use rs::build as b;
        match it {
            ConstraintItem::Expr(e) => out.push(b::item(self.sat_bool(t, e)?)),
            ConstraintItem::Inside {
                expr,
                range,
                is_dist,
                dist_weights,
                ..
            } => {
                let x = self.sat_expr(t, expr)?;
                if *is_dist {
                    let mut ds = Vec::with_capacity(range.len());
                    for (k, r) in range.iter().enumerate() {
                        let item = self.sat_range(t, r)?;
                        let weight = match dist_weights.get(k).and_then(|w| w.as_ref()) {
                            None => None,
                            Some(DistWeight::Each(w)) => {
                                Some(rs::Weight::Each(self.sat_expr(t, w)?))
                            }
                            Some(DistWeight::Total(w)) => {
                                Some(rs::Weight::Spread(self.sat_expr(t, w)?))
                            }
                        };
                        ds.push(rs::DistItem { item, weight });
                    }
                    out.push(b::dist(x, ds));
                } else {
                    let mut set = Vec::with_capacity(range.len());
                    for r in range {
                        set.push(self.sat_range(t, r)?);
                    }
                    out.push(b::item(b::inside(x, set)));
                }
            }
            ConstraintItem::Implication {
                condition,
                constraint,
                ..
            } => {
                let c = self.sat_bool(t, condition)?;
                let mut body = Vec::new();
                self.sat_item(t, constraint, &mut body)?;
                out.push(rs::Item::Implies(c, body));
            }
            ConstraintItem::IfElse {
                condition,
                then_item,
                else_item,
                ..
            } => {
                let c = self.sat_bool(t, condition)?;
                let mut th = Vec::new();
                self.sat_item(t, then_item, &mut th)?;
                let mut el = Vec::new();
                if let Some(e) = else_item {
                    self.sat_item(t, e, &mut el)?;
                }
                out.push(b::if_else(c, th, el));
            }
            ConstraintItem::Foreach {
                array, vars, item, ..
            } => {
                // One index over a rand 1-D array: a solver foreach.
                if let (Some(name), [Some(var)]) = (self.sat_member(t, array), vars.as_slice()) {
                    let a = t.arrays.get(&name)?;
                    let (id, lo) = (a.id, a.lo);
                    let l = t.p.loop_var();
                    t.loops.push((var.name.clone(), l, lo));
                    let mut body = Vec::new();
                    let r = self.sat_item(t, item, &mut body);
                    t.loops.pop();
                    r?;
                    out.push(b::foreach(id, l, body));
                    return Some(());
                }
                // A state (unpacked) array: unrolled over its current indices.
                // A packed vector's bits are not its elements; left to the
                // other paths.
                if self.sat_reads_rand(t, array)
                    || vars.len() != 1
                    || !self.sat_unpacked_state(array)
                {
                    return None;
                }
                let Some(Some(var)) = vars.first() else {
                    return None;
                };
                let n = self.sat_state_len(t, array)?;
                for i in 0..n {
                    let mut iv = Value::from_u64(i as u64, 32);
                    iv.is_signed = true;
                    t.consts.push((var.name.clone(), iv));
                    let r = self.sat_item(t, item, out);
                    t.consts.pop();
                    r?;
                }
            }
            ConstraintItem::Solve { before, after, .. } => {
                let refs = |t: &SatTr, ids: &[Identifier]| -> Vec<rs::VarRef> {
                    ids.iter()
                        .filter_map(|id| {
                            t.scalars
                                .get(&id.name)
                                .map(|v| rs::VarRef::Var(*v))
                                .or_else(|| t.arrays.get(&id.name).map(|a| rs::VarRef::Array(a.id)))
                        })
                        .collect()
                };
                let (bs, as_) = (refs(t, before), refs(t, after));
                if !bs.is_empty() && !as_.is_empty() {
                    t.p.solve_before(bs, as_);
                }
            }
            ConstraintItem::Soft(inner) => {
                let mut body = Vec::new();
                self.sat_item(t, inner, &mut body)?;
                out.extend(body.into_iter().map(b::soft));
            }
            ConstraintItem::Block(items) => {
                for i in items {
                    self.sat_item(t, i, out)?;
                }
            }
            ConstraintItem::Unique { exprs, .. } => {
                let mut es = Vec::new();
                for e in exprs {
                    // A whole fixed array names each of its elements.
                    if let Some(a) = self.sat_member(t, e).and_then(|n| t.arrays.get(&n)) {
                        if a.kind != CollKind::Fixed {
                            return None;
                        }
                        let id = a.id;
                        let n = match t.p.array_size(id) {
                            rs::ArraySize::Fixed(n) => n,
                            rs::ArraySize::Dynamic { .. } => return None,
                        };
                        es.extend((0..n).map(|i| b::elem(id, b::int(i as i64))));
                    } else {
                        es.push(self.sat_expr(t, e)?);
                    }
                }
                if es.len() > 1 {
                    out.push(rs::Item::Unique(es));
                }
            }
        }
        Some(())
    }

    fn sat_range(&mut self, t: &mut SatTr, r: &ConstraintRange) -> Lw<rs::SetItem> {
        Some(match r {
            ConstraintRange::Value(v) => self.sat_set_value(t, v)?,
            ConstraintRange::Range { lo, hi } => {
                rs::SetItem::Range(self.sat_expr(t, lo)?, self.sat_expr(t, hi)?)
            }
        })
    }

    fn sat_set_value(&mut self, t: &mut SatTr, v: &Expression) -> Lw<rs::SetItem> {
        Some(match &Self::unparen(v).kind {
            ExprKind::Range(lo, hi) => {
                rs::SetItem::Range(self.sat_expr(t, lo)?, self.sat_expr(t, hi)?)
            }
            _ => rs::SetItem::Value(self.sat_expr(t, v)?),
        })
    }

    /// A condition: the expression itself (its truth is non-zero).
    fn sat_bool(&mut self, t: &mut SatTr, e: &Expression) -> Lw<rs::Expr> {
        self.sat_expr(t, e)
    }

    /// The rand member an operand names: `x`, `this.x`, or `obj.x` for the
    /// receiver of an inline `obj.randomize() with {…}`.
    fn sat_member(&self, t: &SatTr, e: &Expression) -> Option<String> {
        let recv_ok = |r: &str| r == "this" || t.receiver.as_deref() == Some(r);
        let name = match &Self::unparen(e).kind {
            ExprKind::Ident(h)
                if h.root.is_none() && h.path.iter().all(|s| s.selects.is_empty()) =>
            {
                match h.path.len() {
                    1 => h.path[0].name.name.clone(),
                    2 if recv_ok(&h.path[0].name.name) => h.path[1].name.name.clone(),
                    _ => return None,
                }
            }
            ExprKind::MemberAccess { expr, member } => match &expr.kind {
                ExprKind::This => member.name.clone(),
                ExprKind::Ident(h) if h.path.len() == 1 && recv_ok(&h.path[0].name.name) => {
                    member.name.clone()
                }
                _ => return None,
            },
            _ => return None,
        };
        // A `foreach` index or an unrolled state index shadows a member.
        if t.loop_of(&name).is_some() || t.consts.iter().any(|c| c.0 == name) {
            return None;
        }
        (t.scalars.contains_key(&name) || t.arrays.contains_key(&name)).then_some(name)
    }

    /// Whether `e` reads a rand variable (or a rand array). A shape the
    /// walk does not look into (`with` clauses, patterns, …) may read one,
    /// so it counts as reading — the lowering then gives it up.
    fn sat_reads_rand(&self, t: &SatTr, e: &Expression) -> bool {
        if self.sat_member(t, e).is_some() {
            return true;
        }
        let mut found = false;
        Self::sat_walk(e, &mut |x| {
            if !found && (Self::sat_opaque(x) || self.sat_member(t, x).is_some()) {
                found = true;
            }
        });
        found
    }

    /// A node whose operands `sat_walk` does not visit.
    fn sat_opaque(e: &Expression) -> bool {
        !matches!(
            e.kind,
            ExprKind::Number(_)
                | ExprKind::StringLiteral(_)
                | ExprKind::TypeLiteral(_)
                | ExprKind::Ident(_)
                | ExprKind::Unary { .. }
                | ExprKind::Binary { .. }
                | ExprKind::Conditional { .. }
                | ExprKind::Concatenation(_)
                | ExprKind::Replication { .. }
                | ExprKind::Call { .. }
                | ExprKind::SystemCall { .. }
                | ExprKind::Inside { .. }
                | ExprKind::MemberAccess { .. }
                | ExprKind::Index { .. }
                | ExprKind::RangeSelect { .. }
                | ExprKind::Range(..)
                | ExprKind::Paren(_)
                | ExprKind::Dollar
                | ExprKind::Null
                | ExprKind::This
        )
    }

    /// Whether `e` reads a solver `foreach` index.
    fn sat_reads_loop(t: &SatTr, e: &Expression) -> bool {
        let mut found = false;
        Self::sat_walk(e, &mut |x| {
            if let ExprKind::Ident(h) = &x.kind
                && h.path.len() == 1
                && t.loop_of(&h.path[0].name.name).is_some()
            {
                found = true;
            }
        });
        found
    }

    fn sat_walk(e: &Expression, f: &mut dyn FnMut(&Expression)) {
        f(e);
        match &e.kind {
            ExprKind::Unary { operand, .. } => Self::sat_walk(operand, f),
            ExprKind::Binary { left, right, .. } => {
                Self::sat_walk(left, f);
                Self::sat_walk(right, f);
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                Self::sat_walk(condition, f);
                Self::sat_walk(then_expr, f);
                Self::sat_walk(else_expr, f);
            }
            ExprKind::Concatenation(es) => es.iter().for_each(|x| Self::sat_walk(x, f)),
            ExprKind::Replication { count, exprs } => {
                Self::sat_walk(count, f);
                exprs.iter().for_each(|x| Self::sat_walk(x, f));
            }
            ExprKind::Call { func, args } => {
                Self::sat_walk(func, f);
                args.iter().for_each(|x| Self::sat_walk(x, f));
            }
            ExprKind::SystemCall { args, .. } => args.iter().for_each(|x| Self::sat_walk(x, f)),
            ExprKind::Inside { expr, ranges } => {
                Self::sat_walk(expr, f);
                ranges.iter().for_each(|x| Self::sat_walk(x, f));
            }
            ExprKind::MemberAccess { expr, .. } => Self::sat_walk(expr, f),
            ExprKind::Index { expr, index } => {
                Self::sat_walk(expr, f);
                Self::sat_walk(index, f);
            }
            ExprKind::RangeSelect {
                expr, left, right, ..
            } => {
                Self::sat_walk(expr, f);
                Self::sat_walk(left, f);
                Self::sat_walk(right, f);
            }
            ExprKind::Range(a, c) => {
                Self::sat_walk(a, f);
                Self::sat_walk(c, f);
            }
            ExprKind::Paren(x) => Self::sat_walk(x, f),
            _ => {}
        }
    }

    /// Whether `array` names an unpacked array (a member of this object or a
    /// variable in scope), not a packed vector.
    fn sat_unpacked_state(&self, array: &Expression) -> bool {
        let Some(name) = Self::foreach_base_name(array) else {
            return false;
        };
        self.this_stack
            .last()
            .copied()
            .flatten()
            .and_then(|h| self.heap.get(h)?.as_ref())
            .and_then(|i| self.module.classes.get(&i.class_name))
            .is_some_and(|cd| {
                cd.array_properties.contains_key(&name) || cd.queue_properties.contains_key(&name)
            })
    }

    /// The current length of a state array a `foreach` walks.
    fn sat_state_len(&mut self, t: &SatTr, array: &Expression) -> Option<usize> {
        let size = Expression::new(
            ExprKind::Call {
                func: Box::new(Expression::new(
                    ExprKind::MemberAccess {
                        expr: Box::new(array.clone()),
                        member: Identifier {
                            name: "size".to_string(),
                            span: Span::dummy(),
                        },
                    },
                    array.span,
                )),
                args: Vec::new(),
            },
            array.span,
        );
        let v = self.sat_eval(t, &size);
        if v.has_xz() {
            return None;
        }
        usize::try_from(v.to_u64()?).ok()
    }

    /// Evaluate a state expression with the unrolled indices bound.
    fn sat_eval(&mut self, t: &SatTr, e: &Expression) -> Value {
        if t.consts.is_empty() {
            return self.eval_expr(e);
        }
        let frame: HashMap<String, Value> = t.consts.iter().cloned().collect();
        self.push_local_frame(frame);
        let v = self.eval_expr(e);
        self.pop_local_frame();
        v
    }

    /// An operand that reads no rand variable: a constant now, or a call
    /// the solver makes per `foreach` index.
    fn sat_state(&mut self, t: &mut SatTr, e: &Expression) -> Lw<rs::Expr> {
        if !Self::sat_reads_loop(t, e) {
            return Some(rs::Expr::Const(bits_of(&self.sat_eval(t, e))?));
        }
        // Its type, with every index at its first value.
        let binds: Vec<String> = t.loops.iter().map(|l| l.0.clone()).collect();
        let probe: HashMap<String, Value> = t
            .consts
            .iter()
            .cloned()
            .chain(t.loops.iter().map(|l| {
                let mut v = Value::from_u64(l.2 as u64, 32);
                v.is_signed = true;
                (l.0.clone(), v)
            }))
            .collect();
        self.push_local_frame(probe);
        let v = self.eval_expr(e);
        self.pop_local_frame();
        if v.is_real || v.width == 0 {
            return None;
        }
        let args = t.loops.iter().map(|l| Self::sat_index(l.1, l.2)).collect();
        // The unrolled indices are folded into the expression's frame.
        let mut expr = e.clone();
        for (n, c) in &t.consts {
            expr = Self::sat_bind_const(&expr, n, c);
        }
        t.funs.push(SatFun::Eval { expr, binds });
        Some(rs::Expr::Call {
            func: rs::FuncId(t.funs.len() as u32 - 1),
            width: v.width,
            signed: v.is_signed,
            args,
        })
    }

    /// A bare identifier expression.
    fn sat_ident(name: &str) -> Expression {
        Expression::new(
            ExprKind::Ident(HierarchicalIdentifier {
                root: None,
                path: vec![HierPathSegment {
                    name: Identifier {
                        name: name.to_string(),
                        span: Span::dummy(),
                    },
                    selects: Vec::new(),
                }],
                span: Span::dummy(),
                cached_signal_id: Cell::new(None),
                cached_resolved_name: std::cell::OnceCell::new(),
            }),
            Span::dummy(),
        )
    }

    /// A `foreach` index's value: the solver's position plus the first index.
    fn sat_index(l: rs::LoopId, lo: i64) -> rs::Expr {
        use rs::build as b;
        if lo == 0 {
            b::lp(l)
        } else {
            b::bin(rs::BinOp::Add, b::lp(l), b::int(lo))
        }
    }

    /// `e` with the identifier `n` replaced by the literal `c`.
    fn sat_bind_const(e: &Expression, n: &str, c: &Value) -> Expression {
        let mut e = e.clone();
        fn walk(e: &mut Expression, n: &str, lit: &Expression) {
            if let ExprKind::Ident(h) = &e.kind
                && h.path.len() == 1
                && h.path[0].name.name == n
            {
                *e = lit.clone();
                return;
            }
            match &mut e.kind {
                ExprKind::Unary { operand, .. } => walk(operand, n, lit),
                ExprKind::Binary { left, right, .. } => {
                    walk(left, n, lit);
                    walk(right, n, lit);
                }
                ExprKind::Conditional {
                    condition,
                    then_expr,
                    else_expr,
                } => {
                    walk(condition, n, lit);
                    walk(then_expr, n, lit);
                    walk(else_expr, n, lit);
                }
                ExprKind::Concatenation(es) => es.iter_mut().for_each(|x| walk(x, n, lit)),
                ExprKind::Call { args, .. } | ExprKind::SystemCall { args, .. } => {
                    args.iter_mut().for_each(|x| walk(x, n, lit))
                }
                ExprKind::Index { expr, index } => {
                    walk(expr, n, lit);
                    walk(index, n, lit);
                }
                ExprKind::MemberAccess { expr, .. } => walk(expr, n, lit),
                ExprKind::Paren(x) => walk(x, n, lit),
                _ => {}
            }
        }
        let lit = Expression::new(
            ExprKind::Number(NumberLiteral::Integer {
                size: Some(32),
                signed: true,
                base: NumberBase::Decimal,
                value: c.to_i64().unwrap_or(0).to_string(),
                cached_val: Default::default(),
            }),
            e.span,
        );
        walk(&mut e, n, &lit);
        e
    }

    /// Lower an operand.
    fn sat_expr(&mut self, t: &mut SatTr, e: &Expression) -> Lw<rs::Expr> {
        use rs::build as b;
        let e = Self::unparen(e);
        if let Some(n) = self.sat_member(t, e) {
            return t.scalars.get(&n).map(|v| b::var(*v));
        }
        if let ExprKind::Ident(h) = &e.kind
            && h.path.len() == 1
            && let Some((l, lo)) = t.loop_of(&h.path[0].name.name)
        {
            return Some(Self::sat_index(l, lo));
        }
        if !self.sat_reads_rand(t, e) {
            return self.sat_state(t, e);
        }
        Some(match &e.kind {
            ExprKind::Unary { op, operand } => {
                let a = self.sat_expr(t, operand)?;
                let op = match op {
                    UnaryOp::Plus => rs::UnOp::Plus,
                    UnaryOp::Minus => rs::UnOp::Neg,
                    UnaryOp::LogNot => rs::UnOp::LogNot,
                    UnaryOp::BitNot => rs::UnOp::BitNot,
                    UnaryOp::BitAnd => rs::UnOp::RedAnd,
                    UnaryOp::BitNand => rs::UnOp::RedNand,
                    UnaryOp::BitOr => rs::UnOp::RedOr,
                    UnaryOp::BitNor => rs::UnOp::RedNor,
                    UnaryOp::BitXor => rs::UnOp::RedXor,
                    UnaryOp::BitXnor => rs::UnOp::RedXnor,
                    _ => return None,
                };
                b::un(op, a)
            }
            ExprKind::Binary { op, left, right } => {
                use rs::BinOp as R;
                let op = match op {
                    BinaryOp::Add => R::Add,
                    BinaryOp::Sub => R::Sub,
                    BinaryOp::Mul => R::Mul,
                    BinaryOp::Div => R::Div,
                    BinaryOp::Mod => R::Mod,
                    BinaryOp::Eq | BinaryOp::CaseEq => R::Eq,
                    BinaryOp::Neq | BinaryOp::CaseNeq => R::Ne,
                    BinaryOp::LogAnd => R::LogAnd,
                    BinaryOp::LogOr => R::LogOr,
                    BinaryOp::LogImplies => R::Implies,
                    BinaryOp::LogEquiv => R::Equiv,
                    BinaryOp::Lt => R::Lt,
                    BinaryOp::Leq => R::Le,
                    BinaryOp::Gt => R::Gt,
                    BinaryOp::Geq => R::Ge,
                    BinaryOp::BitAnd => R::BitAnd,
                    BinaryOp::BitOr => R::BitOr,
                    BinaryOp::BitXor => R::BitXor,
                    BinaryOp::BitXnor => R::BitXnor,
                    BinaryOp::ShiftLeft | BinaryOp::ArithShiftLeft => R::Shl,
                    BinaryOp::ShiftRight => R::Shr,
                    BinaryOp::ArithShiftRight => R::AShr,
                    _ => return None,
                };
                b::bin(op, self.sat_expr(t, left)?, self.sat_expr(t, right)?)
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => b::cond(
                self.sat_expr(t, condition)?,
                self.sat_expr(t, then_expr)?,
                self.sat_expr(t, else_expr)?,
            ),
            ExprKind::Concatenation(es) => {
                let mut v = Vec::with_capacity(es.len());
                for x in es {
                    v.push(self.sat_expr(t, x)?);
                }
                rs::Expr::Concat(v)
            }
            ExprKind::Replication { count, exprs } => {
                if self.sat_reads_rand(t, count) {
                    return None;
                }
                let n = self.sat_eval(t, count).to_u64()? as u32;
                let mut v = Vec::with_capacity(exprs.len());
                for x in exprs {
                    v.push(self.sat_expr(t, x)?);
                }
                rs::Expr::Replicate(n, Box::new(rs::Expr::Concat(v)))
            }
            ExprKind::Inside { expr, ranges } => {
                let x = self.sat_expr(t, expr)?;
                let mut set = Vec::with_capacity(ranges.len());
                for r in ranges {
                    set.push(self.sat_set_value(t, r)?);
                }
                b::inside(x, set)
            }
            ExprKind::Index { expr, index } => {
                let name = self.sat_member(t, expr)?;
                if let Some(a) = t.arrays.get(&name) {
                    let (id, lo) = (a.id, a.lo);
                    let i = self.sat_expr(t, index)?;
                    let i = if lo == 0 {
                        i
                    } else {
                        b::bin(rs::BinOp::Sub, i, b::int(lo))
                    };
                    return Some(b::elem(id, i));
                }
                // A bit-select of a rand scalar.
                let v = *t.scalars.get(&name)?;
                let off = self.sat_packed_lsb(&name)?;
                let i = self.sat_expr(t, index)?;
                let i = if off == 0 {
                    i
                } else {
                    b::bin(rs::BinOp::Sub, i, b::int(off))
                };
                rs::Expr::Bit {
                    base: Box::new(b::var(v)),
                    index: Box::new(i),
                }
            }
            ExprKind::RangeSelect {
                expr,
                kind,
                left,
                right,
            } => {
                let name = self.sat_member(t, expr)?;
                let v = *t.scalars.get(&name)?;
                let off = self.sat_packed_lsb(&name)?;
                if self.sat_reads_rand(t, left)
                    || self.sat_reads_rand(t, right)
                    || Self::sat_reads_loop(t, left)
                {
                    return None;
                }
                let l = self.sat_eval(t, left).to_i64()?;
                let r = self.sat_eval(t, right).to_i64()?;
                let (msb, lsb) = match kind {
                    RangeKind::Constant => (l.max(r), l.min(r)),
                    RangeKind::IndexedUp => (l + r - 1, l),
                    RangeKind::IndexedDown => (l, l - r + 1),
                };
                let (msb, lsb) = (msb - off, lsb - off);
                let w = t.p.var_width(v) as i64;
                if lsb < 0 || msb >= w || msb < lsb {
                    return None;
                }
                rs::Expr::Slice {
                    base: Box::new(b::var(v)),
                    msb: msb as u32,
                    lsb: lsb as u32,
                }
            }
            ExprKind::SystemCall { name, args } => match (name.as_str(), args.as_slice()) {
                ("$__xz_type_cast", [ty, inner]) => {
                    let ExprKind::TypeLiteral(dt) = &ty.kind else {
                        return None;
                    };
                    if is_type_real(dt) {
                        return None;
                    }
                    let w = resolve_type_width(
                        dt,
                        Some(&self.module.parameters),
                        Some(&self.module.typedefs),
                    );
                    b::cast(w, is_type_signed(dt), self.sat_expr(t, inner)?)
                }
                ("$__xz_size_cast", [n, inner]) if !self.sat_reads_rand(t, n) => {
                    let w = self.sat_eval(t, n).to_u64()? as u32;
                    let x = self.sat_expr(t, inner)?;
                    let s = self.sat_signed(t, &x);
                    b::cast(w, s, x)
                }
                ("$__xz_named_cast", [ty, inner]) => {
                    let nm = self.named_cast_key(ty)?;
                    let (w, s) = if let Some(dt) = self.module.typedef_types.get(nm.as_str()) {
                        if is_type_real(dt) {
                            return None;
                        }
                        (self.cast_context_width(dt), Some(is_type_signed(dt)))
                    } else if let Some(&w) = self.module.typedefs.get(nm.as_str()) {
                        (w, Some(false))
                    } else if !self.sat_reads_rand(t, ty) {
                        (self.sat_eval(t, ty).to_u64()? as u32, None)
                    } else {
                        return None;
                    };
                    let x = self.sat_expr(t, inner)?;
                    let s = s.unwrap_or_else(|| self.sat_signed(t, &x));
                    b::cast(w, s, x)
                }
                ("$signed", [inner]) | ("$unsigned", [inner]) => {
                    let x = self.sat_expr(t, inner)?;
                    let w = t.p.expr_width(&x);
                    b::cast(w, name == "$signed", x)
                }
                _ => return None,
            },
            ExprKind::Call { func, args } => {
                // `arr.size()` of a rand array.
                if let ExprKind::MemberAccess { expr, member } = &func.kind
                    && args.is_empty()
                    && member.name == "size"
                {
                    let name = self.sat_member(t, expr)?;
                    let a = t.arrays.get_mut(&name)?;
                    a.sized = true;
                    return Some(b::size(a.id));
                }
                // §18.5.12: a function of rand arguments, evaluated once they
                // are fixed. Each argument is bound to a fresh local.
                if !Self::sat_plain_call(func) {
                    return None;
                }
                let mut lowered = Vec::with_capacity(args.len());
                let mut binds = Vec::with_capacity(args.len());
                let mut call_args = Vec::with_capacity(args.len());
                for (k, a) in args.iter().enumerate() {
                    lowered.push(self.sat_expr(t, a)?);
                    let n = format!("__xz_sat_arg{}_{}", t.funs.len(), k);
                    call_args.push(Self::sat_ident(&n));
                    binds.push(n);
                }
                let call = Expression::new(
                    ExprKind::Call {
                        func: func.clone(),
                        args: call_args,
                    },
                    e.span,
                );
                // The return type, from a call with the arguments at zero.
                let zero: HashMap<String, Value> = binds
                    .iter()
                    .zip(&lowered)
                    .map(|(n, x)| {
                        let mut v = Value::zero(t.p.expr_width(x));
                        v.is_signed = self.sat_signed(t, x);
                        (n.clone(), v)
                    })
                    .collect();
                self.push_local_frame(zero);
                let r = self.eval_expr(&call);
                self.pop_local_frame();
                if r.is_real || r.width == 0 {
                    return None;
                }
                t.funs.push(SatFun::Eval { expr: call, binds });
                rs::Expr::Call {
                    func: rs::FuncId(t.funs.len() as u32 - 1),
                    width: r.width,
                    signed: r.is_signed,
                    args: lowered,
                }
            }
            _ => return None,
        })
    }

    /// A call of a function or of a method of this object (not of another
    /// object, whose state the solver could not see change).
    fn sat_plain_call(func: &Expression) -> bool {
        match &func.kind {
            ExprKind::Ident(h) => h.path.len() == 1,
            ExprKind::MemberAccess { expr, .. } => matches!(expr.kind, ExprKind::This),
            _ => false,
        }
    }

    fn sat_signed(&self, t: &SatTr, x: &rs::Expr) -> bool {
        t.p.expr_signed(x)
    }

    /// The declared LSB of a rand scalar's packed range (`[31:8]` -> 8);
    /// `None` for an ascending or multi-dimensional range.
    fn sat_packed_lsb(&self, name: &str) -> Option<i64> {
        let handle = self.this_stack.last().copied().flatten()?;
        match self.class_prop_packed_dims(handle, name).as_deref() {
            None | Some([]) => Some(0),
            Some([(msb, lsb)]) if msb >= lsb => Some(*lsb),
            _ => None,
        }
    }
}
