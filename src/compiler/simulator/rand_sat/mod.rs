//! `svrand` — SystemVerilog constrained randomization of any width, by
//! bit-blasting onto a SAT solver (batsat). A proof of concept for xezim.
//!
//! The caller lowers one `randomize()` into a [`Problem`] and calls
//! [`Problem::solve`]; see [`ir`] for what the caller is responsible for.

mod bb;
#[cfg(test)]
mod difftest;
mod domain;
mod eval;
pub mod ir;
mod lower;
mod solve;
mod types;
pub mod value;

pub use ir::{
    ArrayId, ArraySize, BinOp, DistItem, Expr, FuncId, Item, LoopId, Problem, SetItem, UnOp, VarId,
    VarRef, Weight, build,
};
pub use solve::SolveError;
pub use value::Bits;

/// When a solve gives up: past `deadline`, or once `interrupted` says so
/// (a SIGTERM to the simulator).
#[derive(Clone, Copy)]
pub struct Limits {
    pub deadline: Option<std::time::Instant>,
    pub interrupted: fn() -> bool,
}

impl Limits {
    pub fn hit(&self) -> bool {
        (self.interrupted)()
            || self
                .deadline
                .is_some_and(|d| std::time::Instant::now() >= d)
    }
}

/// Evaluates a function called from a constraint, once its rand arguments
/// are fixed (§18.5.12).
pub trait FuncEval {
    fn call(&mut self, func: FuncId, args: &[Bits]) -> Bits;
}

/// For problems without function calls.
#[cfg(test)]
pub struct NoFuncs;

#[cfg(test)]
impl FuncEval for NoFuncs {
    fn call(&mut self, func: FuncId, _: &[Bits]) -> Bits {
        panic!("no function {func:?}")
    }
}
