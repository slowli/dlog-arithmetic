//! Interpreter for generic finite group arithmetic.

#![deny(missing_docs, missing_debug_implementations)]

pub mod functions;
mod groups;
mod interpreter;
pub mod parser;

pub use crate::{
    groups::{Ed25519, Group},
    interpreter::{EvalError, Scope, Value, ValueType, Var},
};