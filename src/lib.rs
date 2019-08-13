//! Scripting language and its interpreter for arithmetic in groups
//! with hard discrete log problem.
//!
//! # Examples
//!
//! ```
//! use dlog_arithmetic::{
//!     functions as fns, parser::{Span, Statement}, Context, Ed25519, Group,
//!     Value, ValueType,
//! };
//! use rand::thread_rng;
//!
//! let mut context = Context::new(Ed25519);
//! context
//!     .innermost_scope()
//!     // Add a selected group generator (basepoint) as a variable `G`.
//!     .insert_var("G", Value::Element(Ed25519.base_element()))
//!     // Add a function returning a random scalar, as `rand()`.
//!     .insert_native_fn("rand", fns::Rand::new(thread_rng()))
//!     .insert_native_fn("sha512", fns::FromSha512);
//!
//! // Language snippet. Syntax is essentially a mix of Python and Rust.
//! let mut code = r#"
//!     ## Comments start with a hash sign `#`.
//!     x = 12345; # `x` is a *scalar* (member of the `Z/nZ` group).
//!     X = [x]G;  # `X` is a group element obtained by adding the basepoint to itself `x` times.
//!     X ?= x * G; # `x * G` is another way to write multiplication by a scalar;
//!                 ##`?=` is equality assertion.
//!     ## Element arithmetic uses additive notation:
//!     X + G ?= [x + 1]G;
//!     ## Function calls require the function name to be preceded by a colon:
//!     x = :rand(); # `x` is now a random scalar.
//!
//!     ## The language supports tuples and destructuring. For example,
//!     ## here we create a "keypair".
//!     keypair = :rand() * (1, G);
//!     (x, K) = keypair; K ?= [x]G;
//!     ## Tuples of the same type can be added or subtracted, resulting in the tuple
//!     ## of the same type. Tuples can also be multiplied / divided by a scalar.
//!     keypair / 2 ?= (x/2, [x/2]G);
//!
//!     ## Like Rust, language supports blocks and associated variable scopes.
//!     Y = {
//!         x = :rand(); # shadows the `x` definition above
//!         [x]G
//!     };
//!
//!     ## It is possible to define user functions:
//!     fn gen() {
//!         :rand() * (1, G)
//!     }
//!     (x, K) = :gen();
//!
//!     ## Functions can take arguments with optional type annotations.
//!     fn ed25519_sign(x, message: bytes) {
//!         (r, R) = :gen();
//!         c = :sha512(R, [x]G, message);
//!         (R, r + c * x)
//!     }
//!     :ed25519_sign(x, "Hello, world!")
//! "#.to_owned();
//! // Snippets should be ended with EOF in order to be recognized as complete.
//! code.push('\0');
//!
//! let statements = Statement::parse_list(Span::new(&code)).unwrap();
//! let output = context.evaluate(&statements).unwrap();
//! // `output` is equal to the last evaluated statement, i.e., a digital signature
//! assert_eq!(output.ty(), ValueType::Tuple(vec![ValueType::Element, ValueType::Scalar]));
//! ```

#![deny(missing_docs, missing_debug_implementations)]

pub mod functions;
mod groups;
mod interpreter;
pub mod parser;
mod type_inference;

pub use crate::{
    groups::{Ed25519, Group},
    interpreter::{
        Backtrace, BacktraceElement, Code, Context, ErrorWithBacktrace, EvalError, Scope, Value,
        ValueType,
    },
    type_inference::{TypeContext, TypeError},
};
