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
//! let mut context = Context::standard(Ed25519, thread_rng());
//!
//! // Language snippet. Syntax is essentially a mix of Python and Rust.
//! let mut code = r#"
//!     ## Comments start with a hash sign `#`.
//!     x = 12345; # `x` is a *scalar* (member of the `Z/nZ` field).
//!     X = [x]G;  # `X` is a group element obtained by adding the basepoint to itself `x` times.
//!     :assert(X == x * G);
//!     ## `x * G` is another way to write multiplication by a scalar.
//!
//!     ## Element arithmetic uses additive notation:
//!     :assert(X + G == [x + 1]G);
//!     ## Function calls require the function name to be preceded by a colon:
//!     x = :sc_rand(); # `x` is now a random scalar.
//!
//!     ## The language supports tuples and destructuring. For example,
//!     ## here we create a "keypair".
//!     keypair = :sc_rand() * (1, G);
//!     (x, K) = keypair;
//!     :assert(K == [x]G);
//!     ## Tuples of the same type can be added or subtracted, resulting in the tuple
//!     ## of the same type. Tuples can also be multiplied / divided by a scalar.
//!     :assert(keypair / 2 == (x/2, [x/2]G));
//!
//!     ## Like Rust, language supports blocks and associated variable scopes.
//!     Y = {
//!         x = :sc_rand(); # shadows the `x` definition above
//!         [x]G
//!     };
//!
//!     ## It is possible to define user functions:
//!     fn gen() {
//!         :sc_rand() * (1, G)
//!     }
//!     (x, K) = :gen();
//!
//!     ## Functions can take arguments with optional type annotations.
//!     fn ed25519_sign(x, message: bytes) {
//!         (r, R) = :gen();
//!         c = :sc_sha512(R, [x]G, message);
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
