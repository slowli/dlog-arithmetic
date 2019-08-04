//! Functions.

use curve25519::scalar::Scalar;
use failure::Error;
use rand_core::{CryptoRng, RngCore};
use sha2::{Digest, Sha512};
use std::fmt;

use crate::{groups::Ed25519, Group, Value, ValueType};

/// Function type.
#[derive(Debug, Clone, PartialEq)]
pub struct FnType {
    /// Type of function arguments.
    pub args: FnArgs,
    /// Type of the value returned by the function.
    pub return_type: ValueType,
}

impl fmt::Display for FnType {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "fn({})", self.args)?;
        if self.return_type != ValueType::Void {
            write!(formatter, " -> {}", self.return_type)?;
        }
        Ok(())
    }
}

/// Type of function arguments.
#[derive(Debug, Clone, PartialEq)]
pub enum FnArgs {
    /// Any arguments are accepted.
    Any,
    /// Lists accepted arguments.
    List(Vec<ValueType>),
}

impl fmt::Display for FnArgs {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FnArgs::Any => formatter.write_str("..."),
            FnArgs::List(args) => {
                for (i, arg) in args.iter().enumerate() {
                    fmt::Display::fmt(arg, formatter)?;
                    if i + 1 < args.len() {
                        formatter.write_str(", ")?;
                    }
                }
                Ok(())
            }
        }
    }
}

/// Function on zero or more `Value`s.
pub trait Function<G: Group> {
    /// Returns the type signature of this function.
    fn ty(&self) -> FnType;
    /// Executes the function on the specified arguments.
    fn execute(&mut self, args: &[Value<G>]) -> Result<Value<G>, Error>;
}

/// Function converting any serializable arguments into a scalar.
#[derive(Debug, Clone, Copy)]
pub struct FromSha512;

impl Function<Ed25519> for FromSha512 {
    fn ty(&self) -> FnType {
        FnType {
            args: FnArgs::Any,
            return_type: ValueType::Scalar,
        }
    }

    fn execute(&mut self, args: &[Value<Ed25519>]) -> Result<Value<Ed25519>, Error> {
        fn input_var(hash: &mut Sha512, var: &Value<Ed25519>) {
            match var {
                Value::Buffer(buffer) => hash.input(buffer),
                Value::Scalar(scalar) => hash.input(scalar.as_bytes()),
                Value::Element(elem) => hash.input(elem.compress().as_bytes()),
                Value::Tuple(fragments) => {
                    for fragment in fragments {
                        input_var(hash, fragment);
                    }
                }
                Value::Void => unreachable!(),
            }
        }

        let mut hash = Sha512::default();
        for arg in args {
            input_var(&mut hash, arg);
        }
        Ok(Value::Scalar(Scalar::from_hash(hash)))
    }
}

/// Function creating a random scalar.
#[derive(Debug, Clone, Copy)]
pub struct Rand<R>(pub R);

impl<R: CryptoRng + RngCore> Function<Ed25519> for Rand<R> {
    fn ty(&self) -> FnType {
        FnType {
            args: FnArgs::List(vec![]),
            return_type: ValueType::Scalar,
        }
    }

    fn execute(&mut self, args: &[Value<Ed25519>]) -> Result<Value<Ed25519>, Error> {
        debug_assert!(args.is_empty());
        Ok(Value::Scalar(Scalar::random(&mut self.0)))
    }
}
