use failure_derive::*;
use std::{collections::HashMap, fmt, ops};

use crate::{
    functions::{FnArgs, FnType, Function},
    groups::Group,
    parser::{
        map_span, map_span_ref, BinaryOp, Expr, LiteralType, Lvalue, Spanned, SpannedExpr,
        SpannedLvalue, SpannedStatement,
    },
};

/// Value used in finite group arithmetic.
pub enum Value<G: Group> {
    /// Absence of value, `()` in Rust terms.
    Void,
    /// Scalar value.
    Scalar(G::Scalar),
    /// Group element.
    Element(G::Element),
    /// Arbitrary-sized byte buffer.
    Buffer(Vec<u8>),
    /// Tuple of values.
    Tuple(Vec<Value<G>>),
}

impl<G: Group> Clone for Value<G> {
    fn clone(&self) -> Self {
        match self {
            Value::Void => Value::Void,
            Value::Scalar(sc) => Value::Scalar(*sc),
            Value::Element(ge) => Value::Element(*ge),
            Value::Buffer(ref buffer) => Value::Buffer(buffer.clone()),
            Value::Tuple(ref fragments) => Value::Tuple(fragments.clone()),
        }
    }
}

impl<G: Group> PartialEq for Value<G> {
    fn eq(&self, rhs: &Self) -> bool {
        use self::Value::*;
        match (self, rhs) {
            (Void, Void) => true,
            (Scalar(x), Scalar(y)) => x == y,
            (Element(x), Element(y)) => x == y,
            (Buffer(x), Buffer(y)) => x == y,
            (Tuple(xs), Tuple(ys)) => xs == ys,
            _ => false,
        }
    }
}

impl<G: Group> fmt::Debug for Value<G>
where
    G::Scalar: fmt::Debug,
    G::Element: fmt::Debug,
{
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Void => formatter.debug_tuple("Void").finish(),
            Value::Scalar(value) => formatter.debug_tuple("Scalar").field(value).finish(),
            Value::Element(value) => formatter.debug_tuple("Element").field(value).finish(),
            Value::Buffer(buffer) => formatter.debug_tuple("Buffer").field(buffer).finish(),
            Value::Tuple(fragments) => {
                let mut tuple = formatter.debug_tuple("Tuple");
                for fragment in fragments {
                    tuple.field(fragment);
                }
                tuple.finish()
            }
        }
    }
}

impl<G: Group> Value<G> {
    /// Returns the type of the value.
    pub fn ty(&self) -> ValueType {
        match self {
            Value::Void => ValueType::Void,
            Value::Scalar(_) => ValueType::Scalar,
            Value::Element(_) => ValueType::Element,
            Value::Buffer(_) => ValueType::Buffer,
            Value::Tuple(fragments) => ValueType::Tuple(fragments.iter().map(Value::ty).collect()),
        }
    }

    /// Converts this value into a scalar, if possible.
    pub fn as_scalar(&self) -> Option<G::Scalar> {
        match self {
            Value::Scalar(sc) => Some(*sc),
            _ => None,
        }
    }

    /// Converts this value into a group element, if possible.
    pub fn as_element(&self) -> Option<G::Element> {
        match self {
            Value::Element(ge) => Some(*ge),
            _ => None,
        }
    }
}

impl<G: Group> ops::Add for Value<G> {
    type Output = Result<Self, EvalError>;

    fn add(self, rhs: Self) -> Self::Output {
        use self::Value::*;

        match (self, rhs) {
            (Scalar(x), Scalar(y)) => Ok(Value::Scalar(x + y)),
            (Element(x), Element(y)) => Ok(Value::Element(x + y)),

            (Buffer(mut x), Buffer(y)) => Ok(Value::Buffer({
                x.extend_from_slice(&y);
                x
            })),

            (Tuple(ref xs), Tuple(ref ys)) if xs.len() == ys.len() => xs
                .iter()
                .zip(ys)
                .map(|(x, y)| x.clone() + y.clone())
                .collect::<Result<Vec<_>, _>>()
                .map(Value::Tuple),

            (lhs, rhs) => Err(EvalError::InvalidBinaryOp {
                op: "+",
                lhs_ty: lhs.ty(),
                rhs_ty: rhs.ty(),
            }),
        }
    }
}

impl<G: Group> ops::Sub for Value<G> {
    type Output = Result<Self, EvalError>;

    fn sub(self, rhs: Self) -> Self::Output {
        use self::Value::*;

        match (self, rhs) {
            (Scalar(x), Scalar(y)) => Ok(Value::Scalar(x - y)),
            (Element(x), Element(y)) => Ok(Value::Element(x - y)),

            (Tuple(ref xs), Tuple(ref ys)) if xs.len() == ys.len() => xs
                .iter()
                .zip(ys)
                .map(|(x, y)| x.clone() - y.clone())
                .collect::<Result<Vec<_>, _>>()
                .map(Value::Tuple),

            (lhs, rhs) => Err(EvalError::InvalidBinaryOp {
                op: "-",
                lhs_ty: lhs.ty(),
                rhs_ty: rhs.ty(),
            }),
        }
    }
}

impl<G: Group> ops::Mul for Value<G> {
    type Output = Result<Self, EvalError>;

    fn mul(self, rhs: Self) -> Self::Output {
        use self::Value::*;

        match (self, rhs) {
            (Scalar(x), Scalar(y)) => Ok(Value::Scalar(x * y)),
            (Scalar(x), Element(y)) => Ok(Value::Element(y * &x)),
            (Scalar(x), Tuple(ref ys)) => ys
                .iter()
                .map(|y| Scalar(x) * y.clone())
                .collect::<Result<Vec<_>, _>>()
                .map(Value::Tuple),

            (lhs, rhs) => Err(EvalError::InvalidBinaryOp {
                op: "*",
                lhs_ty: lhs.ty(),
                rhs_ty: rhs.ty(),
            }),
        }
    }
}

/// Variable description.
#[derive(Clone)]
pub struct Var<G: Group> {
    /// Current value.
    pub value: Value<G>,
    /// Flag signalizing if this variable is a constant.
    pub constant: bool,
}

impl<G: Group> fmt::Debug for Var<G>
where
    G::Scalar: fmt::Debug,
    G::Element: fmt::Debug,
{
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter
            .debug_struct("Var")
            .field("value", &self.value)
            .field("constant", &self.constant)
            .finish()
    }
}

impl<G: Group> Var<G> {
    /// Creates a new variable.
    pub fn new(value: Value<G>) -> Self {
        Self {
            value,
            constant: false,
        }
    }

    /// Creates a new constant.
    pub fn constant(value: Value<G>) -> Self {
        Self {
            value,
            constant: true,
        }
    }
}

/// Variable scope containing functions and variables.
pub struct Scope<G: Group> {
    group: G,
    variables: HashMap<String, Var<G>>,
    functions: HashMap<String, (FnType, Box<dyn Function<G>>)>,
}

impl<G: Group> fmt::Debug for Scope<G>
where
    G::Scalar: fmt::Debug,
    G::Element: fmt::Debug,
{
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter
            .debug_map()
            .entries(&self.variables)
            .entries(self.functions.iter().map(|(name, (ty, _))| {
                (format!(":{}", name), ty)
            }))
            .finish()
    }
}

impl<G: Group> Scope<G> {
    /// Creates a new scope with no associated variables and functions.
    pub fn new(group: G) -> Self {
        Scope {
            group,
            variables: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    /// Gets the variable with the specified name.
    pub fn get_var(&self, name: &str) -> Option<&Value<G>> {
        self.variables.get(name).map(|var| &var.value)
    }

    /// Returns an interator over all variables in this scope.
    pub fn variables<'s>(&'s self) -> impl Iterator<Item = (&str, &Var<G>)> + 's {
        self.variables
            .iter()
            .map(|(name, value)| (name.as_str(), value))
    }

    /// Defines a variable with the specified name and value.
    pub fn insert_var(&mut self, name: &str, value: Value<G>) -> &mut Self {
        self.variables.insert(name.to_owned(), Var::new(value));
        self
    }

    /// Defines a constant with the specified name and value.
    // TODO: probably can be removed if embedded scopes are implemented
    pub fn insert_constant(&mut self, name: &str, value: Value<G>) -> &mut Self {
        self.variables.insert(name.to_owned(), Var::constant(value));
        self
    }

    /// Removes all variables from the scope. Constants and functions are not removed.
    pub fn clear(&mut self) {
        self.variables.retain(|_, var| var.constant);
    }

    /// Defines a function with the specified name.
    pub fn insert_fn<F>(&mut self, name: &str, fun: F) -> &mut Self
    where
        F: Function<G> + 'static,
    {
        let fn_type = fun.ty();
        self.functions
            .insert(name.to_owned(), (fn_type, Box::new(fun)));
        self
    }
}

/// Possible value type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueType {
    /// Any type.
    Any,
    /// Void (`()` in Rust).
    Void,
    /// Group scalar.
    Scalar,
    /// Group element.
    Element,
    /// Byte buffer.
    Buffer,
    /// Tuple.
    Tuple(Vec<ValueType>),
}

impl fmt::Display for ValueType {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ValueType::Void => formatter.write_str("void"),
            ValueType::Any => formatter.write_str("_"),
            ValueType::Scalar => formatter.write_str("Sc"),
            ValueType::Element => formatter.write_str("Ge"),
            ValueType::Buffer => formatter.write_str("bytes"),
            ValueType::Tuple(fragments) => {
                formatter.write_str("(")?;
                for (i, frag) in fragments.iter().enumerate() {
                    fmt::Display::fmt(frag, formatter)?;
                    if i + 1 < fragments.len() {
                        formatter.write_str(", ")?;
                    }
                }
                formatter.write_str(")")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Typed<T> {
    pub inner: T,
    pub ty: ValueType,
}

impl<T> Typed<T> {
    pub(crate) fn any(value: T) -> Self {
        Self {
            inner: value,
            ty: ValueType::Any,
        }
    }

    pub(crate) fn scalar(value: T) -> Self {
        Self {
            inner: value,
            ty: ValueType::Scalar,
        }
    }

    pub fn tuple(len: usize, value: T) -> Self {
        Self {
            inner: value,
            ty: ValueType::Tuple(vec![ValueType::Any; len]),
        }
    }
}

impl<'a> Typed<Expr<'a>> {
    pub(crate) fn from_literal(lit: Expr<'a>) -> Self {
        Self {
            ty: match lit {
                Expr::Literal { ty, .. } => match ty {
                    LiteralType::Buffer => ValueType::Buffer,
                    LiteralType::Scalar => ValueType::Scalar,
                    LiteralType::Element => ValueType::Element,
                },
                _ => unreachable!(),
            },
            inner: lit,
        }
    }
}

/// Error that can occur during expression evaluation.
#[derive(Debug, Fail)]
pub enum EvalError {
    /// Undefined variable.
    #[fail(display = "Undefined variable")]
    Undefined,

    /// Undefined function.
    #[fail(display = "Undefined function")]
    UndefinedFunction,

    /// Error converting a number to a scalar.
    #[fail(display = "Error converting number to scalar: {}", _0)]
    IntToScalar(#[fail(cause)] failure::Error),

    /// Error converting bytes to a scalar.
    #[fail(display = "Error converting buffer to scalar: {}", _0)]
    BufferToScalar(#[fail(cause)] failure::Error),

    /// Error converting bytes to a group element.
    #[fail(display = "Error converting buffer to element: {}", _0)]
    BufferToElement(#[fail(cause)] failure::Error),

    /// Division by zero.
    #[fail(display = "Division by zero")]
    DivisionByZero,

    /// Unexpected argument types for a function.
    #[fail(display = "Function does not support arguments with these types")]
    ArgTypeMismatch {
        /// Expected argument types.
        expected: FnArgs,
    },

    /// Mismatch between type annotation and actual value type.
    #[fail(display = "Annotated type mismatch")]
    AnnotatedTypeMismatch {
        /// Actual value type.
        actual: ValueType,
    },

    /// Invalid value types for a binary operation.
    #[fail(display = "Invalid arguments for a binary operation")]
    InvalidBinaryOp {
        /// Operator.
        op: &'static str,
        /// Type of the LHS of the operation.
        lhs_ty: ValueType,
        /// Type of the RHS of the operation.
        rhs_ty: ValueType,
    },

    /// Runtime error during function evaluation.
    #[fail(display = "Error evaluating function")]
    FunctionCall(#[fail(cause)] failure::Error),

    /// Assertion failure.
    #[fail(display = "Assertion failed")]
    AssertionFail,

    /// RHS of an assignment cannot be destructured into a tuple.
    #[fail(display = "Cannot destructure variable")]
    CannotDestructure(ValueType),

    /// RHS and LHS of an assignment are tuples of different sizes.
    #[fail(
        display = "A tuple with {} elements cannot be destructured into {} elements",
        actual, expected
    )]
    TupleLenMismatch {
        /// Tuple size of the LHS.
        expected: usize,
        /// Tuple size of the RHS.
        actual: usize,
    },

    /// LHS of the assignment is a constant.
    #[fail(display = "Cannot assign to a constant")]
    CannotAssignToConstant,
}

impl<G: Group> Scope<G> {
    /// Evaluates expression.
    pub fn evaluate_expr<'a>(
        &mut self,
        expr: &SpannedExpr<'a>,
    ) -> Result<Value<G>, Spanned<'a, EvalError>> {
        use crate::parser::Expr::*;

        match expr.extra.inner {
            Variable => self
                .get_var(expr.fragment)
                .cloned()
                .ok_or_else(|| map_span_ref(expr, EvalError::Undefined)),

            Number => {
                let value = expr
                    .fragment
                    .parse::<u64>()
                    .map_err(|e| map_span_ref(expr, EvalError::IntToScalar(e.into())))?;
                self.group
                    .scalar_from_u64(value)
                    .map(Value::Scalar)
                    .map_err(|e| map_span_ref(expr, EvalError::IntToScalar(e.into())))
            }

            Literal { ty, ref value } => match ty {
                LiteralType::Buffer => Ok(Value::Buffer(value.clone())),
                LiteralType::Scalar => self
                    .group
                    .scalar_from_bytes(value)
                    .map(Value::Scalar)
                    .map_err(|e| map_span_ref(expr, EvalError::BufferToScalar(e.into()))),
                LiteralType::Element => self
                    .group
                    .element_from_bytes(value)
                    .map(Value::Element)
                    .map_err(|e| map_span_ref(expr, EvalError::BufferToElement(e.into()))),
            },

            Tuple(ref fragments) => {
                let fragments: Result<Vec<_>, _> = fragments
                    .iter()
                    .map(|frag| self.evaluate_expr(frag))
                    .collect();
                fragments.map(Value::Tuple)
            }

            Function { name, ref args } => {
                let resolved_name = &name.fragment[1..];

                self.functions
                    .get(resolved_name)
                    .ok_or_else(|| map_span(name, EvalError::UndefinedFunction))?;
                let args: Result<Vec<_>, _> =
                    args.iter().map(|arg| self.evaluate_expr(arg)).collect();
                let args = args?;

                let (ty, func) = self.functions.get_mut(resolved_name).unwrap();
                if let FnArgs::List(ref expected_types) = ty.args {
                    let arg_types: Vec<_> = args.iter().map(Value::ty).collect();
                    if &arg_types != expected_types {
                        return Err(map_span_ref(
                            expr,
                            EvalError::ArgTypeMismatch {
                                expected: ty.args.clone(),
                            },
                        ));
                    }
                }
                func.execute(&args)
                    .map_err(|e| map_span_ref(expr, EvalError::FunctionCall(e)))
            }

            // Arithmetic operations
            Binary {
                lhs: ref x,
                rhs: ref y,
                op,
            } => {
                let lhs = self.evaluate_expr(x)?;
                let rhs = self.evaluate_expr(y)?;
                match op.extra {
                    BinaryOp::Add => lhs + rhs,
                    BinaryOp::Sub => lhs - rhs,
                    BinaryOp::Mul => lhs * rhs,

                    BinaryOp::Div => match (lhs, rhs) {
                        (x, Value::Scalar(y)) => self
                            .group
                            .invert_scalar(y)
                            .ok_or(EvalError::DivisionByZero)
                            .and_then(|y_inv| Value::Scalar(y_inv) * x),
                        (lhs, rhs) => Err(EvalError::InvalidBinaryOp {
                            op: "/",
                            lhs_ty: lhs.ty(),
                            rhs_ty: rhs.ty(),
                        }),
                    },

                    BinaryOp::Power => match (lhs, rhs) {
                        (Value::Scalar(x), Value::Element(y)) => Ok(Value::Element(y * &x)),
                        (lhs, rhs) => Err(EvalError::InvalidBinaryOp {
                            op: "[]",
                            lhs_ty: lhs.ty(),
                            rhs_ty: rhs.ty(),
                        }),
                    },
                }
                .map_err(|e| map_span_ref(expr, e))
            }
        }
    }

    fn assign<'a>(
        &mut self,
        lvalue: &SpannedLvalue<'a>,
        rvalue: Value<G>,
    ) -> Result<(), Spanned<'a, EvalError>> {
        match lvalue.extra {
            Lvalue::Variable { ref ty } => {
                if let Some(ref ty) = ty {
                    let actual = rvalue.ty();
                    if ty.extra != actual {
                        return Err(map_span_ref(
                            ty,
                            EvalError::AnnotatedTypeMismatch { actual },
                        ));
                    }
                }
                let var_name = lvalue.fragment;
                if let Some(var) = self.variables.get(var_name) {
                    if var.constant {
                        return Err(map_span_ref(lvalue, EvalError::CannotAssignToConstant));
                    }
                }
                if var_name != "_" {
                    self.variables.insert(var_name.to_owned(), Var::new(rvalue));
                }
            }

            Lvalue::Tuple(ref assignments) => {
                if let Value::Tuple(fragments) = rvalue {
                    if assignments.len() != fragments.len() {
                        return Err(map_span_ref(
                            lvalue,
                            EvalError::TupleLenMismatch {
                                expected: assignments.len(),
                                actual: fragments.len(),
                            },
                        ));
                    }

                    for (assignment, fragment) in assignments.iter().zip(fragments) {
                        self.assign(assignment, fragment)?;
                    }
                } else {
                    return Err(map_span_ref(
                        lvalue,
                        EvalError::CannotDestructure(rvalue.ty()),
                    ));
                }
            }
        }
        Ok(())
    }

    /// Evaluates a list of statements.
    pub fn evaluate<'a>(
        &mut self,
        statements: &[SpannedStatement<'a>],
    ) -> Result<Value<G>, Spanned<'a, EvalError>> {
        use crate::parser::Statement::*;

        let mut return_value = Value::Void;
        for statement in statements {
            return_value = Value::Void;
            match &statement.extra {
                Empty => {}

                Expr(expr) => {
                    return_value = self.evaluate_expr(expr)?;
                }
                Assignment { ref lhs, ref rhs } => {
                    let evaluated = self.evaluate_expr(rhs)?;
                    self.assign(lhs, evaluated)?;
                }

                Comparison {
                    ref lhs,
                    ref rhs,
                    eq_sign,
                } => {
                    let lhs_eval = self.evaluate_expr(lhs)?;
                    let rhs_eval = self.evaluate_expr(rhs)?;
                    if lhs_eval != rhs_eval {
                        return Err(map_span(*eq_sign, EvalError::AssertionFail));
                    }
                }
            }
        }
        Ok(return_value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        functions::{FromSha512, Rand},
        groups::{Ed25519, Ed25519Error},
        parser::Expr,
    };

    use assert_matches::assert_matches;
    use curve25519::{constants::ED25519_BASEPOINT_POINT, scalar::Scalar, traits::IsIdentity};
    use rand::thread_rng;
    use sha2::{Digest, Sha512};
    use std::{collections::HashSet, convert::TryInto};

    #[test]
    fn function_type_display() {
        let ty = FnType {
            args: FnArgs::Any,
            return_type: ValueType::Scalar,
        };
        assert_eq!(ty.to_string(), "fn(...) -> Sc");

        let ty = FnType {
            args: FnArgs::List(vec![
                ValueType::Element,
                ValueType::Tuple(vec![ValueType::Scalar, ValueType::Scalar]),
            ]),
            return_type: ValueType::Element,
        };
        assert_eq!(ty.to_string(), "fn(Ge, (Sc, Sc)) -> Ge");

        let ty = FnType {
            args: FnArgs::List(vec![
                ValueType::Element,
                ValueType::Tuple(vec![ValueType::Scalar, ValueType::Scalar]),
            ]),
            return_type: ValueType::Void,
        };
        assert_eq!(ty.to_string(), "fn(Ge, (Sc, Sc))");
    }

    #[test]
    fn evaluating_scalar() {
        let mut state = Scope::new(Ed25519);
        state
            .insert_fn("sc_sha512", FromSha512)
            .insert_var("x", Value::Scalar(Scalar::from(5_u64)))
            .insert_var("G", Value::Element(ED25519_BASEPOINT_POINT));

        let scalar_expr = "(x + 1) * 10 + 9";
        let scalar_expr = Expr::from_str(scalar_expr).unwrap();
        let output = state.evaluate_expr(&scalar_expr).unwrap();
        assert_eq!(output, Value::Scalar(Scalar::from(69_u64)));

        let scalar_expr = "4/5";
        let scalar_expr = Expr::from_str(scalar_expr).unwrap();
        let output = state.evaluate_expr(&scalar_expr).unwrap();
        let expected = Scalar::from(4_u64) * Scalar::from(5_u64).invert();
        assert_eq!(output, Value::Scalar(expected));

        let scalar_expr = "1 + 4 / (x + 1 - 6)";
        let scalar_expr = Expr::from_str(scalar_expr).unwrap();
        let error = state.evaluate_expr(&scalar_expr).unwrap_err();
        assert_matches!(error.extra, EvalError::DivisionByZero);

        let scalar_expr =
            "16 + 0xsdeaffeeddeaffeeddeaffeeddeaffeeddeaffeeddeaffeedfedcba0504030201";
        let scalar_expr = Expr::from_str(scalar_expr).unwrap();
        let output = state.evaluate_expr(&scalar_expr).unwrap();
        let bytes = hex::decode("eeaffeeddeaffeeddeaffeeddeaffeeddeaffeeddeaffeedfedcba0504030201")
            .unwrap();
        let bytes = bytes[..].try_into().unwrap();
        let expected = Scalar::from_canonical_bytes(bytes).unwrap();
        assert_eq!(output, Value::Scalar(expected));

        let scalar_expr = "0xs0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
        let scalar_expr = Expr::from_str(scalar_expr).unwrap();
        let error = state.evaluate_expr(&scalar_expr).unwrap_err();
        assert_matches!(
            error.extra,
            EvalError::BufferToScalar(ref e)
                if e.downcast_ref::<Ed25519Error>() == Some(&Ed25519Error::NonCanonicalScalar)
        );

        let scalar_expr = ":sc_sha512(0x01000000, 1001 * G)";
        let scalar_expr = Expr::from_str(scalar_expr).unwrap();
        let mut hasher = Sha512::default();
        hasher.input(&[1_u8, 0, 0, 0]);
        hasher.input(
            (ED25519_BASEPOINT_POINT * Scalar::from(1001_u64))
                .compress()
                .as_bytes(),
        );
        let expected = Scalar::from_hash(hasher);
        assert_eq!(
            state.evaluate_expr(&scalar_expr).unwrap(),
            Value::Scalar(expected)
        );

        state.insert_fn("sc_rand", Rand(thread_rng()));
        let scalar_expr = ":sc_rand()";
        let scalar_expr = Expr::from_str(scalar_expr).unwrap();
        let random_scalars: HashSet<_> = (0..5)
            .map(|_| {
                if let Value::Scalar(sc) = state.evaluate_expr(&scalar_expr).unwrap() {
                    sc.to_bytes()
                } else {
                    unreachable!("Unexpected return type");
                }
            })
            .collect();
        assert_eq!(random_scalars.len(), 5);
    }

    #[test]
    fn evaluating_element() {
        let mut state = Scope::new(Ed25519);
        state
            .insert_var("x", Value::Scalar(Scalar::from(5_u64)))
            .insert_constant("G", Value::Element(ED25519_BASEPOINT_POINT));
        let element_expr = "x*G";
        let element_expr = Expr::from_str(element_expr).unwrap();
        let output = state.evaluate_expr(&element_expr).unwrap();
        let expected = ED25519_BASEPOINT_POINT * Scalar::from(5_u64);
        assert_eq!(output, Value::Element(expected));

        let element_expr = "((x + 1) / 2) * G";
        let element_expr = Expr::from_str(element_expr).unwrap();
        let output = state.evaluate_expr(&element_expr).unwrap();
        let expected = ED25519_BASEPOINT_POINT * Scalar::from(3_u64);
        assert_eq!(output, Value::Element(expected));

        let element_expr = "(x/3) * G + [1/3]G";
        let element_expr = Expr::from_str(element_expr).unwrap();
        let output = state.evaluate_expr(&element_expr).unwrap();
        let expected = ED25519_BASEPOINT_POINT * Scalar::from(2_u64);
        assert_eq!(output, Value::Element(expected));

        let random_scalar = Scalar::random(&mut thread_rng());
        let random_point = ED25519_BASEPOINT_POINT * random_scalar;
        let element_expr = format!(
            "0xg{} - [0xs{}]G",
            hex::encode(random_point.compress().as_bytes()),
            hex::encode(random_scalar.as_bytes())
        );
        let element_expr = Expr::from_str(&element_expr).unwrap();
        let output = state.evaluate_expr(&element_expr).unwrap();
        if let Value::Element(output) = output {
            assert!(output.is_identity());
        } else {
            unreachable!("Invalid expression type");
        }
    }
}
