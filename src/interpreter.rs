use failure_derive::*;
use std::{collections::HashMap, fmt, ops, rc::Rc};
use typed_arena::Arena;

use crate::{
    functions::{FnArgs, FnType, Function, InterpretedFn},
    groups::Group,
    parser::{
        map_span, map_span_ref, BinaryOp, Error as ParseError, Expr, LiteralType, Lvalue, Spanned,
        SpannedExpr, SpannedLvalue, SpannedStatement, Statement,
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

/// Variable scope containing functions and variables.
#[derive(Clone)]
pub struct Scope<'a, G: Group> {
    variables: HashMap<String, Value<G>>,
    functions: HashMap<String, (FnType, Rc<dyn Function<G> + 'a>)>,
}

impl<G: Group> Default for Scope<'_, G> {
    fn default() -> Self {
        Self {
            variables: HashMap::new(),
            functions: HashMap::new(),
        }
    }
}

impl<G: Group> fmt::Debug for Scope<'_, G>
where
    G::Scalar: fmt::Debug,
    G::Element: fmt::Debug,
{
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter
            .debug_map()
            .entries(&self.variables)
            .entries(
                self.functions
                    .iter()
                    .map(|(name, (ty, _))| (format!(":{}", name), ty)),
            )
            .finish()
    }
}

impl<'a, G: Group> Scope<'a, G> {
    /// Creates a new scope with no associated variables and functions.
    pub fn new() -> Self {
        Self::default()
    }

    /// Checks if the scope contains a variable with the specified name.
    pub fn contains_var(&self, name: &str) -> bool {
        self.variables.contains_key(name)
    }

    /// Gets the variable with the specified name.
    pub fn get_var(&self, name: &str) -> Option<&Value<G>> {
        self.variables.get(name)
    }

    /// Returns an iterator over all variables in this scope.
    pub fn variables<'s>(&'s self) -> impl Iterator<Item = (&str, &Value<G>)> + 's {
        self.variables
            .iter()
            .map(|(name, value)| (name.as_str(), value))
    }

    /// Returns an iterator over functions defined in this scope.
    pub fn functions<'s>(&'s self) -> impl Iterator<Item = (&str, &FnType)> + 's {
        self.functions
            .iter()
            .map(|(name, (ty, _))| (name.as_str(), ty))
    }

    /// Defines a variable with the specified name and value.
    pub fn insert_var(&mut self, name: &str, value: Value<G>) -> &mut Self {
        self.variables.insert(name.to_owned(), value);
        self
    }

    /// Removes all variables from the scope. Constants and functions are not removed.
    pub fn clear(&mut self) {
        self.variables.clear();
    }

    /// Checks if the scope contains a function with the specified name.
    pub fn contains_fn(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }

    /// Defines a function with the specified name.
    pub fn insert_fn<F>(&mut self, name: &str, fun: F) -> &mut Self
    where
        F: Function<G> + 'a,
    {
        let fn_type = fun.ty();
        self.functions
            .insert(name.to_owned(), (fn_type, Rc::new(fun)));
        self
    }

    pub(crate) fn insert_fn_inner(&mut self, name: &str, fun: (FnType, Rc<dyn Function<G> + 'a>)) {
        self.functions.insert(name.to_owned(), fun);
    }

    pub(crate) fn assign<'lv>(
        &mut self,
        lvalue: &SpannedLvalue<'lv>,
        rvalue: Value<G>,
    ) -> Result<(), Spanned<'lv, EvalError>> {
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
                if var_name != "_" {
                    self.variables.insert(var_name.to_owned(), rvalue);
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
}

/// Possible value type.
#[derive(Debug, Clone, Eq)]
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

impl PartialEq for ValueType {
    fn eq(&self, other: &Self) -> bool {
        use self::ValueType::*;
        match (self, other) {
            (Any, _)
            | (_, Any)
            | (Void, Void)
            | (Scalar, Scalar)
            | (Element, Element)
            | (Buffer, Buffer) => true,

            (Tuple(xs), Tuple(ys)) => xs == ys,
            _ => false,
        }
    }
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

    /// Function definition within a function, which is not yet supported.
    #[fail(display = "Embedded functions are not yet supported")]
    EmbeddedFunction,
}

/// Stack of variable scopes that can be used to evaluate `Statement`s.
pub struct Context<'a, G: Group> {
    pub(crate) group: G,
    scopes: Vec<Scope<'a, G>>,
}

impl<G: Group> fmt::Debug for Context<'_, G>
where
    G::Scalar: fmt::Debug,
    G::Element: fmt::Debug,
{
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter
            .debug_struct("ScopeStack")
            .field("scopes", &self.scopes)
            .finish()
    }
}

impl<'a, G: Group> Context<'a, G> {
    /// Creates a new stack with a single global scope.
    pub fn new(group: G) -> Self {
        Self {
            group,
            scopes: vec![Scope::new()],
        }
    }

    pub(crate) fn from_scope(group: G, scope: Scope<'a, G>) -> Self {
        Self {
            group,
            scopes: vec![scope],
        }
    }

    /// Returns an exclusive reference to the innermost scope.
    pub fn innermost_scope(&mut self) -> &mut Scope<'a, G> {
        self.scopes.last_mut().unwrap()
    }

    /// Creates a new scope and pushes it onto the stack.
    pub fn create_scope(&mut self) {
        self.scopes.push(Scope::new());
    }

    /// Pops the innermost scope.
    pub fn pop_scope(&mut self) -> Option<Scope<'a, G>> {
        if self.scopes.len() > 1 {
            self.scopes.pop() // should always be `Some(_)`
        } else {
            None
        }
    }

    /// Gets the variable with the specified name. The variable is looked up starting from
    /// the innermost scope.
    pub fn get_var(&self, name: &str) -> Option<&Value<G>> {
        self.scopes
            .iter()
            .rev()
            .filter_map(|scope| scope.get_var(name))
            .next()
    }

    /// Gets the function with the specified name. The variable is looked up starting from
    /// the innermost scope.
    pub(crate) fn get_fn(&self, name: &str) -> Option<&(FnType, Rc<dyn Function<G> + 'a>)> {
        self.scopes
            .iter()
            .rev()
            .filter_map(|scope| scope.functions.get(name))
            .next()
    }

    /// Evaluates expression.
    pub fn evaluate_expr(
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
                let args: Result<Vec<_>, _> =
                    args.iter().map(|arg| self.evaluate_expr(arg)).collect();
                let args = args?;

                let resolved_name = &name.fragment[1..];
                let (ty, func) = self
                    .get_fn(resolved_name)
                    .ok_or_else(|| map_span(name, EvalError::UndefinedFunction))?;

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

            Block(ref statements) => {
                self.create_scope();
                let result = self.evaluate(statements);
                self.scopes.pop(); // Clear the scope in any case
                result
            }
        }
    }

    /// Evaluates a list of statements.
    pub fn evaluate(
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

                Fn(def) => {
                    let fun = InterpretedFn::new(def, self)?;
                    self.innermost_scope().insert_fn(def.name.fragment, fun);
                }

                Assignment { ref lhs, ref rhs } => {
                    let evaluated = self.evaluate_expr(rhs)?;
                    self.scopes.last_mut().unwrap().assign(lhs, evaluated)?;
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

/// Arena-based code holder.
#[derive(Default)]
pub struct Code {
    snippets: Arena<String>,
}

impl fmt::Debug for Code {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.debug_tuple("Code").field(&"_").finish()
    }
}

impl Code {
    /// Creates an empty code holder.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds an expression to the holder.
    pub fn add_expr(&self, mut code: String) -> Result<SpannedExpr, Spanned<ParseError>> {
        code.push('\0');
        let code = self.snippets.alloc(code);
        let len = code.len();
        match Expr::parse(code) {
            Ok(expr) => Ok(expr),
            Err(_) => Expr::parse(&code[..(len - 1)]),
        }
    }

    /// Adds a list of statements to the holder.
    pub fn add_statements(
        &self,
        mut code: String,
    ) -> Result<Vec<SpannedStatement>, Spanned<ParseError>> {
        // FIXME: this is slow (we need to parse a string twice)
        code.push('\0');
        let code = self.snippets.alloc(code);
        let len = code.len();
        match Statement::list_from_str(code) {
            Ok(statements) => Ok(statements),
            Err(_) => Statement::list_from_str(&code[..(len - 1)]),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        functions::{FromSha512, Rand},
        groups::{Ed25519, Ed25519Error},
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
        let code = Code::new();
        let mut state = Context::new(Ed25519);
        state
            .innermost_scope()
            .insert_fn("sc_sha512", FromSha512)
            .insert_var("x", Value::Scalar(Scalar::from(5_u64)))
            .insert_var("G", Value::Element(ED25519_BASEPOINT_POINT));

        let scalar_expr = code.add_expr("(x + 1) * 10 + 9".to_owned()).unwrap();
        let output = state.evaluate_expr(&scalar_expr).unwrap();
        assert_eq!(output, Value::Scalar(Scalar::from(69_u64)));

        let scalar_expr = code.add_expr("4/5".to_owned()).unwrap();
        let output = state.evaluate_expr(&scalar_expr).unwrap();
        let expected = Scalar::from(4_u64) * Scalar::from(5_u64).invert();
        assert_eq!(output, Value::Scalar(expected));

        let scalar_expr = "1 + 4 / (x + 1 - 6)";
        let scalar_expr = code.add_expr(scalar_expr.to_owned()).unwrap();
        let error = state.evaluate_expr(&scalar_expr).unwrap_err();
        assert_matches!(error.extra, EvalError::DivisionByZero);

        let scalar_expr =
            "16 + 0xs_deaffeeddeaffeeddeaffeeddeaffeeddeaffeeddeaffeedfedcba0504030201";
        let scalar_expr = code.add_expr(scalar_expr.to_owned()).unwrap();
        let output = state.evaluate_expr(&scalar_expr).unwrap();
        let bytes = hex::decode("eeaffeeddeaffeeddeaffeeddeaffeeddeaffeeddeaffeedfedcba0504030201")
            .unwrap();
        let bytes = bytes[..].try_into().unwrap();
        let expected = Scalar::from_canonical_bytes(bytes).unwrap();
        assert_eq!(output, Value::Scalar(expected));

        let scalar_expr =
            "0xs_01234567_89abcdef_01234567_89abcdef_01234567_89abcdef_01234567_89abcdef";
        let scalar_expr = code.add_expr(scalar_expr.to_owned()).unwrap();
        let error = state.evaluate_expr(&scalar_expr).unwrap_err();
        assert_matches!(
            error.extra,
            EvalError::BufferToScalar(ref e)
                if e.downcast_ref::<Ed25519Error>() == Some(&Ed25519Error::NonCanonicalScalar)
        );

        let scalar_expr = ":sc_sha512(0x01000000, 1001 * G)";
        let scalar_expr = code.add_expr(scalar_expr.to_owned()).unwrap();
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

        state
            .innermost_scope()
            .insert_fn("sc_rand", Rand::new(thread_rng()));
        let scalar_expr = ":sc_rand()";
        let scalar_expr = code.add_expr(scalar_expr.to_owned()).unwrap();
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
        let code = Code::new();
        let mut state = Context::new(Ed25519);
        state
            .innermost_scope()
            .insert_var("x", Value::Scalar(Scalar::from(5_u64)))
            .insert_var("G", Value::Element(ED25519_BASEPOINT_POINT));
        let element_expr = code.add_expr("x*G".to_owned()).unwrap();
        let output = state.evaluate_expr(&element_expr).unwrap();
        let expected = ED25519_BASEPOINT_POINT * Scalar::from(5_u64);
        assert_eq!(output, Value::Element(expected));

        let element_expr = "((x + 1) / 2) * G";
        let element_expr = code.add_expr(element_expr.to_owned()).unwrap();
        let output = state.evaluate_expr(&element_expr).unwrap();
        let expected = ED25519_BASEPOINT_POINT * Scalar::from(3_u64);
        assert_eq!(output, Value::Element(expected));

        let element_expr = "(x/3) * G + [1/3]G";
        let element_expr = code.add_expr(element_expr.to_owned()).unwrap();
        let output = state.evaluate_expr(&element_expr).unwrap();
        let expected = ED25519_BASEPOINT_POINT * Scalar::from(2_u64);
        assert_eq!(output, Value::Element(expected));

        let random_scalar = Scalar::random(&mut thread_rng());
        let random_point = ED25519_BASEPOINT_POINT * random_scalar;
        let element_expr = format!(
            "0xg_{} - [0xs_{}]G",
            hex::encode(random_point.compress().as_bytes()),
            hex::encode(random_scalar.as_bytes())
        );
        let element_expr = code.add_expr(element_expr).unwrap();
        let output = state.evaluate_expr(&element_expr).unwrap();
        if let Value::Element(output) = output {
            assert!(output.is_identity());
        } else {
            unreachable!("Invalid expression type");
        }
    }
}
