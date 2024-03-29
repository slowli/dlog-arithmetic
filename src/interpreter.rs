use failure_derive::*;
use rand_core::{CryptoRng, RngCore};
use std::{borrow::Cow, collections::HashMap, fmt, ops, rc::Rc};
use typed_arena::Arena;

use crate::{
    functions::{Assert, FnArgs, FnType, FromSha512, Function, InterpretedFn, NativeFn, Rand},
    groups::Group,
    parser::{
        create_span, create_span_ref, map_span, BinaryOp, Error as ParseError, Expr, LiteralType,
        Lvalue, Span, Spanned, SpannedExpr, SpannedLvalue, SpannedStatement, Statement, UnaryOp,
    },
    type_inference::{Substitutions, TypeContext, TypeError},
};

/// Value used in finite group arithmetic.
pub enum Value<G: Group> {
    /// Absence of value, `()` in Rust terms.
    Void,
    /// Boolean value.
    Bool(bool),
    /// Scalar value.
    Scalar(G::Scalar),
    /// Group element.
    Element(G::Element),
    /// Arbitrary-sized byte buffer.
    Bytes(Vec<u8>),
    /// Tuple of values.
    Tuple(Vec<Value<G>>),
}

impl<G: Group> Clone for Value<G> {
    fn clone(&self) -> Self {
        match self {
            Value::Void => Value::Void,
            Value::Bool(b) => Value::Bool(*b),
            Value::Scalar(sc) => Value::Scalar(*sc),
            Value::Element(ge) => Value::Element(*ge),
            Value::Bytes(ref buffer) => Value::Bytes(buffer.clone()),
            Value::Tuple(ref fragments) => Value::Tuple(fragments.clone()),
        }
    }
}

impl<G: Group> PartialEq for Value<G> {
    fn eq(&self, rhs: &Self) -> bool {
        use self::Value::*;
        match (self, rhs) {
            (Void, Void) => true,
            (Bool(x), Bool(y)) => x == y,
            (Scalar(x), Scalar(y)) => x == y,
            (Element(x), Element(y)) => x == y,
            (Bytes(x), Bytes(y)) => x == y,
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
            Value::Bool(b) => formatter.debug_tuple("Bool").field(b).finish(),
            Value::Scalar(value) => formatter.debug_tuple("Scalar").field(value).finish(),
            Value::Element(value) => formatter.debug_tuple("Element").field(value).finish(),
            Value::Bytes(buffer) => formatter.debug_tuple("Bytes").field(buffer).finish(),
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
            Value::Bool(_) => ValueType::Bool,
            Value::Scalar(_) => ValueType::Scalar,
            Value::Element(_) => ValueType::Element,
            Value::Bytes(_) => ValueType::Bytes,
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

impl<G: Group> ops::Not for Value<G> {
    type Output = Result<Self, EvalError>;

    fn not(self) -> Self::Output {
        match self {
            Value::Bool(b) => Ok(Value::Bool(!b)),
            _ => Err(EvalError::InvalidUnaryOp {
                op: "!",
                ty: self.ty(),
            }),
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

            (Bytes(mut x), Bytes(y)) => Ok(Value::Bytes({
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
    functions: HashMap<String, Function<'a, G>>,
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
            .entries(&self.functions)
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
            .map(|(name, fun)| (name.as_str(), fun.ty()))
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
    pub(crate) fn insert_fn(&mut self, name: &str, fun: Function<'a, G>) {
        self.functions.insert(name.to_owned(), fun);
    }

    /// Inserts a native function into the context.
    pub fn insert_native_fn<F>(&mut self, name: &str, fun: F) -> &mut Self
    where
        F: NativeFn<G> + 'static,
    {
        self.functions
            .insert(name.to_owned(), Function::native(fun));
        self
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
                        return Err(create_span_ref(
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
                        return Err(create_span_ref(
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
                    return Err(create_span_ref(
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
    /// Boolean.
    Bool,
    /// Group scalar.
    Scalar,
    /// Group element.
    Element,
    /// Byte buffer.
    Bytes,
    /// Tuple.
    Tuple(Vec<ValueType>),
    /// Type variable.
    TypeVar(usize),
}

impl PartialEq for ValueType {
    fn eq(&self, other: &Self) -> bool {
        use self::ValueType::*;
        match (self, other) {
            (Any, _)
            | (_, Any)
            | (Void, Void)
            | (Bool, Bool)
            | (Scalar, Scalar)
            | (Element, Element)
            | (Bytes, Bytes) => true,

            (TypeVar(x), TypeVar(y)) => x == y,
            (Tuple(xs), Tuple(ys)) => xs == ys,
            _ => false,
        }
    }
}

impl fmt::Display for ValueType {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ValueType::Any => formatter.write_str("_"),
            ValueType::TypeVar(idx) => formatter.write_str(Self::type_param(*idx).as_ref()),

            ValueType::Void => formatter.write_str("void"),
            ValueType::Bool => formatter.write_str("bool"),
            ValueType::Bytes => formatter.write_str("bytes"),
            ValueType::Scalar => formatter.write_str("Sc"),
            ValueType::Element => formatter.write_str("Ge"),
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

impl ValueType {
    pub(crate) fn type_param(index: usize) -> Cow<'static, str> {
        const PARAM_NAMES: &str = "TUVXYZ";
        PARAM_NAMES
            .get(index..=index)
            .map(Cow::from)
            .unwrap_or_else(|| Cow::from(format!("T{}", index - PARAM_NAMES.len())))
    }
}

/// Error that can occur during expression evaluation.
#[derive(Debug, Fail)]
pub enum EvalError {
    /// Error converting a number to a scalar.
    #[fail(display = "Error converting number to scalar: {}", _0)]
    IntToScalar(#[fail(cause)] failure::Error),

    /// Error converting bytes to a scalar.
    #[fail(display = "Error converting buffer to scalar: {}", _0)]
    BytesToScalar(#[fail(cause)] failure::Error),

    /// Error converting bytes to a group element.
    #[fail(display = "Error converting buffer to element: {}", _0)]
    BytesToElement(#[fail(cause)] failure::Error),

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

    /// Invalid value type for a unary operation.
    #[fail(display = "Invalid argument for a unary operation")]
    InvalidUnaryOp {
        /// Operator.
        op: &'static str,
        /// Type of the argument.
        ty: ValueType,
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

    /// Type inference error.
    #[fail(display = "Type inference error: {}", _0)]
    Type(#[fail(cause)] TypeError),
}

impl From<TypeError> for EvalError {
    fn from(e: TypeError) -> Self {
        EvalError::Type(e)
    }
}

/// Call backtrace.
#[derive(Debug, Default)]
pub struct Backtrace<'a> {
    calls: Vec<BacktraceElement<'a>>,
}

/// Function call.
#[derive(Debug, Clone, Copy)]
pub struct BacktraceElement<'a> {
    /// Function name.
    pub fn_name: &'a str,
    /// Code span of the function definition.
    pub def_span: Span<'a>,
    /// Code span of the function call.
    pub call_span: Span<'a>,
}

impl<'a> Backtrace<'a> {
    /// Iterates over the backtrace, starting from the most recent call.
    pub fn calls<'s>(&'s self) -> impl Iterator<Item = BacktraceElement<'a>> + 's {
        self.calls.iter().rev().cloned()
    }

    /// Appends a function call into the backtrace.
    fn push_call(&mut self, fn_name: &'a str, def_span: Span<'a>, call_span: Span<'a>) {
        self.calls.push(BacktraceElement {
            fn_name,
            def_span,
            call_span,
        });
    }

    /// Pops a function call.
    fn pop_call(&mut self) {
        self.calls.pop();
    }
}

/// Error with the associated backtrace.
#[derive(Debug)]
pub struct ErrorWithBacktrace<'a> {
    /// Error.
    pub inner: Spanned<'a, EvalError>,
    /// Backtrace information.
    pub backtrace: Backtrace<'a>,
}

/// Stack of variable scopes that can be used to evaluate `Statement`s.
pub struct Context<'a, G: Group> {
    pub(crate) group: G,
    scopes: Vec<Scope<'a, G>>,
    type_inference: bool,
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
    /// Creates a new context.
    pub fn new(group: G) -> Self {
        Self {
            group,
            scopes: vec![Scope::new()],
            type_inference: false,
        }
    }

    /// Switches on type inference of the evaluated statements / expressions.
    pub fn enable_type_inference(&mut self) {
        self.type_inference = true;
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
    pub fn get_fn(&self, name: &str) -> Option<&Function<'a, G>> {
        self.scopes
            .iter()
            .rev()
            .filter_map(|scope| scope.functions.get(name))
            .next()
    }

    fn check_fn_args(
        expr: &SpannedExpr<'a>,
        args: &[Value<G>],
        ty: &FnType,
    ) -> Result<(), Spanned<'a, EvalError>> {
        if let FnArgs::List(ref expected_types) = ty.args {
            let arg_types = args.iter().map(Value::ty);
            let mut substitutions = Substitutions::default();
            for (expected_ty, arg_ty) in expected_types.iter().zip(arg_types) {
                substitutions.unify(expected_ty, &arg_ty).map_err(|_| {
                    create_span_ref(
                        expr,
                        EvalError::ArgTypeMismatch {
                            expected: ty.args.clone(),
                        },
                    )
                })?;
            }
        }
        Ok(())
    }

    fn evaluate_fn(
        &mut self,
        expr: &SpannedExpr<'a>,
        func: &InterpretedFn<'a, G>,
        args: &[Value<G>],
        backtrace: &mut Option<Backtrace<'a>>,
    ) -> Result<Value<G>, Spanned<'a, EvalError>> {
        let name = match expr.extra {
            Expr::Function { name, .. } => name,
            _ => unreachable!(),
        };
        let def = &func.definition.extra;

        if let Some(backtrace) = backtrace {
            backtrace.push_call(
                &name.fragment[1..],
                create_span_ref(&func.definition, ()),
                create_span_ref(expr, ()),
            );
        }
        self.scopes.push(func.captures.clone());
        for (lvalue, val) in def.args.iter().zip(args) {
            self.innermost_scope().assign(lvalue, val.clone())?;
        }
        let result = self.evaluate_inner(&def.body, backtrace, None);

        if result.is_ok() {
            if let Some(backtrace) = backtrace {
                backtrace.pop_call();
            }
        }
        self.pop_scope();
        result
    }

    fn evaluate_expr_inner(
        &mut self,
        expr: &SpannedExpr<'a>,
        backtrace: &mut Option<Backtrace<'a>>,
    ) -> Result<Value<G>, Spanned<'a, EvalError>> {
        match expr.extra {
            Expr::Variable => self.get_var(expr.fragment).cloned().ok_or_else(|| {
                create_span_ref(
                    expr,
                    TypeError::UndefinedVar(expr.fragment.to_owned()).into(),
                )
            }),

            Expr::Number => {
                let value = expr
                    .fragment
                    .parse::<u64>()
                    .map_err(|e| create_span_ref(expr, EvalError::IntToScalar(e.into())))?;
                self.group
                    .scalar_from_u64(value)
                    .map(Value::Scalar)
                    .map_err(|e| create_span_ref(expr, EvalError::IntToScalar(e.into())))
            }

            Expr::Literal { ty, ref value } => match ty {
                LiteralType::Bytes => Ok(Value::Bytes(value.clone())),
                LiteralType::Scalar => self
                    .group
                    .scalar_from_bytes(value)
                    .map(Value::Scalar)
                    .map_err(|e| create_span_ref(expr, EvalError::BytesToScalar(e.into()))),
                LiteralType::Element => self
                    .group
                    .element_from_bytes(value)
                    .map(Value::Element)
                    .map_err(|e| create_span_ref(expr, EvalError::BytesToElement(e.into()))),
            },

            Expr::Tuple(ref fragments) => {
                let fragments: Result<Vec<_>, _> = fragments
                    .iter()
                    .map(|frag| self.evaluate_expr_inner(frag, backtrace))
                    .collect();
                fragments.map(Value::Tuple)
            }

            Expr::Function { name, ref args } => {
                let args: Result<Vec<_>, _> = args
                    .iter()
                    .map(|arg| self.evaluate_expr_inner(arg, backtrace))
                    .collect();
                let args = args?;

                let resolved_name = &name.fragment[1..];
                if let Some(func) = self.get_fn(resolved_name).cloned() {
                    if !self.type_inference {
                        // If type inference is on, types are checked earlier.
                        Self::check_fn_args(expr, &args, func.ty())?;
                    }
                    match func {
                        Function::Interpreted(ref func) => {
                            self.evaluate_fn(expr, func, &args, backtrace)
                        }
                        Function::Native(_, ref func) => func
                            .execute(&args)
                            .map_err(|e| create_span_ref(expr, EvalError::FunctionCall(e))),
                    }
                } else {
                    Err(create_span(
                        name,
                        TypeError::UndefinedFn(resolved_name.to_owned()).into(),
                    ))
                }
            }

            // Arithmetic operations
            Expr::Unary { ref inner, op } => {
                let val = self.evaluate_expr_inner(inner, backtrace)?;

                match op.extra {
                    UnaryOp::Not => (!val).map_err(|e| create_span_ref(expr, e)),
                    UnaryOp::Neg => {
                        // FIXME: this may be slow
                        let minus_one = Value::Scalar(-self.group.scalar_from_u64(1).unwrap());
                        (minus_one * val).map_err(|e| create_span_ref(expr, e))
                    }
                }
            }

            Expr::Binary {
                lhs: ref x,
                rhs: ref y,
                op,
            } => {
                let lhs = self.evaluate_expr_inner(x, backtrace)?;

                // Short-circuit logic for bool operations.
                match op.extra {
                    BinaryOp::And | BinaryOp::Or => match lhs {
                        Value::Bool(b) => {
                            if !b && op.extra == BinaryOp::And {
                                return Ok(Value::Bool(false));
                            } else if b && op.extra == BinaryOp::Or {
                                return Ok(Value::Bool(true));
                            }
                        }

                        _ => {
                            return Err(create_span_ref(
                                expr,
                                EvalError::InvalidBinaryOp {
                                    op: op.extra.as_str(),
                                    lhs_ty: lhs.ty(),
                                    rhs_ty: ValueType::Any,
                                },
                            ));
                        }
                    },

                    _ => { /* do nothing yet */ }
                }

                let rhs = self.evaluate_expr_inner(y, backtrace)?;
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

                    BinaryOp::Eq | BinaryOp::NotEq => {
                        let (lhs_ty, rhs_ty) = (lhs.ty(), rhs.ty());
                        if lhs_ty != rhs_ty {
                            Err(EvalError::InvalidBinaryOp {
                                op: op.extra.as_str(),
                                lhs_ty,
                                rhs_ty,
                            })
                        } else if op.extra == BinaryOp::Eq {
                            Ok(Value::Bool(lhs == rhs))
                        } else {
                            Ok(Value::Bool(lhs != rhs))
                        }
                    }

                    BinaryOp::And | BinaryOp::Or => {
                        match rhs {
                            // This works since we know that AND / OR hasn't short-circuited.
                            Value::Bool(b) => Ok(Value::Bool(b)),

                            _ => Err(EvalError::InvalidBinaryOp {
                                op: op.extra.as_str(),
                                lhs_ty: ValueType::Bool,
                                rhs_ty: rhs.ty(),
                            }),
                        }
                    }
                }
                .map_err(|e| create_span_ref(expr, e))
            }

            Expr::Block(ref statements) => {
                self.create_scope();
                let result = self.evaluate_inner(statements, backtrace, None);
                self.scopes.pop(); // Clear the scope in any case
                result
            }
        }
    }

    /// Evaluates expression.
    pub fn evaluate_expr(
        &mut self,
        expr: &SpannedExpr<'a>,
    ) -> Result<Value<G>, ErrorWithBacktrace<'a>> {
        if self.type_inference {
            let mut type_context = TypeContext::new(self);
            type_context
                .process_expr(expr)
                .map_err(|e| ErrorWithBacktrace {
                    inner: map_span(e, Into::into),
                    backtrace: Backtrace::default(),
                })?;
        }

        let mut backtrace = Some(Backtrace::default());
        self.evaluate_expr_inner(expr, &mut backtrace)
            .map_err(|e| ErrorWithBacktrace {
                inner: e,
                backtrace: backtrace.unwrap(),
            })
    }

    /// Evaluates a list of statements.
    fn evaluate_inner(
        &mut self,
        statements: &[SpannedStatement<'a>],
        backtrace: &mut Option<Backtrace<'a>>,
        fn_types: Option<&HashMap<&'a str, FnType>>,
    ) -> Result<Value<G>, Spanned<'a, EvalError>> {
        use crate::parser::Statement::*;

        let mut return_value = Value::Void;
        for statement in statements {
            return_value = Value::Void;
            match &statement.extra {
                Empty => {}

                Expr(expr) => {
                    return_value = self.evaluate_expr_inner(expr, backtrace)?;
                }

                Fn(def) => {
                    let mut fun = InterpretedFn::new(create_span_ref(statement, def.clone()), self)
                        .map_err(|e| map_span(e, Into::into))?;
                    // TODO: this type assignment can backfire if a function is redefined.
                    if let Some(fn_types) = fn_types {
                        fun.set_ty(fn_types[def.name.fragment].clone());
                    }
                    self.innermost_scope()
                        .insert_fn(def.name.fragment, Function::Interpreted(Rc::new(fun)));
                }

                Assignment { ref lhs, ref rhs } => {
                    let evaluated = self.evaluate_expr_inner(rhs, backtrace)?;
                    self.scopes.last_mut().unwrap().assign(lhs, evaluated)?;
                }
            }
        }
        Ok(return_value)
    }

    /// Evaluates a list of statements.
    pub fn evaluate(
        &mut self,
        statements: &[SpannedStatement<'a>],
    ) -> Result<Value<G>, ErrorWithBacktrace<'a>> {
        let fun_types = if self.type_inference {
            let mut type_context = TypeContext::new(self);
            type_context
                .process_statements(statements)
                .map_err(|e| ErrorWithBacktrace {
                    inner: map_span(e, Into::into),
                    backtrace: Backtrace::default(),
                })?;
            Some(type_context.innermost_scope().functions().clone())
        } else {
            None
        };

        let mut backtrace = Some(Backtrace::default());
        self.evaluate_inner(statements, &mut backtrace, fun_types.as_ref())
            .map_err(|e| ErrorWithBacktrace {
                inner: e,
                backtrace: backtrace.unwrap(),
            })
    }
}

impl<G: Group> Context<'_, G>
where
    FromSha512: NativeFn<G>,
{
    /// Creates a standard context with predefined variables and functions.
    ///
    /// # Variables
    ///
    /// - `O`: the identity element of the group
    /// - `G`: the group basepoint
    /// - `true`, `false`: Boolean constants
    ///
    /// # Functions
    ///
    /// - `assert(bool)`: Asserts that a provided boolean expression is true. See [`Assert`].
    /// - `sc_rand() -> Sc`: Generates a random scalar. See [`Rand`].
    /// - `sc_sha512(...) -> Sc`: Generates a scalar based on the SHA-512 digest of the arguments.
    ///   See [`FromSha512`].
    ///
    /// [`Assert`]: fns/struct.Assert.html
    /// [`Rand`]: fns/struct.Rand.html
    /// [`FromSha512`]: fns/struct.FromSha512.html
    pub fn standard<R>(group: G, rng: R) -> Self
    where
        R: CryptoRng + RngCore + 'static,
        Rand<R>: NativeFn<G>,
    {
        let mut scope = Scope::new();
        scope
            .insert_var("O", Value::Element(group.identity_element()))
            .insert_var("G", Value::Element(group.base_element()))
            .insert_var("true", Value::Bool(true))
            .insert_var("false", Value::Bool(false))
            .insert_native_fn("assert", Assert)
            .insert_native_fn("sc_rand", Rand::new(rng))
            .insert_native_fn("sc_sha512", FromSha512);
        Self {
            group,
            scopes: vec![scope],
            type_inference: false,
        }
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

    /// Adds a string to the holder terminated by a `\0` char.
    pub fn add_terminated_string(&self, mut code: String) -> &str {
        code.push('\0');
        self.snippets.alloc(code)
    }

    /// Adds an expression to the holder.
    pub fn add_expr(&self, code: String) -> Result<SpannedExpr, Spanned<ParseError>> {
        let code = Span::new(self.add_terminated_string(code));
        Expr::parse(code)
    }

    /// Adds a list of statements to the holder.
    pub fn add_statements(
        &self,
        code: String,
    ) -> Result<Vec<SpannedStatement>, Spanned<ParseError>> {
        let code = Span::new(self.add_terminated_string(code));
        Statement::parse_list(code)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        functions::{FromSha512, Rand, TypeConstraint},
        groups::{Ed25519, Ed25519Error},
    };

    use assert_matches::assert_matches;
    use curve25519::{constants::ED25519_BASEPOINT_POINT, scalar::Scalar, traits::IsIdentity};
    use rand::thread_rng;
    use sha2::{Digest, Sha512};
    use std::{collections::HashSet, convert::TryInto, iter::FromIterator};

    #[test]
    fn function_type_display() {
        let ty = FnType {
            args: FnArgs::Any,
            return_type: ValueType::Scalar,
            type_count: 0,
            constraints: None,
        };
        assert_eq!(ty.to_string(), "fn(...) -> Sc");

        let ty = FnType {
            args: FnArgs::List(vec![
                ValueType::Element,
                ValueType::Tuple(vec![ValueType::Scalar, ValueType::Scalar]),
            ]),
            return_type: ValueType::Element,
            type_count: 0,
            constraints: None,
        };
        assert_eq!(ty.to_string(), "fn(Ge, (Sc, Sc)) -> Ge");

        let ty = FnType {
            args: FnArgs::List(vec![
                ValueType::Element,
                ValueType::Tuple(vec![ValueType::Scalar, ValueType::Scalar]),
            ]),
            return_type: ValueType::Void,
            type_count: 0,
            constraints: None,
        };
        assert_eq!(ty.to_string(), "fn(Ge, (Sc, Sc))");

        let ty = FnType {
            args: FnArgs::List(vec![
                ValueType::Element,
                ValueType::Tuple(vec![ValueType::TypeVar(0), ValueType::TypeVar(1)]),
            ]),
            return_type: ValueType::TypeVar(0),
            type_count: 2,
            constraints: Some(HashMap::from_iter(vec![(
                1,
                TypeConstraint::MaybeNonLinear,
            )])),
        };
        assert_eq!(ty.to_string(), "fn<T, U: ?Lin>(Ge, (T, U)) -> T");
    }

    #[test]
    fn evaluating_scalar() {
        let code = Code::new();
        let mut state = Context::new(Ed25519);
        state
            .innermost_scope()
            .insert_native_fn("sc_sha512", FromSha512)
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
        assert_matches!(error.inner.extra, EvalError::DivisionByZero);

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
            error.inner.extra,
            EvalError::BytesToScalar(ref e)
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
            .insert_native_fn("sc_rand", Rand::new(thread_rng()));
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
