//! Functions.

use curve25519::scalar::Scalar;
use failure::{format_err, Error};
use rand_core::{CryptoRng, RngCore};
use sha2::{Digest, Sha512};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt,
    rc::Rc,
};

use crate::{
    groups::Ed25519,
    parser::{
        create_span_ref, Expr, FnDefinition, Lvalue, Spanned, SpannedExpr, SpannedLvalue,
        SpannedStatement, Statement,
    },
    type_inference::TypeError,
    Context, Group, Scope, Value, ValueType,
};

/// Constraints on a type.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TypeConstraint {
    /// The type may be non-linear.
    ///
    /// Linear type `T` defines `T + T: T`, `T - T: T`, `Sc * T: T` and `T / Sc: T` operations.
    /// Linear types include scalars, elements, voids and tuples with linear components.
    /// Examples of non-linear types are `bytes` and `bool`.
    MaybeNonLinear,
}

impl fmt::Display for TypeConstraint {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypeConstraint::MaybeNonLinear => formatter.write_str("?Lin"),
        }
    }
}

/// Function type.
#[derive(Debug, Clone, PartialEq)]
pub struct FnType {
    /// Type of function arguments.
    pub args: FnArgs,
    /// Type of the value returned by the function.
    pub return_type: ValueType,
    /// Number of type parameters.
    pub type_count: usize,
    /// Constraints on the type parameters.
    pub constraints: Option<HashMap<usize, TypeConstraint>>,
}

impl fmt::Display for FnType {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("fn")?;
        if self.type_count > 0 {
            formatter.write_str("<")?;

            for i in 0..self.type_count {
                formatter.write_str(ValueType::type_param(i).as_ref())?;
                if !self.is_linear(i) {
                    formatter.write_str(": ?Lin")?;
                }
                if i + 1 < self.type_count {
                    formatter.write_str(", ")?;
                }
            }
            formatter.write_str(">")?;
        }
        write!(formatter, "({})", self.args)?;
        if let ValueType::Void = self.return_type {
            // We need to use `if let` rather than comparison to handle `return_type == Any`.
        } else {
            write!(formatter, " -> {}", self.return_type)?;
        }
        Ok(())
    }
}

impl FnType {
    pub(crate) fn new(
        mut args: Vec<ValueType>,
        mut return_type: ValueType,
        linear_types: &HashSet<usize>,
    ) -> Self {
        let mut reduced = HashMap::new();
        for ty in args.iter_mut().chain(Some(&mut return_type)) {
            reduce(&mut reduced, ty, linear_types);
        }

        fn reduce(
            reductions: &mut HashMap<usize, (usize, bool)>,
            ty: &mut ValueType,
            linear_types: &HashSet<usize>,
        ) {
            let len = reductions.len();
            if let ValueType::TypeVar(idx) = ty {
                let (reduced_idx, _) = *reductions
                    .entry(*idx)
                    .or_insert_with(|| (len, linear_types.contains(idx)));
                *ty = ValueType::TypeVar(reduced_idx);
            } else if let ValueType::Tuple(ref mut fragments) = ty {
                for fragment in fragments {
                    reduce(reductions, fragment, linear_types);
                }
            }
        }

        let constraints = if !reduced.is_empty() {
            let collected: HashMap<_, _> = reduced
                .values()
                .filter_map(|(idx, is_linear)| {
                    if !*is_linear {
                        Some((*idx, TypeConstraint::MaybeNonLinear))
                    } else {
                        None
                    }
                })
                .collect();
            if !collected.is_empty() {
                Some(collected)
            } else {
                None
            }
        } else {
            None
        };

        Self {
            args: FnArgs::List(args),
            return_type,
            type_count: reduced.len(),
            constraints,
        }
    }

    pub(crate) fn any(args_len: usize) -> Self {
        Self {
            args: FnArgs::List((0..args_len).map(|_| ValueType::Any).collect()),
            return_type: ValueType::Any,
            type_count: 0,
            constraints: None,
        }
    }

    /// Checks if a type variable with the specified index is linear.
    pub(crate) fn is_linear(&self, var_idx: usize) -> bool {
        debug_assert!(var_idx < self.type_count);
        self.constraints
            .as_ref()
            .and_then(|constraints| constraints.get(&var_idx))
            .is_none()
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
pub trait NativeFn<G: Group> {
    /// Returns the type signature of this function.
    fn ty(&self) -> FnType;
    /// Executes the function on the specified arguments.
    fn execute(&self, args: &[Value<G>]) -> Result<Value<G>, Error>;
}

/// Function converting any serializable arguments into a scalar.
#[derive(Debug, Clone, Copy)]
pub struct FromSha512;

impl NativeFn<Ed25519> for FromSha512 {
    fn ty(&self) -> FnType {
        FnType {
            args: FnArgs::Any,
            return_type: ValueType::Scalar,
            type_count: 0,
            constraints: None,
        }
    }

    fn execute(&self, args: &[Value<Ed25519>]) -> Result<Value<Ed25519>, Error> {
        fn input_var(hash: &mut Sha512, var: &Value<Ed25519>) {
            match var {
                Value::Bool(b) => hash.input(&[*b as u8]),
                Value::Bytes(buffer) => hash.input(buffer),
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
#[derive(Debug, Clone)]
pub struct Rand<R>(RefCell<R>);

impl<R: CryptoRng + RngCore> Rand<R> {
    /// Creates a new function instance.
    pub fn new(rng: R) -> Self {
        Rand(RefCell::new(rng))
    }
}

impl<R: CryptoRng + RngCore> NativeFn<Ed25519> for Rand<R> {
    fn ty(&self) -> FnType {
        FnType {
            args: FnArgs::List(vec![]),
            return_type: ValueType::Scalar,
            type_count: 0,
            constraints: None,
        }
    }

    fn execute(&self, args: &[Value<Ed25519>]) -> Result<Value<Ed25519>, Error> {
        debug_assert!(args.is_empty());
        let mut rng = self.0.borrow_mut();
        Ok(Value::Scalar(Scalar::random(&mut *rng)))
    }
}

/// Assertion function.
#[derive(Debug, Clone, Copy)]
pub struct Assert;

impl<G: Group> NativeFn<G> for Assert {
    fn ty(&self) -> FnType {
        FnType {
            args: FnArgs::List(vec![ValueType::Bool]),
            return_type: ValueType::Void,
            type_count: 0,
            constraints: None,
        }
    }

    fn execute(&self, args: &[Value<G>]) -> Result<Value<G>, Error> {
        match args {
            [Value::Bool(true)] => Ok(Value::Void),
            [Value::Bool(false)] => Err(format_err!("Assertion failed")),
            _ => unreachable!(),
        }
    }
}

/// Function defined within the interpreter.
pub struct InterpretedFn<'a, G: Group> {
    pub(crate) definition: Spanned<'a, FnDefinition<'a>>,
    ty: FnType,
    pub(crate) captures: Scope<'a, G>,
}

impl<G: Group> fmt::Debug for InterpretedFn<'_, G>
where
    G::Scalar: fmt::Debug,
    G::Element: fmt::Debug,
{
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter
            .debug_struct("InterpretedFn")
            .field("definition", &self.definition)
            .field("captures", &self.captures)
            .finish()
    }
}

impl<'a, G: Group> InterpretedFn<'a, G> {
    /// Creates a new function.
    pub fn new(
        definition: Spanned<'a, FnDefinition<'a>>,
        context: &Context<'a, G>,
    ) -> Result<Self, Spanned<'a, TypeError>> {
        let mut captures = Scope::new();
        let mut local_vars = HashSet::new();

        for arg in &definition.extra.args {
            set_local_vars(&mut local_vars, arg);
        }
        for statement in &definition.extra.body {
            process_vars_in_statement(&mut captures, &mut local_vars, statement, context)?;
        }

        Ok(Self {
            ty: FnType::any(definition.extra.args.len()),
            definition,
            captures,
        })
    }

    /// Returns the function type.
    pub fn ty(&self) -> &FnType {
        &self.ty
    }

    pub(crate) fn set_ty(&mut self, ty: FnType) {
        self.ty = ty;
    }
}

/// Container type for all functions.
#[derive(Clone)]
pub enum Function<'a, G: Group> {
    /// Native function.
    Native(FnType, Rc<dyn NativeFn<G>>),
    /// Interpreted function.
    Interpreted(Rc<InterpretedFn<'a, G>>),
}

impl<G: Group> fmt::Debug for Function<'_, G>
where
    G::Scalar: fmt::Debug,
    G::Element: fmt::Debug,
{
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Function::Native(..) => formatter.debug_tuple("Native").field(&"_").finish(),
            Function::Interpreted(func) => {
                formatter.debug_tuple("Interpreted").field(func).finish()
            }
        }
    }
}

impl<'a, G: Group> Function<'a, G> {
    pub(crate) fn native<F: NativeFn<G> + 'static>(f: F) -> Self {
        Function::Native(f.ty(), Rc::new(f))
    }

    /// Returns the function type.
    pub fn ty(&self) -> &FnType {
        match self {
            Function::Native(ty, _) => ty,
            Function::Interpreted(func) => func.ty(),
        }
    }

    /// Returns the definition of a function.
    pub fn definition(&self) -> Option<&Spanned<'a, FnDefinition<'a>>> {
        match self {
            Function::Native(..) => None,
            Function::Interpreted(func) => Some(&func.definition),
        }
    }
}

fn set_local_vars<'lv>(local_vars: &mut HashSet<&'lv str>, lvalue: &SpannedLvalue<'lv>) {
    match lvalue.extra {
        Lvalue::Variable { .. } => {
            if lvalue.fragment != "_" {
                local_vars.insert(lvalue.fragment);
            }
        }
        Lvalue::Tuple(ref fragments) => {
            for fragment in fragments {
                set_local_vars(local_vars, fragment);
            }
        }
    }
}

fn process_vars<'a, G: Group>(
    captures: &mut Scope<'a, G>,
    local_vars: &mut HashSet<&'a str>,
    expr: &SpannedExpr<'a>,
    context: &Context<'a, G>,
) -> Result<(), Spanned<'a, TypeError>> {
    match expr.extra {
        Expr::Variable => {
            let var_name = expr.fragment;
            if local_vars.contains(var_name) || captures.contains_var(var_name) {
                // No action needs to be performed
            } else if let Some(val) = context.get_var(var_name) {
                captures.insert_var(var_name, val.clone());
            } else {
                return Err(create_span_ref(
                    expr,
                    TypeError::UndefinedVar(var_name.to_owned()),
                ));
            }
        }

        Expr::Number | Expr::Literal { .. } => { /* no action */ }

        Expr::Tuple(ref fragments) => {
            for fragment in fragments {
                process_vars(captures, local_vars, fragment, context)?;
            }
        }
        Expr::Unary { ref inner, .. } => {
            process_vars(captures, local_vars, inner, context)?;
        }
        Expr::Binary {
            ref lhs, ref rhs, ..
        } => {
            process_vars(captures, local_vars, lhs, context)?;
            process_vars(captures, local_vars, rhs, context)?;
        }
        Expr::Function { ref args, name } => {
            for arg in args {
                process_vars(captures, local_vars, arg, context)?;
            }
            let fn_name = &name.fragment[1..];
            if captures.contains_fn(fn_name) {
                // No action required.
            } else if let Some(fun) = context.get_fn(fn_name) {
                captures.insert_fn(fn_name, fun.clone());
            } else {
                return Err(create_span_ref(
                    &name,
                    TypeError::UndefinedFn(fn_name.to_owned()),
                ));
            }
        }
        Expr::Block(ref statements) => {
            for statement in statements {
                process_vars_in_statement(captures, local_vars, statement, context)?;
            }
        }
    }
    Ok(())
}

fn process_vars_in_statement<'a, G: Group>(
    captures: &mut Scope<'a, G>,
    local_vars: &mut HashSet<&'a str>,
    statement: &SpannedStatement<'a>,
    context: &Context<'a, G>,
) -> Result<(), Spanned<'a, TypeError>> {
    match statement.extra {
        Statement::Expr(ref expr) => process_vars(captures, local_vars, expr, context),
        Statement::Assignment { ref lhs, ref rhs } => {
            process_vars(captures, local_vars, rhs, context)?;
            set_local_vars(local_vars, lhs);
            Ok(())
        }
        Statement::Empty => Ok(()),
        Statement::Fn(_) => Err(create_span_ref(statement, TypeError::EmbeddedFunction)),
    }
}
