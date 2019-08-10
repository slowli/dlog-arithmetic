use failure_derive::*;
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use crate::{
    functions::{FnArgs, FnType, Function},
    interpreter::{Context, Value, ValueType},
    parser::{
        create_span_ref, BinaryOp, Expr, FnDefinition, LiteralType, Lvalue, Spanned, SpannedExpr,
        SpannedLvalue, SpannedStatement, Statement, UnaryOp,
    },
    Group,
};

/// Errors that can occur during type inference.
#[derive(Debug, Clone, Fail)]
pub enum TypeError {
    /// Trying to unify tuples of different sizes.
    #[fail(
        display = "A tuple with {} elements cannot be unified with a tuple with {} elements",
        _0, _1
    )]
    TupleLenMismatch(usize, usize),

    /// Trying to unify incompatible types.
    #[fail(display = "Trying to unify incompatible types `{}` and `{}`", _0, _1)]
    IncompatibleTypes(ValueType, ValueType),

    /// Undefined variable occurrence.
    #[fail(display = "Variable `{}` is not defined", _0)]
    UndefinedVar(String),

    /// Undefined function occurrence.
    #[fail(display = "Function `{}` is not defined", _0)]
    UndefinedFn(String),

    /// Mismatch between the number of args in the function definition and call.
    #[fail(
        display = "Function expects {} args, but is called with {} args",
        expected, actual
    )]
    ArgLenMismatch {
        /// Number of args in function definition.
        expected: usize,
        /// Number of args supplied in the call.
        actual: usize,
    },

    /// Trying to unify a type with a type containing it.
    #[fail(
        display = "Trying to unify a type `T` with a type containing it: {}",
        _0
    )]
    RecursiveType(ValueType),

    /// Non-linear type.
    #[fail(display = "Non-linear type: {}", _0)]
    NonLinearType(ValueType),

    /// Function definition within a function, which is not yet supported.
    #[fail(display = "Embedded functions are not yet supported")]
    EmbeddedFunction,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct Substitutions {
    eqs: HashMap<usize, ValueType>,
    lin: HashSet<usize>,
}

impl Substitutions {
    fn fast_resolve<'a>(&'a self, mut ty: &'a ValueType) -> &'a ValueType {
        while let ValueType::TypeVar(idx) = ty {
            let resolved = self.eqs.get(&idx);
            if let Some(resolved) = resolved {
                ty = resolved;
            } else {
                break;
            }
        }
        ty
    }

    fn resolve<'a>(&'a self, ty: &'a ValueType) -> ValueType {
        let ty = self.fast_resolve(ty);
        if let ValueType::Tuple(ref fragments) = ty {
            ValueType::Tuple(fragments.iter().map(|frag| self.resolve(frag)).collect())
        } else {
            ty.clone()
        }
    }

    pub fn unify(&mut self, lhs: &ValueType, rhs: &ValueType) -> Result<(), TypeError> {
        use self::ValueType::*;

        match (lhs, rhs) {
            (lhs, rhs) if lhs == rhs => {
                // we already know that types are equal
                Ok(())
            }
            (TypeVar(idx), rhs) => self.unify_var(*idx, rhs),
            (lhs, TypeVar(idx)) => self.unify_var(*idx, lhs),

            (Tuple(ref types_l), Tuple(ref types_r)) => {
                if types_l.len() != types_r.len() {
                    return Err(TypeError::TupleLenMismatch(types_l.len(), types_r.len()));
                }
                for (type_l, type_r) in types_l.iter().zip(types_r) {
                    self.unify(type_l, type_r)?;
                }
                Ok(())
            }

            (x, y) => Err(TypeError::IncompatibleTypes(x.clone(), y.clone())),
        }
    }

    fn check_occurrence(&self, var_idx: usize, ty: &ValueType) -> bool {
        if ValueType::TypeVar(var_idx) == *ty {
            true
        } else if let ValueType::TypeVar(idx) = ty {
            if let Some(subst) = self.eqs.get(idx) {
                self.check_occurrence(var_idx, subst)
            } else {
                // `ty` points to a different type var
                false
            }
        } else if let ValueType::Tuple(ref fragments) = ty {
            fragments
                .iter()
                .any(|frag| self.check_occurrence(var_idx, frag))
        } else {
            false
        }
    }

    fn sanitize_type(&self, fixed_idx: usize, ty: &ValueType) -> ValueType {
        match self.resolve(ty) {
            ValueType::TypeVar(i) if i == fixed_idx => ValueType::TypeVar(0),
            ValueType::TypeVar(_) => ValueType::Any,
            ValueType::Tuple(ref fragments) => ValueType::Tuple(
                fragments
                    .iter()
                    .map(|fragment| self.sanitize_type(fixed_idx, fragment))
                    .collect(),
            ),
            simple_ty => simple_ty.clone(),
        }
    }

    fn unify_var(&mut self, var_idx: usize, ty: &ValueType) -> Result<(), TypeError> {
        if let Some(subst) = self.eqs.get(&var_idx).cloned() {
            return self.unify(&subst, ty);
        }
        if let ValueType::TypeVar(idx) = ty {
            if let Some(subst) = self.eqs.get(&idx).cloned() {
                return self.unify(&ValueType::TypeVar(var_idx), &subst);
            }
        }

        if self.check_occurrence(var_idx, ty) {
            Err(TypeError::RecursiveType(self.sanitize_type(var_idx, ty)))
        } else {
            if self.lin.contains(&var_idx) {
                self.mark_as_linear(ty)?;
            }
            self.eqs.insert(var_idx, ty.clone());
            Ok(())
        }
    }

    fn mark_as_linear(&mut self, ty: &ValueType) -> Result<(), TypeError> {
        match ty {
            ValueType::TypeVar(idx) => {
                self.lin.insert(*idx);
                if let Some(subst) = self.eqs.get(idx).cloned() {
                    self.mark_as_linear(&subst)
                } else {
                    Ok(())
                }
            }
            ValueType::Any => unreachable!(),

            ValueType::Bool | ValueType::Buffer => Err(TypeError::NonLinearType(ty.clone())),
            ValueType::Scalar | ValueType::Element | ValueType::Void => {
                // These types are linear.
                Ok(())
            }

            ValueType::Tuple(ref fragments) => {
                for fragment in fragments {
                    self.mark_as_linear(fragment)
                        .map_err(|_| TypeError::NonLinearType(ty.clone()))?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct TypeScope<'a> {
    variables: HashMap<&'a str, ValueType>,
    functions: HashMap<&'a str, FnType>,
}

impl<'a> TypeScope<'a> {
    pub(crate) fn functions(&self) -> &HashMap<&'a str, FnType> {
        &self.functions
    }
}

/// Context for deriving type information.
pub struct TypeContext<'a, 'ctx, G: Group> {
    count: usize,
    outer: &'ctx Context<'a, G>,
    scopes: Vec<TypeScope<'a>>,
}

impl<G: Group> fmt::Debug for TypeContext<'_, '_, G> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter
            .debug_struct("TypeContext")
            .field("count", &self.count)
            .field("scopes", &self.scopes)
            .finish()
    }
}

#[derive(Debug, Clone)]
struct TypeEquation {
    lhs: ValueType,
    rhs: ValueType,
}

impl<'a, 'ctx, G: Group> TypeContext<'a, 'ctx, G> {
    /// Creates a type context based on the interpreter context.
    pub fn new(context: &'ctx Context<'a, G>) -> Self {
        TypeContext {
            count: 0,
            outer: context,
            scopes: vec![TypeScope::default()],
        }
    }

    /// Gets type of the specified variable.
    pub fn get_var_type(&self, name: &str) -> Option<ValueType> {
        self.scopes
            .iter()
            .rev()
            .flat_map(|scope| scope.variables.get(name).cloned())
            .next()
            .or_else(|| self.outer.get_var(name).map(Value::ty))
    }

    /// Gets type of the specified function.
    pub fn get_fn_type(&self, name: &str) -> Option<&FnType> {
        self.scopes
            .iter()
            .rev()
            .flat_map(|scope| scope.functions.get(name))
            .next()
            .or_else(|| self.outer.get_fn(name).map(Function::ty))
    }

    /// Returns the innermost variable scope.
    pub fn innermost_scope(&self) -> &TypeScope<'a> {
        self.scopes.last().unwrap()
    }

    fn process_expr_inner(
        &mut self,
        substitutions: &mut Substitutions,
        expr: &SpannedExpr<'a>,
    ) -> Result<ValueType, Spanned<'a, TypeError>> {
        use self::Expr::*;

        match expr.extra {
            Variable => self.get_var_type(expr.fragment).ok_or_else(|| {
                create_span_ref(expr, TypeError::UndefinedVar(expr.fragment.to_owned()))
            }),

            Number => Ok(ValueType::Scalar),
            Literal { ty, .. } => Ok(match ty {
                LiteralType::Buffer => ValueType::Buffer,
                LiteralType::Scalar => ValueType::Scalar,
                LiteralType::Element => ValueType::Element,
            }),

            Tuple(ref terms) => {
                let term_types: Result<Vec<_>, _> = terms
                    .iter()
                    .map(|term| self.process_expr_inner(substitutions, term))
                    .collect();
                term_types.map(ValueType::Tuple)
            }

            Function { ref args, name } => {
                let fn_name = &name.fragment[1..];
                let fn_ty = self
                    .get_fn_type(fn_name)
                    .ok_or_else(|| {
                        create_span_ref(&name, TypeError::UndefinedFn(fn_name.to_owned()))
                    })?
                    .clone();

                if let FnArgs::List(ref arg_types) = fn_ty.args {
                    let args_len = args.len();
                    if arg_types.len() != args_len {
                        let e = create_span_ref(
                            expr,
                            TypeError::ArgLenMismatch {
                                expected: arg_types.len(),
                                actual: args_len,
                            },
                        );
                        return Err(e);
                    }
                }

                let actual_types: Result<Vec<_>, _> = args
                    .iter()
                    .map(|arg| self.process_expr_inner(substitutions, arg))
                    .collect();
                let actual_types = actual_types?;

                if let FnArgs::List(ref arg_types) = fn_ty.args {
                    for (i, (arg, arg_ty)) in actual_types.iter().zip(arg_types).enumerate() {
                        let rhs = self.instantiate_type(&arg_ty);
                        substitutions
                            .unify(arg, &rhs)
                            .map_err(|e| create_span_ref(&args[i], e))?;
                    }
                }
                let return_type = self.instantiate_type(&fn_ty.return_type);

                // Copy constraints on the newly generated type vars from the function definition.
                for i in 0..fn_ty.type_count {
                    if fn_ty.is_linear(i) {
                        substitutions
                            .mark_as_linear(&ValueType::TypeVar(self.count + i))
                            .map_err(|e| create_span_ref(&args[i], e))?;
                    }
                }

                self.count += fn_ty.type_count;
                Ok(return_type)
            }

            Block(ref statements) => {
                self.scopes.push(TypeScope::default());
                let mut return_type = ValueType::Void;
                for (i, statement) in statements.iter().enumerate() {
                    let ty = self.process_statement(substitutions, statement)?;
                    if i == statements.len() - 1 {
                        return_type = ty;
                    }
                }
                // TODO: do we need to pop a scope on error?
                self.scopes.pop();
                // The type returned by the block is equal to the type of the last statement.
                Ok(return_type)
            }

            Unary { op, ref inner } => match op.extra {
                UnaryOp::Not => {
                    let inner_type = self.process_expr_inner(substitutions, inner)?;
                    substitutions
                        .unify(&inner_type, &ValueType::Bool)
                        .map_err(|e| create_span_ref(expr, e))?;
                    Ok(ValueType::Bool)
                }
                UnaryOp::Neg => self.process_expr_inner(substitutions, inner),
            },

            Binary {
                ref lhs,
                ref rhs,
                op,
            } => {
                let lhs_ty = self.process_expr_inner(substitutions, lhs)?;
                let rhs_ty = self.process_expr_inner(substitutions, rhs)?;

                match op.extra {
                    BinaryOp::Add | BinaryOp::Sub => {
                        substitutions
                            .unify(&lhs_ty, &rhs_ty)
                            .and_then(|()| substitutions.mark_as_linear(&lhs_ty))
                            .map_err(|e| create_span_ref(expr, e))?;
                        Ok(rhs_ty)
                    }

                    BinaryOp::Mul => {
                        substitutions
                            .unify(&lhs_ty, &ValueType::Scalar)
                            .and_then(|()| substitutions.mark_as_linear(&rhs_ty))
                            .map_err(|e| create_span_ref(expr, e))?;
                        Ok(rhs_ty)
                    }

                    BinaryOp::Div => {
                        substitutions
                            .unify(&rhs_ty, &ValueType::Scalar)
                            .and_then(|()| substitutions.mark_as_linear(&lhs_ty))
                            .map_err(|e| create_span_ref(expr, e))?;
                        Ok(lhs_ty)
                    }

                    BinaryOp::Power => {
                        substitutions
                            .unify(&lhs_ty, &ValueType::Scalar)
                            .and_then(|()| substitutions.unify(&rhs_ty, &ValueType::Element))
                            .map_err(|e| create_span_ref(expr, e))?;
                        Ok(rhs_ty)
                    }

                    BinaryOp::Eq | BinaryOp::NotEq => {
                        substitutions
                            .unify(&lhs_ty, &rhs_ty)
                            .map_err(|e| create_span_ref(expr, e))?;
                        Ok(ValueType::Bool)
                    }

                    BinaryOp::And | BinaryOp::Or => {
                        substitutions
                            .unify(&lhs_ty, &ValueType::Bool)
                            .map_err(|e| create_span_ref(expr, e))?;
                        substitutions
                            .unify(&rhs_ty, &ValueType::Bool)
                            .map_err(|e| create_span_ref(expr, e))?;
                        Ok(ValueType::Bool)
                    }
                }
            }
        }
    }

    /// Processes an isolated expression.
    pub fn process_expr(
        &mut self,
        expr: &SpannedExpr<'a>,
    ) -> Result<ValueType, Spanned<'a, TypeError>> {
        let mut substitutions = Substitutions::default();
        self.process_expr_inner(&mut substitutions, expr)
    }

    fn assign_new_type(&mut self, ty: &mut ValueType) {
        if let ValueType::Any = ty {
            *ty = ValueType::TypeVar(self.count);
            self.count += 1;
        } else if let ValueType::Tuple(ref mut fragments) = ty {
            for fragment in fragments {
                self.assign_new_type(fragment);
            }
        }
    }

    /// Instantiates a type from a function definition.
    ///
    /// This function assumes that `TypeVar`s in the definition are well-formed, i.e.,
    /// counted from zero without spaces.
    fn instantiate_type(&mut self, ty: &ValueType) -> ValueType {
        if let ValueType::TypeVar(idx) = ty {
            ValueType::TypeVar(self.count + *idx)
        } else if let ValueType::Tuple(ref fragments) = ty {
            ValueType::Tuple(
                fragments
                    .iter()
                    .map(|frag| self.instantiate_type(frag))
                    .collect(),
            )
        } else {
            ty.clone()
        }
    }

    fn process_lvalue(
        &mut self,
        substitutions: &mut Substitutions,
        lvalue: &SpannedLvalue<'a>,
    ) -> ValueType {
        match lvalue.extra {
            Lvalue::Variable { ref ty } => {
                let mut value_type = if let Some(ty) = ty {
                    // `ty` may contain `Any` elements, so we need to replace them with type vars.
                    ty.extra.clone()
                } else {
                    ValueType::Any
                };
                self.assign_new_type(&mut value_type);

                self.scopes
                    .last_mut()
                    .unwrap()
                    .variables
                    .insert(lvalue.fragment, value_type.clone());
                value_type
            }

            Lvalue::Tuple(ref fragments) => ValueType::Tuple(
                fragments
                    .iter()
                    .map(|fragment| self.process_lvalue(substitutions, fragment))
                    .collect(),
            ),
        }
    }

    fn process_fn_def(
        &mut self,
        substitutions: &mut Substitutions,
        def: &FnDefinition<'a>,
    ) -> Result<(), Spanned<'a, TypeError>> {
        self.scopes.push(TypeScope::default());
        let arg_types: Vec<_> = def
            .args
            .iter()
            .map(|arg| self.process_lvalue(substitutions, arg))
            .collect();

        let mut return_type = ValueType::Void;
        for (i, statement) in def.body.iter().enumerate() {
            let ty = self.process_statement(substitutions, statement)?;
            if i == def.body.len() - 1 {
                return_type = ty;
            }
        }
        // TODO: do we need to pop a scope on error?
        self.scopes.pop();

        let arg_types = arg_types
            .iter()
            .map(|arg| substitutions.resolve(arg))
            .collect();
        let return_type = substitutions.resolve(&return_type);
        let fn_ty = FnType::new(arg_types, return_type, &substitutions.lin);
        self.scopes
            .last_mut()
            .unwrap()
            .functions
            .insert(def.name.fragment, fn_ty);
        Ok(())
    }

    fn process_statement(
        &mut self,
        substitutions: &mut Substitutions,
        statement: &SpannedStatement<'a>,
    ) -> Result<ValueType, Spanned<'a, TypeError>> {
        use self::Statement::*;
        match statement.extra {
            Empty => Ok(ValueType::Void),
            Expr(ref expr) => self.process_expr_inner(substitutions, expr),

            Assignment { ref lhs, ref rhs } => {
                let rhs_ty = self.process_expr_inner(substitutions, rhs)?;
                let lhs_ty = self.process_lvalue(substitutions, lhs);
                substitutions
                    .unify(&lhs_ty, &rhs_ty)
                    .map(|()| ValueType::Void)
                    .map_err(|e| create_span_ref(statement, e))
            }

            Fn(ref def) => self
                .process_fn_def(substitutions, def)
                .map(|()| ValueType::Void),
        }
    }

    /// Processes statements. After processing, the context will contain type info
    /// about newly declared vars / functions.
    pub fn process_statements(
        &mut self,
        statements: &[SpannedStatement<'a>],
    ) -> Result<(), Spanned<'a, TypeError>> {
        let mut substitutions = Substitutions::default();
        for statement in statements {
            self.process_statement(&mut substitutions, statement)?;
        }

        let scope = self.scopes.last_mut().unwrap();
        for var_type in scope.variables.values_mut() {
            *var_type = substitutions.resolve(var_type);
        }
        // Function types are processed on creation, so we don't need to post-process them here.

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        functions::{FromSha512, Rand},
        parser::Span,
        Ed25519,
    };
    use assert_matches::assert_matches;
    use rand::thread_rng;

    fn create_context(_: &str) -> Context<Ed25519> {
        let mut context = Context::new(Ed25519);
        context
            .innermost_scope()
            .insert_var("G", Value::Element(Ed25519.base_element()))
            .insert_var("true", Value::Bool(true))
            .insert_var("false", Value::Bool(false))
            .insert_native_fn("rand", Rand::new(thread_rng()))
            .insert_native_fn("sha512", FromSha512);
        context
    }

    #[test]
    fn statements_with_a_block() {
        let code = "y = { x = 3; 2*x }; [y]x == 6 * x;\0";
        let statements = Statement::parse_list(Span::new(code)).unwrap();
        let mut context = Context::new(Ed25519);
        context
            .innermost_scope()
            .insert_var("x", Value::Element(Ed25519.base_element()));

        let mut types = TypeContext::new(&context);
        types.process_statements(&statements).unwrap();
        assert_eq!(types.get_var_type("y").unwrap(), ValueType::Scalar);
    }

    #[test]
    fn boolean_statements() {
        let code = "y = x == [2]x; y = y || { x = 3; x != 7 };\0";
        let statements = Statement::parse_list(Span::new(code)).unwrap();
        let mut context = Context::new(Ed25519);
        context
            .innermost_scope()
            .insert_var("x", Value::Element(Ed25519.base_element()));

        let mut types = TypeContext::new(&context);
        types.process_statements(&statements).unwrap();
        assert_eq!(types.get_var_type("y").unwrap(), ValueType::Bool);
    }

    #[test]
    fn function_def() {
        let mut code = r#"
        fn sign(x, msg) {
            (r, R) = :rand() * (1, G);
            c = :sha512(R, msg);
            (R, r + c * x)
        }
        "#
        .to_owned();
        code.push('\0');

        let statements = Statement::parse_list(Span::new(&code)).unwrap();
        let context = create_context(&code);
        let mut types = TypeContext::new(&context);
        types.process_statements(&statements).unwrap();
        assert_eq!(
            types.get_fn_type("sign").unwrap().to_string(),
            "fn<T: ?Lin>(Sc, T) -> (Ge, Sc)"
        );
    }

    #[test]
    fn non_linear_types_in_function() {
        let mut code = r#"
        fn compare(x, y) {
            x == y
        }
        fn compare_hash(x, z) {
            x == [:sha512(z)]G
        }
        fn add_hashes(x, y) {
            :sha512(x, y) + :sha512(y, x)
        }
        "#
        .to_owned();
        code.push('\0');

        let statements = Statement::parse_list(Span::new(&code)).unwrap();
        let context = create_context(&code);
        let mut types = TypeContext::new(&context);
        types.process_statements(&statements).unwrap();
        assert_eq!(
            types.get_fn_type("compare").unwrap().to_string(),
            "fn<T: ?Lin>(T, T) -> bool"
        );
        assert_eq!(
            types.get_fn_type("compare_hash").unwrap().to_string(),
            "fn<T: ?Lin>(Ge, T) -> bool"
        );
        assert_eq!(
            types.get_fn_type("add_hashes").unwrap().to_string(),
            "fn<T: ?Lin, U: ?Lin>(T, U) -> Sc"
        );
    }

    #[test]
    fn type_hints_in_block() {
        let mut code = r#"
        fn hinted(x, (_, Z)) {
            (r: Sc, R) = :rand() * x;
            sum: Ge = R + Z;
            sum / r
        }
        "#
        .to_owned();
        code.push('\0');

        let statements = Statement::parse_list(Span::new(&code)).unwrap();
        let context = create_context(&code);
        let mut types = TypeContext::new(&context);
        types.process_statements(&statements).unwrap();
        assert_eq!(
            types.get_fn_type("hinted").unwrap().to_string(),
            "fn<T: ?Lin>((Sc, Ge), (T, Ge)) -> Ge"
        );
    }

    #[test]
    fn type_recursion() {
        let code = "fn bog(x) { x + (x, G) }\0";
        let statements = Statement::parse_list(Span::new(code)).unwrap();
        let context = create_context(code);
        let mut types = TypeContext::new(&context);
        let err = types.process_statements(&statements).unwrap_err();
        assert_eq!(err.fragment, "x + (x, G)");
        assert_matches!(err.extra, TypeError::RecursiveType(ref ty) if ty.to_string() == "(T, Ge)");

        let mut code = r#"
            fn add(x, y) { x + y } # this function is fine
            fn bog(x) { :add(x, (1, x)) } # ...but its application is not
        "#
        .to_owned();
        code.push('\0');

        let statements = Statement::parse_list(Span::new(&code)).unwrap();
        let mut types = TypeContext::new(&context);
        let err = types.process_statements(&statements).unwrap_err();
        assert_matches!(err.extra, TypeError::RecursiveType(ref ty) if ty.to_string() == "(Sc, T)");
    }

    #[test]
    fn type_hint_resulting_in_error() {
        let mut code = r#"
        fn bog(x, y: Sc) {
            [x]G + y
        }
        "#
        .to_owned();
        code.push('\0');

        let statements = Statement::parse_list(Span::new(&code)).unwrap();
        let context = create_context(&code);
        let mut types = TypeContext::new(&context);
        let err = types.process_statements(&statements).unwrap_err();
        assert_eq!(err.fragment, "[x]G + y");
        assert_matches!(
            err.extra,
            TypeError::IncompatibleTypes(ref t1, ref t2)
                if *t1 == ValueType::Element && *t2 == ValueType::Scalar
        );
    }

    #[test]
    fn function_with_arg_type_hint() {
        let mut code = r#"
        fn sign(x, msg: Bytes) {
            (r, R) = :rand() * (1, G);
            c = :sha512(R, msg);
            (R, r + c * x)
        }

        fn tuple_fn(x: (_, Sc), y) {
            (z0, z1) = x + y;
            (z0 - z1) * G
        }
        "#
        .to_owned();
        code.push('\0');

        let statements = Statement::parse_list(Span::new(&code)).unwrap();
        let context = create_context(&code);
        let mut types = TypeContext::new(&context);
        types.process_statements(&statements).unwrap();
        assert_eq!(
            types.get_fn_type("sign").unwrap().to_string(),
            "fn(Sc, Bytes) -> (Ge, Sc)"
        );
        assert_eq!(
            types.get_fn_type("tuple_fn").unwrap().to_string(),
            "fn((Sc, Sc), (Sc, Sc)) -> Ge"
        );
    }

    #[test]
    fn linear_marking() {
        let code = "fn add(x, y) { (x == y, x + y) }\0";
        let statements = Statement::parse_list(Span::new(&code)).unwrap();
        let context = create_context(&code);
        let mut types = TypeContext::new(&context);
        types.process_statements(&statements).unwrap();
        let ty = types.get_fn_type("add").unwrap();
        assert_eq!(ty.to_string(), "fn<T>(T, T) -> (bool, T)");

        let code = "fn add(x, y) { (x == y, x + y) } :add(true, false);\0";
        let statements = Statement::parse_list(Span::new(&code)).unwrap();
        let mut types = TypeContext::new(&context);
        let err = types.process_statements(&statements).unwrap_err();
        assert_matches!(err.extra, TypeError::NonLinearType(ValueType::Bool));

        let mut code = r#"
            fn add(x, y) {
                (x == y, x + y)
            }
            fn bog(x) {
                flag = x == 1;
                :add(flag, !flag)
            }
        "#
        .to_owned();
        code.push('\0');
        let statements = Statement::parse_list(Span::new(&code)).unwrap();
        let mut types = TypeContext::new(&context);
        let err = types.process_statements(&statements).unwrap_err();
        assert_matches!(err.extra, TypeError::NonLinearType(ValueType::Bool));
    }

    #[test]
    fn function_dependencies() {
        let mut code = r#"
        fn add(x, y) { x + y }
        :add(1, 2); # check that the calls work with different types
        :add((1, G), 3 * (5, G));

        fn add2(x) { :add(x, 2) }
        "#
        .to_owned();
        code.push('\0');

        let statements = Statement::parse_list(Span::new(&code)).unwrap();
        let context = create_context(&code);
        let mut types = TypeContext::new(&context);
        types.process_statements(&statements).unwrap();
        assert_eq!(
            types.get_fn_type("add").unwrap().to_string(),
            "fn<T>(T, T) -> T"
        );
        assert_eq!(
            types.get_fn_type("add2").unwrap().to_string(),
            "fn(Sc) -> Sc"
        );
    }
}
