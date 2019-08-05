//! Parsing logic for finite-group arithmetic.

use nom::{
    branch::alt,
    bytes::{complete::{tag, take_while, take_while1, take_while_m_n}, streaming},
    character::complete::char as tag_char,
    combinator::{cut, map, map_res, opt, peek, recognize},
    error::{context, ErrorKind},
    multi::{fold_many1, many0, separated_list},
    sequence::{delimited, preceded, terminated, tuple},
    Err as NomErr,
};
use nom_locate::{LocatedSpan, LocatedSpanEx};
use std::{fmt, mem};

use crate::interpreter::{Typed, ValueType};

#[cfg(test)]
mod tests;

/// Code span.
pub type Span<'a> = LocatedSpan<&'a str>;
/// Value with an associated code span.
pub type Spanned<'a, T> = LocatedSpanEx<&'a str, T>;
type NomResult<'a, T> = nom::IResult<Span<'a>, T, SpannedError<'a>>;

pub(crate) fn map_span<T, U>(span: Spanned<T>, extra: U) -> Spanned<U> {
    Spanned {
        offset: span.offset,
        line: span.line,
        fragment: span.fragment,
        extra,
    }
}

pub(crate) fn map_span_ref<'a, T, U>(span: &Spanned<'a, T>, extra: U) -> Spanned<'a, U> {
    Spanned {
        offset: span.offset,
        line: span.line,
        fragment: span.fragment,
        extra,
    }
}

fn unite_spans<'a, T, U>(input: Span<'a>, start: &Spanned<T>, end: &Spanned<U>) -> Span<'a> {
    debug_assert!(input.offset <= start.offset);
    debug_assert!(start.offset <= end.offset);
    debug_assert!(input.offset + input.fragment.len() >= end.offset + end.fragment.len());

    let start_idx = start.offset - input.offset;
    let end_idx = end.offset + end.fragment.len() - input.offset;
    Span {
        offset: start.offset,
        line: start.line,
        fragment: &input.fragment[start_idx..end_idx],
        extra: (),
    }
}

/// Parsing context.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Context {
    /// Variable name.
    Var,
    /// Function invocation.
    Fun,
    /// Arithmetic expression.
    Expr,
}

impl fmt::Display for Context {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Context::Var => formatter.write_str("variable"),
            Context::Fun => formatter.write_str("function call"),
            Context::Expr => formatter.write_str("arithmetic expression"),
        }
    }
}

impl Context {
    fn new(s: &str) -> Self {
        use self::Context::*;
        match s {
            "var" => Var,
            "fn" => Fun,
            "expr" => Expr,
            _ => unreachable!(),
        }
    }

    fn to_str(self) -> &'static str {
        use self::Context::*;
        match self {
            Var => "var",
            Fun => "fn",
            Expr => "expr",
        }
    }
}

/// Parsing error.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Error<'a> {
    /// Input is not in ASCII.
    NonAsciiInput,

    /// No rules where expecting this character.
    UnexpectedChar {
        /// Parsing context.
        context: Option<Spanned<'a, Context>>,
    },

    /// Unexpected expression end.
    UnexpectedTerm {
        /// Parsing context.
        context: Option<Spanned<'a, Context>>,
    },

    /// Hex decoding error.
    Hex(hex::FromHexError),
    /// Leftover symbols after parsing.
    Leftovers,
    /// Input is incomplete.
    Incomplete,

    /// Other parsing error.
    Other {
        /// `nom`-defined error kind.
        kind: ErrorKind,
        /// Parsing context.
        context: Option<Spanned<'a, Context>>,
    },
}

impl fmt::Display for Error<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::NonAsciiInput => formatter.write_str("Non-ASCII inputs are not supported"),

            Error::UnexpectedChar { context: Some(ctx) } => {
                write!(formatter, "Unexpected character in {}", ctx.extra)
            }
            Error::UnexpectedChar { .. } => formatter.write_str("Unexpected character"),

            Error::UnexpectedTerm { context: Some(ctx) } => {
                write!(formatter, "Unfinished {}", ctx.extra)
            }
            Error::UnexpectedTerm { .. } => formatter.write_str("Unfinished expression"),
            Error::Hex(e) => write!(formatter, "Error decoding from hex: {}", e),
            Error::Leftovers => formatter.write_str("Uninterpreted characters after parsing"),
            Error::Incomplete => formatter.write_str("Incomplete input"),
            Error::Other { .. } => write!(formatter, "Cannot parse sequence"),
        }
    }
}

impl<'a> Error<'a> {
    fn accepts_context(&self) -> bool {
        match self {
            Error::UnexpectedChar { context }
            | Error::UnexpectedTerm { context }
            | Error::Other { context, .. } => context.is_none(),
            _ => false,
        }
    }

    /// Returns optional error context.
    pub fn context(&self) -> Option<Spanned<Context>> {
        match self {
            Error::UnexpectedChar { context }
            | Error::UnexpectedTerm { context }
            | Error::Other { context, .. } => context.to_owned(),
            _ => None,
        }
    }

    fn set_context(&mut self, ctx: Context, span: Span<'a>) {
        match self {
            Error::UnexpectedChar { context }
            | Error::UnexpectedTerm { context }
            | Error::Other { context, .. } => {
                *context = Some(map_span(span, ctx));
            }
            _ => { /* do nothing */ }
        }
    }

    fn with_span<T>(self, span: Spanned<'a, T>) -> SpannedError<'a> {
        SpannedError(map_span(span, self))
    }
}

/// Parsing error with the associated code span.
#[derive(Debug)]
pub struct SpannedError<'a>(Spanned<'a, Error<'a>>);

impl<'a> nom::error::ParseError<Span<'a>> for SpannedError<'a> {
    fn from_error_kind(mut input: Span<'a>, kind: ErrorKind) -> Self {
        if kind == ErrorKind::Char && !input.fragment.is_empty() {
            // Truncate the error span to the first ineligible char.
            input.fragment = &input.fragment[..1];
        }

        SpannedError(map_span(
            input,
            if kind == ErrorKind::Char {
                if input.fragment.is_empty() {
                    Error::UnexpectedTerm { context: None }
                } else {
                    Error::UnexpectedChar { context: None }
                }
            } else {
                Error::Other {
                    kind,
                    context: None,
                }
            },
        ))
    }

    fn append(_: Span<'a>, _: ErrorKind, other: Self) -> Self {
        other
    }

    #[rustfmt::skip]
    fn add_context(input: Span<'a>, ctx: &'static str, mut other: Self) -> Self {
        if other.0.extra.accepts_context() && input.offset < other.0.offset {
            other.0.extra.set_context(Context::new(ctx), input);
        }
        other
    }
}

/// Whitespace and `#...` comments.
fn ws(input: Span) -> NomResult<Span> {
    fn narrow_ws(input: Span) -> NomResult<Span> {
        streaming::take_while1(|c: char| c.is_ascii_whitespace())(input)
    }

    let comment = preceded(tag_char('#'), take_while(|c: char| c != '\n'));
    let ws_line = alt((narrow_ws, comment));
    recognize(many0(ws_line))(input)
}

/// Hex-encoded buffer like `0x09abcd`.
fn hex_buffer(input: Span) -> NomResult<SpannedExpr> {
    let hex_parser = preceded(
        tag("0x"),
        cut(tuple((
            opt(alt((
                map(tag_char('s'), |_| LiteralType::Scalar),
                map(tag_char('S'), |_| LiteralType::Scalar),
                map(tag_char('g'), |_| LiteralType::Element),
                map(tag_char('G'), |_| LiteralType::Element),
            ))),
            fold_many1(
                map_res(
                    preceded(
                        opt(tag_char('_')),
                        take_while1(|c: char| c.is_ascii_hexdigit()),
                    ),
                    |digits: Span| {
                        hex::decode(digits.fragment).map_err(|e| Error::Hex(e).with_span(digits))
                    },
                ),
                vec![],
                |mut acc, digits| {
                    acc.extend_from_slice(&digits);
                    acc
                },
            ),
        ))),
    );

    with_span(map(hex_parser, |(maybe_ty, value)| {
        Typed::from_literal(Expr::Literal {
            ty: maybe_ty.unwrap_or(LiteralType::Buffer),
            value,
        })
    }))(input)
}

/// Variable name, like `a_foo` or `Bar`.
fn var_name(input: Span) -> NomResult<Span> {
    context(
        Context::Var.to_str(),
        preceded(
            peek(take_while_m_n(1, 1, |c: char| {
                c.is_ascii_alphabetic() || c == '_'
            })),
            take_while1(|c: char| c.is_ascii_alphanumeric() || c == '_'),
        ),
    )(input)
}

/// Function arguments, e.g., `(a, B + 1, 0x56)`
fn fun_args(input: Span) -> NomResult<Vec<SpannedExpr>> {
    delimited(
        terminated(tag_char('('), ws),
        separated_list(delimited(ws, tag_char(','), ws), expr),
        preceded(ws, tag_char(')')),
    )(input)
}

/// Wrapper around parsers allowing to capture both their output and the relevant span.
fn with_span<'a, O>(
    parser: impl Fn(Span<'a>) -> NomResult<'a, O>,
) -> impl Fn(Span<'a>) -> NomResult<'a, Spanned<O>> {
    move |input: Span| {
        parser(input).map(|(rem, output)| {
            let spanned = Spanned {
                offset: input.offset,
                line: input.line,
                extra: output,
                fragment: &input.fragment[..(rem.offset - input.offset)],
            };
            (rem, spanned)
        })
    }
}

/// Function invocation, e.g., `:sc_foo(A, b, 0xc0ffee)`.
fn fun(input: Span) -> NomResult<(Span, Vec<SpannedExpr>)> {
    context(
        Context::Fun.to_str(),
        tuple((
            recognize(preceded(tag_char(':'), cut(var_name))),
            cut(preceded(ws, fun_args)),
        )),
    )(input)
}

/// Assignable value.
#[derive(Debug, Clone, PartialEq)]
pub enum Lvalue<'a> {
    /// Simple variable, e.g., `x` or `x: (Sc, Ge)`.
    Variable {
        /// Type annotation.
        ty: Option<Spanned<'a, ValueType>>,
    },
    /// Tuple destructuring, e.g., `(x, y)` or `(x: Sc, _)`.
    Tuple(Vec<SpannedLvalue<'a>>),
}

/// `Lvalue` with the associated code span.
pub type SpannedLvalue<'a> = Spanned<'a, Lvalue<'a>>;

fn type_info(input: Span) -> NomResult<ValueType> {
    alt((
        map(tag_char('_'), |_| ValueType::Any),
        map(tag("Sc"), |_| ValueType::Scalar),
        map(tag("Ge"), |_| ValueType::Element),
        map(
            delimited(
                terminated(tag_char('('), ws),
                separated_list(delimited(ws, tag_char(','), ws), type_info),
                preceded(ws, tag_char(')')),
            ),
            ValueType::Tuple,
        ),
    ))(input)
}

fn lvalue(input: Span) -> NomResult<SpannedLvalue> {
    alt((
        with_span(map(
            delimited(
                terminated(tag_char('('), ws),
                separated_list(delimited(ws, tag_char(','), ws), lvalue),
                preceded(ws, tag_char(')')),
            ),
            Lvalue::Tuple,
        )),
        map(
            tuple((
                var_name,
                opt(preceded(
                    delimited(ws, tag_char(':'), ws),
                    cut(with_span(type_info)),
                )),
            )),
            |(name, ty)| map_span(name, Lvalue::Variable { ty }),
        ),
    ))(input)
}

/// Type of a hex literal.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LiteralType {
    /// Literal is a generic buffer.
    Buffer,
    /// Literal is a group scalar.
    Scalar,
    /// Literal is a group element.
    Element,
}

/// Arithmetic expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr<'a> {
    /// Variable use, e.g., `x`.
    Variable,
    /// Number, e.g., `42`.
    Number,

    /// Hex literal, e.g., `0x_1234`.
    Literal {
        /// Parsed value of the literal.
        value: Vec<u8>,
        /// Type of the literal.
        ty: LiteralType,
    },

    /// Function call, e.g., `:foo(x, y)`.
    Function {
        /// Function name.
        name: Span<'a>,
        /// Function arguments.
        args: Vec<SpannedExpr<'a>>,
    },

    /// Binary operation, e.g., `x + 1`.
    Binary {
        /// LHS of the operation.
        lhs: Box<SpannedExpr<'a>>,
        /// Operator.
        op: Spanned<'a, BinaryOp>,
        /// RHS of the operation.
        rhs: Box<SpannedExpr<'a>>,
    },

    /// Tuple expression, e.g., `(x, y + z)`.
    Tuple(Vec<SpannedExpr<'a>>),

    /// Block expression, e.g., `{ x = 3; x + y }`.
    Block(Vec<SpannedStatement<'a>>),
}

/// `Expr` with the associated type and code span.
pub type SpannedExpr<'a> = Spanned<'a, Typed<Expr<'a>>>;

impl Expr<'_> {
    /// Parses expression from a string.
    pub(crate) fn parse(input: &str) -> Result<SpannedExpr, Spanned<Error>> {
        let input_span = Span::new(input);
        match expr(input_span) {
            Ok((remaining, output)) => {
                if remaining.fragment.is_empty() || remaining.fragment == "\0" {
                    Ok(output)
                } else {
                    Err(Error::Leftovers.with_span(remaining).0)
                }
            }
            Err(NomErr::Error(e)) | Err(NomErr::Failure(e)) => Err(e.0),
            Err(NomErr::Incomplete(_)) => Err(Error::Incomplete.with_span(input_span).0),
        }
    }
}

/// Binary arithmetic operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    /// Addition (`+`).
    Add,
    /// Subtraction (`-`).
    Sub,
    /// Multiplication (`*`).
    Mul,
    /// Division (`/`).
    Div,
    /// Power (`[x]Y`).
    Power,
}

impl BinaryOp {
    fn from_span(span: Span) -> Spanned<Self> {
        Spanned {
            offset: span.offset,
            line: span.line,
            fragment: span.fragment,
            extra: match span.fragment {
                "+" => BinaryOp::Add,
                "-" => BinaryOp::Sub,
                "*" => BinaryOp::Mul,
                "/" => BinaryOp::Div,
                "]" => BinaryOp::Power,
                _ => unreachable!(),
            },
        }
    }
}

fn power_expr(input: Span) -> NomResult<SpannedExpr> {
    with_span(map(
        tuple((
            preceded(
                terminated(tag_char('['), ws),
                cut(tuple((expr, preceded(ws, tag("]"))))),
            ),
            preceded(ws, simple_expr),
        )),
        |((exponent, op), power)| {
            Typed::any(Expr::Binary {
                lhs: Box::new(exponent),
                rhs: Box::new(power),
                op: BinaryOp::from_span(op),
            })
        },
    ))(input)
}

fn paren_expr(input: Span) -> NomResult<SpannedExpr> {
    with_span(delimited(
        terminated(tag_char('('), ws),
        cut(separated_list(delimited(ws, tag_char(','), ws), expr)),
        preceded(ws, tag_char(')')),
    ))(input)
    .and_then(|(rest, mut parsed)| match parsed.extra.len() {
        0 => Err(NomErr::Failure(
            Error::UnexpectedChar { context: None }.with_span(parsed),
        )),
        1 => Ok((rest, parsed.extra.pop().unwrap())),
        _ => {
            let terms = mem::replace(&mut parsed.extra, vec![]);
            Ok((
                rest,
                map_span_ref(&parsed, Typed::tuple(terms.len(), Expr::Tuple(terms))),
            ))
        }
    })
}

fn simple_expr(input: Span) -> NomResult<SpannedExpr> {
    alt((
        map(var_name, |span| map_span(span, Typed::any(Expr::Variable))),
        hex_buffer,
        map(take_while1(|c: char| c.is_ascii_digit()), |span| {
            map_span(span, Typed::scalar(Expr::Number))
        }),
        map(with_span(fun), |mut spanned| {
            let name = spanned.extra.0;
            let args = mem::replace(&mut spanned.extra.1, vec![]);
            map_span(spanned, Typed::any(Expr::Function { name, args }))
        }),
        paren_expr,
        power_expr,
        map(with_span(block), |mut spanned| {
            let statements = mem::replace(&mut spanned.extra, vec![]);
            map_span(spanned, Typed::any(Expr::Block(statements)))
        }),
    ))(input)
}

fn high_priority_expr(input: Span) -> NomResult<SpannedExpr> {
    let high_priority_parser = tuple((
        simple_expr,
        many0(tuple((
            delimited(ws, alt((tag("*"), tag("/"))), ws),
            simple_expr,
        ))),
    ));
    let high_priority_parser = map(high_priority_parser, |(first, rest)| {
        rest.into_iter().fold(first, |acc, (op, expr)| {
            map_span(
                unite_spans(input, &acc, &expr),
                Typed::any(Expr::Binary {
                    lhs: Box::new(acc),
                    op: BinaryOp::from_span(op),
                    rhs: Box::new(expr),
                }),
            )
        })
    });

    alt((high_priority_parser, simple_expr))(input)
}

fn expr(input: Span) -> NomResult<SpannedExpr> {
    let low_priority_parser = tuple((
        high_priority_expr,
        many0(tuple((
            delimited(ws, alt((tag("+"), tag("-"))), ws),
            high_priority_expr,
        ))),
    ));
    let low_priority_parser = map(low_priority_parser, |(first, rest)| {
        rest.into_iter().fold(first, |acc, (op, expr)| {
            map_span(
                unite_spans(input, &acc, &expr),
                Typed::any(Expr::Binary {
                    lhs: Box::new(acc),
                    op: BinaryOp::from_span(op),
                    rhs: Box::new(expr),
                }),
            )
        })
    });

    context(
        Context::Expr.to_str(),
        alt((low_priority_parser, high_priority_expr, simple_expr)),
    )(input)
}

/// Statement.
#[derive(Debug, Clone, PartialEq)]
pub enum Statement<'a> {
    /// Empty statement.
    Empty,
    /// Expression, e.g., `x + (1, 2)`.
    Expr(SpannedExpr<'a>),
    /// Function definition, e.g., `fn foo(x) { x + 1 }`.
    Fn(FnDefinition<'a>),

    /// Assigment, e.g., `(x, y) = (5, 8)`.
    Assignment {
        /// LHS of the assignment.
        lhs: SpannedLvalue<'a>,
        /// RHS of the assignment.
        rhs: SpannedExpr<'a>,
    },

    /// Comparison between 2 expressions, e.g., `[x]G ?= [y]K`.
    Comparison {
        /// LHS of the comparison.
        lhs: SpannedExpr<'a>,
        /// RHS of the comparison.
        rhs: SpannedExpr<'a>,
        /// Equality operator.
        eq_sign: Span<'a>,
    },
}

/// Statement with the associated code span.
pub type SpannedStatement<'a> = Spanned<'a, Statement<'a>>;

impl Statement<'_> {
    /// Parses a list of statements from a string.
    pub(crate) fn list_from_str(input: &str) -> Result<Vec<SpannedStatement>, Spanned<Error>> {
        let parser = delimited(
            ws,
            tuple((
                separated_list(delimited(ws, tag_char(';'), ws), with_span(statement)),
                opt(preceded(ws, tag(";"))),
            )),
            ws,
        );
        let parser = map(parser, |(mut statements, maybe_semicolon)| {
            if let Some(semicolon) = maybe_semicolon {
                statements.push(map_span(semicolon, Statement::Empty));
            }
            statements
        });

        let input_span = Span::new(input);
        parser(input_span)
            .map_err(|e| match e {
                NomErr::Failure(e) | NomErr::Error(e) => e.0,
                NomErr::Incomplete(_) => Error::Incomplete.with_span(input_span).0,
            })
            .and_then(|(remaining, statements)| {
                if remaining.fragment.is_empty() || remaining.fragment == "\0" {
                    Ok(statements)
                } else {
                    Err(Error::Leftovers.with_span(remaining).0)
                }
            })
    }
}

fn statement(input: Span) -> NomResult<Statement> {
    let assignment_parser = tuple((opt(terminated(lvalue, delimited(ws, tag("="), ws))), expr));
    let comparison_parser = tuple((expr, delimited(ws, tag("?="), ws), cut(expr)));

    alt((
        map(fun_def, Statement::Fn),
        map(comparison_parser, |(lhs, eq_sign, rhs)| {
            Statement::Comparison { lhs, eq_sign, rhs }
        }),
        map(assignment_parser, |(lvalue, rvalue)| {
            if let Some(lvalue) = lvalue {
                Statement::Assignment {
                    lhs: lvalue,
                    rhs: rvalue,
                }
            } else {
                Statement::Expr(rvalue)
            }
        }),
    ))(input)
}

fn block(input: Span) -> NomResult<Vec<SpannedStatement>> {
    let parser = delimited(
        terminated(tag_char('{'), ws),
        tuple((
            separated_list(delimited(ws, tag_char(';'), ws), with_span(statement)),
            opt(preceded(ws, tag(";"))),
        )),
        preceded(ws, tag_char('}')),
    );
    map(parser, |(mut statements, maybe_semicolon)| {
        if let Some(semicolon) = maybe_semicolon {
            statements.push(map_span(semicolon, Statement::Empty));
        }
        statements
    })(input)
}

/// Function definition, e.g., `fn foo(x, y) { x + y }`.
#[derive(Debug, Clone, PartialEq)]
pub struct FnDefinition<'a> {
    /// Function name, e.g., `foo`.
    pub name: Span<'a>,
    /// Function arguments, e.g., `x, y`.
    pub args: Vec<SpannedLvalue<'a>>,
    /// Function body, e.g., `x + y`.
    pub body: Vec<SpannedStatement<'a>>,
}

fn fun_def(input: Span) -> NomResult<FnDefinition> {
    let parser = preceded(
        terminated(tag("fn"), ws),
        cut(tuple((
            var_name,
            delimited(
                terminated(tag_char('('), ws),
                separated_list(delimited(ws, tag_char(','), ws), lvalue),
                preceded(ws, tag_char(')')),
            ),
            preceded(ws, block),
        ))),
    );
    map(parser, |(name, args, body)| FnDefinition {
        name,
        args,
        body,
    })(input)
}
