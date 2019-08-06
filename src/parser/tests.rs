use super::*;
use assert_matches::assert_matches;

use crate::ValueType;

fn span(offset: usize, fragment: &str) -> Span {
    Span {
        offset,
        line: 1,
        fragment,
        extra: (),
    }
}

fn sp<'a>(offset: usize, fragment: &'a str, expr: Expr<'a>) -> SpannedExpr<'a> {
    let typed_expr = match expr {
        Expr::Literal { .. } => Typed::from_literal(expr),
        Expr::Number => Typed::scalar(expr),
        _ => Typed::any(expr),
    };
    map_span(span(offset, fragment), typed_expr)
}

fn lsp<'a>(offset: usize, fragment: &'a str, lvalue: Lvalue<'a>) -> SpannedLvalue<'a> {
    map_span(span(offset, fragment), lvalue)
}

#[test]
fn whitespace_can_include_comments() {
    let input = Span::new(":ge(1)");
    assert_eq!(ws(input).unwrap().0, span(0, ":ge(1)"));

    let input = Span::new("   :ge(1)");
    assert_eq!(ws(input).unwrap().0, span(3, ":ge(1)"));

    let input = Span::new("  \n:ge(1)");
    assert_eq!(
        ws(input).unwrap().0,
        Span {
            offset: 3,
            line: 2,
            fragment: ":ge(1)",
            extra: (),
        }
    );
    let input = Span::new("# Comment\n:ge(1)");
    assert_eq!(
        ws(input).unwrap().0,
        Span {
            offset: 10,
            line: 2,
            fragment: ":ge(1)",
            extra: (),
        }
    );
    let input = Span::new("#!\n:ge(1)");
    assert_eq!(
        ws(input).unwrap().0,
        Span {
            offset: 3,
            line: 2,
            fragment: ":ge(1)",
            extra: (),
        }
    );

    let input = Span::new(
        "   # This is a comment.
             \t# This is a comment, too
             this_is_not # although this *is*",
    );
    assert_eq!(
        ws(input).unwrap().0,
        Span {
            offset: 76,
            line: 3,
            fragment: "this_is_not # although this *is*",
            extra: (),
        }
    );
}

#[test]
fn hex_buffer_works() {
    let input = Span::new("0xAbcd1234 + 5");
    assert_eq!(
        hex_buffer(input).unwrap().1,
        sp(
            0,
            "0xAbcd1234",
            Expr::Literal {
                value: vec![0xab, 0xcd, 0x12, 0x34],
                ty: LiteralType::Buffer,
            }
        )
    );

    let input = Span::new("0xg_Abcd_1234 + 5");
    assert_eq!(
        hex_buffer(input).unwrap().1,
        sp(
            0,
            "0xg_Abcd_1234",
            Expr::Literal {
                value: vec![0xab, 0xcd, 0x12, 0x34],
                ty: LiteralType::Element,
            }
        )
    );

    let erroneous_inputs = ["0xAbcd1234a", "0x", "0xP12", "0x__12", "0x_s12", "0xsA_BCD"];
    for &input in &erroneous_inputs {
        let input = Span::new(input);
        assert_matches!(hex_buffer(input).unwrap_err(), NomErr::Failure(_));
    }
}

#[test]
fn var_name_works() {
    let input = Span::new("A + B");
    assert_eq!(var_name(input).unwrap().1, span(0, "A"));
    let input = Span::new("Abc_d + B");
    assert_eq!(var_name(input).unwrap().1, span(0, "Abc_d"));
    let input = Span::new("_ + 3");
    assert_eq!(var_name(input).unwrap().1, span(0, "_"));
}

#[test]
fn fun_works() {
    let input = Span::new(":ge(0x123456) + 1");
    assert_eq!(
        fun(input).unwrap().1,
        (
            span(0, ":ge"),
            vec![sp(
                4,
                "0x123456",
                Expr::Literal {
                    value: vec![0x12, 0x34, 0x56],
                    ty: LiteralType::Buffer,
                }
            )]
        )
    );

    let input = Span::new(":ge (  0x123456\t) + A");
    assert_eq!(
        fun(input).unwrap().1,
        (
            span(0, ":ge"),
            vec![sp(
                7,
                "0x123456",
                Expr::Literal {
                    value: vec![0x12, 0x34, 0x56],
                    ty: LiteralType::Buffer,
                }
            )]
        )
    );
}

#[test]
fn power_expr_works() {
    let input = Span::new("[x]G");
    assert_eq!(
        power_expr(input).unwrap().1.extra.inner,
        Expr::Binary {
            lhs: Box::new(sp(1, "x", Expr::Variable)),
            op: BinaryOp::from_span(span(2, "]")),
            rhs: Box::new(sp(3, "G", Expr::Variable)),
        }
    );

    let input = Span::new("[x]G + C");
    assert_eq!(
        power_expr(input).unwrap().1.extra.inner,
        Expr::Binary {
            lhs: Box::new(sp(1, "x", Expr::Variable)),
            op: BinaryOp::from_span(span(2, "]")),
            rhs: Box::new(sp(3, "G", Expr::Variable)),
        }
    );

    let input = Span::new("[x](G + C)");
    assert_eq!(
        power_expr(input).unwrap().1.extra.inner,
        Expr::Binary {
            lhs: Box::new(sp(1, "x", Expr::Variable)),
            op: BinaryOp::from_span(span(2, "]")),
            rhs: Box::new(sp(
                4,
                "G + C",
                Expr::Binary {
                    lhs: Box::new(sp(4, "G", Expr::Variable)),
                    op: BinaryOp::from_span(span(6, "+")),
                    rhs: Box::new(sp(8, "C", Expr::Variable)),
                },
            )),
        }
    );

    let input = Span::new("[x + :sc(5) + 3]G");
    assert_matches!(
        power_expr(input).unwrap().1.extra.inner,
        Expr::Binary {
            ref lhs,
            ref rhs,
            ..
        } if lhs.fragment == "x + :sc(5) + 3" && rhs.fragment == "G"
    );
}

#[test]
fn element_expr_works() {
    let input = Span::new("A;");
    assert_eq!(expr(input).unwrap().1, sp(0, "A", Expr::Variable));

    let input = Span::new("(:ge(0x1234));");
    assert_eq!(
        expr(input).unwrap().1.extra.inner,
        Expr::Function {
            name: span(1, ":ge"),
            args: vec![sp(
                5,
                "0x1234",
                Expr::Literal {
                    value: vec![0x12, 0x34],
                    ty: LiteralType::Buffer,
                }
            )],
        }
    );

    let input = Span::new(":ge(0x1234) + A_b;");
    assert_eq!(
        expr(input).unwrap().1.extra.inner,
        Expr::Binary {
            lhs: Box::new(sp(0, ":ge(0x1234)", {
                Expr::Function {
                    name: span(0, ":ge"),
                    args: vec![sp(
                        4,
                        "0x1234",
                        Expr::Literal {
                            value: vec![0x12, 0x34],
                            ty: LiteralType::Buffer,
                        },
                    )],
                }
            })),
            op: map_span(span(12, "+"), BinaryOp::Add),
            rhs: Box::new(sp(14, "A_b", Expr::Variable)),
        }
    );

    let input = Span::new(":ge(0x1234) + A_b - C;");
    assert_eq!(
        expr(input).unwrap().1.extra.inner,
        Expr::Binary {
            lhs: Box::new(sp(0, ":ge(0x1234) + A_b", {
                Expr::Binary {
                    lhs: Box::new(sp(
                        0,
                        ":ge(0x1234)",
                        Expr::Function {
                            name: span(0, ":ge"),
                            args: vec![sp(
                                4,
                                "0x1234",
                                Expr::Literal {
                                    value: vec![0x12, 0x34],
                                    ty: LiteralType::Buffer,
                                },
                            )],
                        },
                    )),
                    op: map_span(span(12, "+"), BinaryOp::Add),
                    rhs: Box::new(sp(14, "A_b", Expr::Variable)),
                }
            })),
            op: map_span(span(18, "-"), BinaryOp::Sub),
            rhs: Box::new(sp(20, "C", Expr::Variable)),
        }
    );

    let input = Span::new("(:ge(0x1234) + A_b) - (C + :ge(0x00) + D);");
    assert_eq!(
        expr(input).unwrap().1.extra.inner,
        Expr::Binary {
            lhs: Box::new(sp(1, ":ge(0x1234) + A_b", {
                Expr::Binary {
                    lhs: Box::new(sp(
                        1,
                        ":ge(0x1234)",
                        Expr::Function {
                            name: span(1, ":ge"),
                            args: vec![sp(
                                5,
                                "0x1234",
                                Expr::Literal {
                                    value: vec![0x12, 0x34],
                                    ty: LiteralType::Buffer,
                                },
                            )],
                        },
                    )),
                    op: BinaryOp::from_span(span(13, "+")),
                    rhs: Box::new(sp(15, "A_b", Expr::Variable)),
                }
            })),
            op: BinaryOp::from_span(span(20, "-")),
            rhs: Box::new(sp(23, "C + :ge(0x00) + D", {
                Expr::Binary {
                    lhs: Box::new(sp(
                        23,
                        "C + :ge(0x00)",
                        Expr::Binary {
                            lhs: Box::new(sp(23, "C", Expr::Variable)),
                            op: BinaryOp::from_span(span(25, "+")),
                            rhs: Box::new(sp(
                                27,
                                ":ge(0x00)",
                                Expr::Function {
                                    name: span(27, ":ge"),
                                    args: vec![sp(
                                        31,
                                        "0x00",
                                        Expr::Literal {
                                            value: vec![0],
                                            ty: LiteralType::Buffer,
                                        },
                                    )],
                                },
                            )),
                        },
                    )),
                    op: BinaryOp::from_span(span(37, "+")),
                    rhs: Box::new(sp(39, "D", Expr::Variable)),
                }
            }))
        }
    );
}

#[test]
fn expr_with_numbers_works() {
    let input = Span::new("(2 + a) * b;");
    assert_eq!(
        expr(input).unwrap().1.extra.inner,
        Expr::Binary {
            lhs: Box::new(sp(1, "2 + a", {
                Expr::Binary {
                    lhs: Box::new(sp(1, "2", Expr::Number)),
                    op: BinaryOp::from_span(span(3, "+")),
                    rhs: Box::new(sp(5, "a", Expr::Variable)),
                }
            })),
            op: BinaryOp::from_span(span(8, "*")),
            rhs: Box::new(sp(10, "b", Expr::Variable)),
        }
    );
}

#[test]
fn assignment_works() {
    let input = Span::new("x = :sc(0x1234);");
    assert_eq!(
        statement(input).unwrap().1,
        Statement::Assignment {
            lhs: lsp(0, "x", Lvalue::Variable { ty: None }),
            rhs: Box::new(sp(
                4,
                ":sc(0x1234)",
                Expr::Function {
                    name: span(4, ":sc"),
                    args: vec![sp(
                        8,
                        "0x1234",
                        Expr::Literal {
                            value: vec![0x12, 0x34],
                            ty: LiteralType::Buffer,
                        }
                    )],
                }
            ))
        }
    );

    let input = Span::new("yb = 7 * :sc(0x0001) + k;");
    assert_eq!(
        statement(input).unwrap().1,
        Statement::Assignment {
            lhs: lsp(0, "yb", Lvalue::Variable { ty: None }),
            rhs: Box::new(sp(5, "7 * :sc(0x0001) + k", {
                Expr::Binary {
                    lhs: Box::new(sp(
                        5,
                        "7 * :sc(0x0001)",
                        Expr::Binary {
                            lhs: Box::new(sp(5, "7", Expr::Number)),
                            op: BinaryOp::from_span(span(7, "*")),
                            rhs: Box::new(sp(
                                9,
                                ":sc(0x0001)",
                                Expr::Function {
                                    name: span(9, ":sc"),
                                    args: vec![sp(
                                        13,
                                        "0x0001",
                                        Expr::Literal {
                                            value: vec![0, 1],
                                            ty: LiteralType::Buffer,
                                        },
                                    )],
                                },
                            )),
                        },
                    )),
                    op: BinaryOp::from_span(span(21, "+")),
                    rhs: Box::new(sp(23, "k", Expr::Variable)),
                }
            }))
        }
    );
}

#[test]
fn comparison_works() {
    let input = Span::new("s*G ?= R + h*A;");
    assert_eq!(
        statement(input).unwrap().1,
        Statement::Comparison {
            lhs: Box::new(sp(0, "s*G", {
                Expr::Binary {
                    lhs: Box::new(sp(0, "s", Expr::Variable)),
                    op: BinaryOp::from_span(span(1, "*")),
                    rhs: Box::new(sp(2, "G", Expr::Variable)),
                }
            })),
            rhs: Box::new(sp(7, "R + h*A", {
                Expr::Binary {
                    lhs: Box::new(sp(7, "R", Expr::Variable)),
                    op: BinaryOp::from_span(span(9, "+")),
                    rhs: Box::new(sp(
                        11,
                        "h*A",
                        Expr::Binary {
                            lhs: Box::new(sp(11, "h", Expr::Variable)),
                            op: BinaryOp::from_span(span(12, "*")),
                            rhs: Box::new(sp(13, "A", Expr::Variable)),
                        },
                    )),
                }
            })),
            eq_sign: span(4, "?="),
        }
    );

    let input = Span::new("[s]G ?= R + [h]A;");
    assert_eq!(
        statement(input).unwrap().1,
        Statement::Comparison {
            lhs: Box::new(sp(
                0,
                "[s]G",
                Expr::Binary {
                    lhs: Box::new(sp(1, "s", Expr::Variable)),
                    op: BinaryOp::from_span(span(2, "]")),
                    rhs: Box::new(sp(3, "G", Expr::Variable)),
                }
            )),
            rhs: Box::new(sp(
                8,
                "R + [h]A",
                Expr::Binary {
                    lhs: Box::new(sp(8, "R", Expr::Variable)),
                    op: BinaryOp::from_span(span(10, "+")),
                    rhs: Box::new(sp(
                        12,
                        "[h]A",
                        Expr::Binary {
                            lhs: Box::new(sp(13, "h", Expr::Variable)),
                            op: BinaryOp::from_span(span(14, "]")),
                            rhs: Box::new(sp(15, "A", Expr::Variable)),
                        },
                    )),
                }
            )),
            eq_sign: span(5, "?="),
        }
    );
}

#[test]
fn tuples_are_parsed() {
    let input = Span::new("(x, y)");
    assert_eq!(
        paren_expr(input).unwrap().1.extra,
        Typed {
            inner: Expr::Tuple(vec![sp(1, "x", Expr::Variable), sp(4, "y", Expr::Variable)]),
            ty: ValueType::Tuple(vec![ValueType::Any; 2]),
        }
    );

    let input = Span::new("(x / 2, [y]G, 1)");
    assert_eq!(
        paren_expr(input).unwrap().1.extra.inner,
        Expr::Tuple(vec![
            sp(
                1,
                "x / 2",
                Expr::Binary {
                    lhs: Box::new(sp(1, "x", Expr::Variable)),
                    op: BinaryOp::from_span(span(3, "/")),
                    rhs: Box::new(sp(5, "2", Expr::Number)),
                }
            ),
            sp(
                8,
                "[y]G",
                Expr::Binary {
                    lhs: Box::new(sp(9, "y", Expr::Variable)),
                    op: BinaryOp::from_span(span(10, "]")),
                    rhs: Box::new(sp(11, "G", Expr::Variable)),
                }
            ),
            sp(14, "1", Expr::Number),
        ]),
    );
}

#[test]
fn lvalues_are_parsed() {
    let input = Span::new("x =");
    assert_eq!(
        lvalue(input).unwrap().1.extra,
        Lvalue::Variable { ty: None }
    );

    let input = Span::new("(x, (y, z)) =");
    assert_eq!(
        lvalue(input).unwrap().1.extra,
        Lvalue::Tuple(vec![
            lsp(1, "x", Lvalue::Variable { ty: None }),
            lsp(
                4,
                "(y, z)",
                Lvalue::Tuple(vec![
                    lsp(5, "y", Lvalue::Variable { ty: None }),
                    lsp(8, "z", Lvalue::Variable { ty: None }),
                ])
            )
        ])
    );

    let input = Span::new("(x: (Sc, _), (y, z: Ge)) =");
    assert_eq!(
        lvalue(input).unwrap().1.extra,
        Lvalue::Tuple(vec![
            lsp(
                1,
                "x",
                Lvalue::Variable {
                    ty: Some(map_span(
                        span(4, "(Sc, _)"),
                        ValueType::Tuple(vec![ValueType::Scalar, ValueType::Any,])
                    )),
                }
            ),
            lsp(
                13,
                "(y, z: Ge)",
                Lvalue::Tuple(vec![
                    lsp(14, "y", Lvalue::Variable { ty: None }),
                    lsp(
                        17,
                        "z",
                        Lvalue::Variable {
                            ty: Some(map_span(span(20, "Ge"), ValueType::Element)),
                        }
                    ),
                ])
            )
        ])
    );
}

#[test]
fn expr_evaluation_order() {
    let input = Span::new("1 - 2 + 3 - 4;");
    assert_matches!(
        expr(input).unwrap().1.extra.inner,
        Expr::Binary { op, .. } if op == BinaryOp::from_span(span(10, "-"))
    );

    let input = Span::new("1 / 2 * 3 / 4;");
    assert_matches!(
        expr(input).unwrap().1.extra.inner,
        Expr::Binary { op, .. } if op == BinaryOp::from_span(span(10, "/"))
    );

    let input = Span::new("1 - 2 * 3 - 4;");
    assert_matches!(
        expr(input).unwrap().1.extra.inner,
        Expr::Binary { op, .. } if op == BinaryOp::from_span(span(10, "-"))
    );

    let input = Span::new("X - [2]G + y * Z;");
    assert_matches!(
        expr(input).unwrap().1.extra.inner,
        Expr::Binary { op, .. } if op == BinaryOp::from_span(span(9, "+"))
    );
}

#[test]
fn block_parsing() {
    let input = Span::new("{ x + y }");
    assert_eq!(
        block(input).unwrap().1,
        vec![map_span(
            span(2, "x + y"),
            Statement::Expr(sp(
                2,
                "x + y",
                Expr::Binary {
                    lhs: Box::new(sp(2, "x", Expr::Variable)),
                    op: BinaryOp::from_span(span(4, "+")),
                    rhs: Box::new(sp(6, "y", Expr::Variable)),
                }
            ))
        )]
    );

    let input = Span::new("{ x = 1 + 2; x * 3 }");
    let parsed = block(input).unwrap().1;
    assert_eq!(parsed.len(), 2);
    assert_eq!(parsed[1].fragment, "x * 3");

    let input = Span::new("{ x = 1 + 2; x * 3; }");
    let parsed = block(input).unwrap().1;
    assert_eq!(parsed.len(), 3);
    assert_eq!(parsed[2].extra, Statement::Empty);
}

#[test]
fn fn_definition_parsing() {
    let input = Span::new("fn foo(x) { x + 3 }");
    assert_eq!(
        fun_def(input).unwrap().1,
        FnDefinition {
            name: span(3, "foo"),
            args: vec![lsp(7, "x", Lvalue::Variable { ty: None }),],
            body: vec![map_span(
                span(12, "x + 3"),
                Statement::Expr(sp(
                    12,
                    "x + 3",
                    Expr::Binary {
                        lhs: Box::new(sp(12, "x", Expr::Variable)),
                        op: BinaryOp::from_span(span(14, "+")),
                        rhs: Box::new(sp(16, "3", Expr::Number)),
                    }
                ))
            )],
        }
    );

    let input = Span::new("fn foo(x: Sc, (y, _: Ge)) { x + y }");
    let mut def = fun_def(input).unwrap().1;
    assert_eq!(def.body.len(), 1);
    def.body.clear();
    assert_eq!(
        def,
        FnDefinition {
            name: span(3, "foo"),
            args: vec![
                lsp(
                    7,
                    "x",
                    Lvalue::Variable {
                        ty: Some(map_span(span(10, "Sc"), ValueType::Scalar)),
                    }
                ),
                lsp(
                    14,
                    "(y, _: Ge)",
                    Lvalue::Tuple(vec![
                        lsp(15, "y", Lvalue::Variable { ty: None }),
                        lsp(
                            18,
                            "_",
                            Lvalue::Variable {
                                ty: Some(map_span(span(21, "Ge"), ValueType::Element)),
                            }
                        )
                    ])
                ),
            ],
            body: vec![],
        }
    );
}

#[test]
fn incomplete_fn() {
    let input = Span::new(":sc(1,");
    assert_matches!(fun(input).unwrap_err(), NomErr::Incomplete(_));
}

#[test]
fn incomplete_expr() {
    const SNIPPETS: &[&str] = &[
        "1 +",
        "2 + 3*",
        "2 * :sc(1,",
        ":sc(x) +",
        "(",
        "(x, ",
        "(x, 3 +",
        "(x, 3) + ",
    ];
    for snippet in SNIPPETS {
        let input = Span::new(snippet);
        assert_matches!(expr(input).unwrap_err(), NomErr::Incomplete(_));
    }
}

#[test]
fn incomplete_statement() {
    const SNIPPETS: &[&str] = &[
        "x ?=",
        "x =",
        "(",
        "(x, y",
        "(x, y) =",
        "(\nx: Ge,",
        "x = 2 +",
        "x ?= 2 +",
    ];
    for snippet in SNIPPETS {
        let input = Span::new(snippet);
        assert_matches!(statement(input).unwrap_err(), NomErr::Incomplete(_));
    }
}

#[test]
fn separated_statements_parse() {
    let input = Span::new("x = 1 + 2; x\0");
    let statements = separated_statements(input).unwrap().1;
    assert_eq!(statements.len(), 2);
    assert_eq!(
        statements[1].extra,
        Statement::Expr(sp(11, "x", Expr::Variable))
    );

    let input = Span::new("fn foo(x) { 2*x } :foo(3)\0");
    let statements = separated_statements(input).unwrap().1;
    assert_eq!(statements.len(), 2);
    assert_eq!(statements[1].fragment, ":foo(3)");

    let input = Span::new("{ x = 2; }; :foo(3)\0");
    let statements = separated_statements(input).unwrap().1;
    assert_eq!(statements.len(), 2);
    assert_eq!(statements[1].fragment, ":foo(3)");

    let input = Span::new("y = { x = 2; x + 3 }; :foo(y)\0");
    let statements = separated_statements(input).unwrap().1;
    assert_eq!(statements.len(), 2);
    assert_eq!(statements[1].fragment, ":foo(y)");
}
