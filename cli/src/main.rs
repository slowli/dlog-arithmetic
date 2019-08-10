use codespan::{ByteIndex, ByteOffset, ByteSpan, CodeMap, FileName};
use codespan_reporting::{
    emit,
    termcolor::{Color, ColorChoice, ColorSpec, StandardStream, StandardStreamLock, WriteColor},
    Diagnostic, Label, LabelStyle, Severity,
};
use dlog_arithmetic::{
    functions as fns,
    parser::{Error as ParseError, Span, Spanned, Statement},
    BacktraceElement, Code, Context, Ed25519, ErrorWithBacktrace, EvalError, Group, Scope, Value,
};
use rand::thread_rng;
use rustyline::{error::ReadlineError, Editor};

use std::{
    borrow::Cow,
    io::{self, Write},
};

fn byte_span<T>(span: &Spanned<T>) -> ByteSpan {
    let start = span.offset as u32;
    let end = start + span.fragment.len() as u32;
    ByteSpan::new(ByteIndex(start), ByteIndex(end))
}

fn print_greeting(writer: &StandardStream) -> Result<(), io::Error> {
    let mut writer = writer.lock();
    writer.set_color(ColorSpec::new().set_bold(true))?;
    writeln!(
        writer,
        "dlog-arithmetic REPL v{}",
        env!("CARGO_PKG_VERSION")
    )?;
    writer.reset()?;
    writeln!(writer, "{}", env!("CARGO_PKG_DESCRIPTION"))?;
    writeln!(writer, "Type `.help` for help.")
}

fn report_parse_error(writer: &StandardStream, code_map: &CodeMap<&str>, e: Spanned<ParseError>) {
    let label = Label::new_primary(byte_span(&e)).with_message("Error occurred here");
    let diagnostic = Diagnostic::new_error(e.extra.to_string())
        .with_code("PARSE")
        .with_label(label);
    emit(&mut writer.lock(), code_map, &diagnostic).unwrap();
}

fn report_eval_error(writer: &StandardStream, code_map: &CodeMap<&str>, e: ErrorWithBacktrace) {
    let severity = Severity::Error;
    let main_label = Label::new(byte_span(&e.inner), LabelStyle::Primary);
    let message: Cow<str> = match e.inner.extra {
        EvalError::DivisionByZero => "Right-hand side of this division is 0".into(),
        EvalError::IntToScalar(_) => "Number cannot be converted into scalar".into(),
        EvalError::ArgTypeMismatch { ref expected } => {
            format!("Function expects arguments {}", expected).into()
        }
        EvalError::FunctionCall(ref e) => e.to_string().into(),
        EvalError::InvalidBinaryOp {
            op,
            ref lhs_ty,
            ref rhs_ty,
        } => format!(
            "Operation `{}` is not defined for types {} and {}",
            op, lhs_ty, rhs_ty
        )
        .into(),

        // FIXME: make human-readable descriptions
        ref e => format!("{:?}", e).into(),
    };
    let mut diagnostic = Diagnostic::new(severity, e.inner.extra.to_string())
        .with_code("EVAL")
        .with_label(main_label.with_message(message));

    let mut calls_iter = e.backtrace.calls();
    if let Some(BacktraceElement {
        fn_name,
        def_span,
        call_span,
    }) = calls_iter.next()
    {
        let def_label = Label::new_secondary(byte_span(&def_span))
            .with_message(format!("The error occurred in function `{}`", fn_name));
        diagnostic = diagnostic.with_label(def_label);

        let mut call_site = call_span;
        for BacktraceElement {
            fn_name, call_span, ..
        } in calls_iter
        {
            let call_label = Label::new_secondary(byte_span(&call_site))
                .with_message(format!("...which was called from function `{}`", fn_name));
            diagnostic = diagnostic.with_label(call_label);
            call_site = call_span;
        }
        let call_label = Label::new_secondary(byte_span(&call_site))
            .with_message("...which was called from here");
        diagnostic = diagnostic.with_label(call_label);
    }

    emit(&mut writer.lock(), code_map, &diagnostic).unwrap();
}

fn dump_variable<G: Group>(
    writer: &mut StandardStreamLock,
    var: &Value<G>,
    indent: usize,
) -> io::Result<()> {
    let buffer_color = ColorSpec::new().set_fg(Some(Color::Cyan)).clone();
    let sc_color = ColorSpec::new().set_fg(Some(Color::Green)).clone();
    let ge_color = ColorSpec::new().set_fg(Some(Color::Yellow)).clone();

    match var {
        Value::Bool(b) => {
            writer.set_color(&buffer_color)?;
            write!(writer, "{}", if *b { "true" } else { "false" })?;
            writer.reset()
        }
        Value::Buffer(buffer) => {
            writer.set_color(&buffer_color)?;
            write!(writer, "0x_{}", hex::encode(buffer))?;
            writer.reset()
        }
        Value::Scalar(sc) => {
            writer.set_color(&sc_color)?;
            write!(writer, "0xs_{}", hex::encode(G::scalar_to_bytes(*sc)))?;
            writer.reset()
        }
        Value::Element(ge) => {
            writer.set_color(&ge_color)?;
            write!(writer, "0xg_{}", hex::encode(G::element_to_bytes(*ge)))?;
            writer.reset()
        }
        Value::Void => Ok(()),
        Value::Tuple(fragments) => {
            writeln!(writer, "(")?;
            for (i, fragment) in fragments.iter().enumerate() {
                write!(writer, "{}", " ".repeat(indent + 2))?;
                dump_variable(writer, fragment, indent + 2)?;
                if i + 1 < fragments.len() {
                    writeln!(writer, ",")?;
                } else {
                    writeln!(writer)?;
                }
            }
            write!(writer, "{})", " ".repeat(indent))
        }
    }
}

fn dump_scope<G: Group>(writer: &StandardStream, scope: &Scope<G>) -> io::Result<()> {
    let mut writer = writer.lock();
    for (name, var) in scope.variables() {
        write!(writer, "{} = ", name)?;
        dump_variable(&mut writer, &var, 0)?;
        writeln!(writer)?;
    }

    let fn_color = ColorSpec::new().set_fg(Some(Color::Magenta)).clone();
    for (name, ty) in scope.functions() {
        write!(writer, "{} = ", name)?;
        writer.set_color(&fn_color)?;
        writeln!(writer, "{}", ty)?;
        writer.reset()?;
    }
    Ok(())
}

fn parse_and_eval<'a, G: Group>(
    writer: &StandardStream,
    line: &str,
    line_index: usize,
    code: &'a Code,
    code_map: &mut CodeMap<&'a str>,
    state: &mut Context<'a, G>,
) -> Result<bool, ()> {
    // Append the line to the code map.
    let line = code.add_terminated_string(line.to_owned());
    let file_name = format!("Snip #{}", line_index);
    let file = code_map.add_filemap(FileName::Virtual(file_name.into()), line);
    let byte_span = file.span();
    let visible_span = byte_span.with_end(byte_span.end() - ByteOffset(1));

    if line.starts_with('.') {
        match &line[..(line.len() - 1)] {
            ".clear" => state.innermost_scope().clear(),
            ".dump" => dump_scope(writer, state.innermost_scope()).unwrap(),
            ".help" => unimplemented!(),

            s if s.starts_with(".def ") => {
                let fn_name = &s[5..];
                if let Some(fun) = state.get_fn(fn_name) {
                    if let Some(def) = fun.definition() {
                        println!("{}", def.fragment);
                    } else {
                        println!("<native function>");
                    }
                } else {
                    let label = Label::new(visible_span, LabelStyle::Primary)
                        .with_message(format!("Function `{}` is not defined", fn_name));
                    let diagnostic = Diagnostic::new_error("Undefined function")
                        .with_code("CMD")
                        .with_label(label);
                    emit(&mut writer.lock(), &code_map, &diagnostic).unwrap();
                }
            }

            _ => {
                let label = Label::new(visible_span, LabelStyle::Primary)
                    .with_message("Use `.help commands` to find out commands");
                let diagnostic = Diagnostic::new_error("Unknown command")
                    .with_code("CMD")
                    .with_label(label);
                emit(&mut writer.lock(), &code_map, &diagnostic).unwrap();
            }
        }
        return Ok(false);
    }

    let span = Span {
        offset: byte_span.start().0 as usize,
        line: 0, // not used by the code, so we set it to a dummy value
        fragment: line,
        extra: (),
    };
    let mut incomplete = false;
    let statements = Statement::parse_list(span).or_else(|e| {
        if e.extra == ParseError::Incomplete {
            incomplete = true;
            Ok(vec![])
        } else {
            report_parse_error(writer, code_map, e);
            Err(())
        }
    })?;

    if !incomplete {
        let output = state.evaluate(&statements).map_err(|e| {
            report_eval_error(writer, code_map, e);
        })?;
        if output != Value::Void {
            dump_variable(&mut writer.lock(), &output, 0).unwrap();
        }
    }
    Ok(incomplete)
}

fn main() {
    let mut rl = Editor::<()>::new();
    let writer = StandardStream::stderr(ColorChoice::Auto);
    print_greeting(&writer).unwrap();
    let code = Code::new();
    let mut code_map = CodeMap::new();
    let mut line_index = 0;

    let mut state = Context::typed(Ed25519);
    state
        .innermost_scope()
        .insert_native_fn("sc_sha512", fns::FromSha512)
        .insert_native_fn("sc_rand", fns::Rand::new(thread_rng()))
        .insert_var("O", Value::Element(Ed25519.identity_element()))
        .insert_var("G", Value::Element(Ed25519.base_element()));
    state.create_scope();
    let mut snippet = String::new();
    let mut prompt = ">>> ";

    loop {
        let line = rl.readline(prompt);
        match line {
            Ok(line) => {
                snippet.push_str(&line);
                if let Ok(incomplete) = parse_and_eval(
                    &writer,
                    &snippet,
                    line_index,
                    &code,
                    &mut code_map,
                    &mut state,
                ) {
                    if incomplete {
                        prompt = "... ";
                        snippet.push('\n');
                    } else {
                        prompt = ">>> ";
                        snippet.clear();
                        line_index += 1;
                    }
                    rl.add_history_entry(line);
                } else {
                    prompt = ">>> ";
                    snippet.clear();
                }
            }

            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => {
                println!("Bye");
                break;
            }

            Err(e) => panic!("Error reading command: {}", e),
        }
    }
}
