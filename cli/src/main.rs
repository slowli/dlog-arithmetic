use codespan::{ByteIndex, ByteSpan, CodeMap, FileName};
use codespan_reporting::{
    emit,
    termcolor::{Color, ColorChoice, ColorSpec, StandardStream, StandardStreamLock, WriteColor},
    Diagnostic, Label, LabelStyle, Severity,
};
use eccalc::{
    functions as fns,
    parser::{Error as ParseError, Spanned, Statement},
    Ed25519, EvalError, Group, Scope, Value,
};
use rand::thread_rng;
use rustyline::{error::ReadlineError, Editor};

use std::{
    borrow::Cow,
    io::{self, Write},
};

fn byte_span<T>(span: &Spanned<T>) -> ByteSpan {
    let start = span.offset as u32 + 1;
    let end = start + span.fragment.len() as u32;
    ByteSpan::new(ByteIndex(start), ByteIndex(end))
}

fn print_greeting(writer: &StandardStream) -> Result<(), io::Error> {
    let mut writer = writer.lock();
    writer.set_color(ColorSpec::new().set_bold(true))?;
    writeln!(writer, "eccalc REPL v{}", env!("CARGO_PKG_VERSION"))?;
    writer.reset()?;
    writeln!(writer, "{}", env!("CARGO_PKG_DESCRIPTION"))?;
    writeln!(writer, "Type `.help` for help.")
}

fn report_parse_error(writer: &StandardStream, code_map: &CodeMap<&str>, e: Spanned<ParseError>) {
    let label = Label::new_primary(byte_span(&e)).with_message("Error occurred here");
    let diagnostic = Diagnostic::new_error(e.extra.to_string())
        .with_code("PARSE")
        .with_label(label);
    emit(&mut writer.lock(), &code_map, &diagnostic).unwrap();
}

fn report_eval_error(writer: &StandardStream, code_map: &CodeMap<&str>, e: Spanned<EvalError>) {
    let severity = match e.extra {
        EvalError::AssertionFail => Severity::Warning,
        _ => Severity::Error,
    };
    let main_label = Label::new(byte_span(&e), LabelStyle::Primary);
    let message: Cow<str> = match e.extra {
        EvalError::DivisionByZero => "Right-hand side of this division is 0".into(),
        EvalError::AssertionFail => "Sides of this comparison differ".into(),
        EvalError::IntToScalar(_) => "Number cannot be converted into scalar".into(),
        EvalError::Undefined => "Undefined variable occurrence".into(),
        EvalError::UndefinedFunction => "Undefined function occurrence".into(),
        EvalError::ArgTypeMismatch { ref expected } => {
            format!("Function expects arguments {}", expected).into()
        }
        EvalError::FunctionCall(ref e) => e.to_string().into(),
        EvalError::InvalidBinaryOp {
            op,
            ref lhs_ty,
            ref rhs_ty,
        } => format!(
            "Operation `{}` is not defined for arguments of types {} and {}",
            op, lhs_ty, rhs_ty
        )
        .into(),

        ref e => format!("{:?}", e).into(),
    };
    let diagnostic = Diagnostic::new(severity, e.extra.to_string())
        .with_code("EVAL")
        .with_label(main_label.with_message(message));
    emit(&mut writer.lock(), &code_map, &diagnostic).unwrap();
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

fn dump_state<G: Group>(writer: &StandardStream, state: &Scope<G>) -> io::Result<()> {
    let mut writer = writer.lock();
    for (name, var) in state.variables() {
        if var.constant {
            writer.set_color(ColorSpec::new().set_bold(true))?;
            write!(writer, "const ")?;
            writer.reset()?;
        }
        write!(writer, "{} = ", name)?;
        dump_variable(&mut writer, &var.value, 0)?;
        writeln!(writer)?;
    }
    Ok(())
}

fn parse_and_eval<G: Group>(
    writer: &StandardStream,
    line: &str,
    state: &mut Scope<G>,
) -> Result<(), ()> {
    let mut code_map = CodeMap::new();
    let file_map = code_map.add_filemap(FileName::Virtual("REPL".into()), line);

    if line.starts_with('.') {
        match line {
            ".clear" => state.clear(),
            ".dump" => dump_state(writer, state).unwrap(),
            ".help" => unimplemented!(),

            _ => {
                let label = Label::new(file_map.span(), LabelStyle::Primary)
                    .with_message("Use `.help commands` to find out commands");
                let diagnostic = Diagnostic::new_error("Unknown command")
                    .with_code("CMD")
                    .with_label(label);
                emit(&mut writer.lock(), &code_map, &diagnostic).unwrap();
            }
        }
        return Ok(());
    }

    let statements = Statement::list_from_str(line).map_err(|e| {
        report_parse_error(writer, &code_map, e);
    })?;
    let output = state.evaluate(&statements).map_err(|e| {
        report_eval_error(writer, &code_map, e);
    })?;
    if output != Value::Void {
        dump_variable(&mut writer.lock(), &output, 0).unwrap();
    }

    Ok(())
}

fn main() {
    let mut rl = Editor::<()>::new();
    let writer = StandardStream::stderr(ColorChoice::Auto);
    print_greeting(&writer).unwrap();
    let mut state = Scope::new(Ed25519);
    state
        .insert_fn("sc_sha512", fns::FromSha512)
        .insert_fn("sc_rand", fns::Rand(thread_rng()))
        .insert_constant("O", Value::Element(Ed25519.identity_element()))
        .insert_constant("G", Value::Element(Ed25519.base_element()));

    loop {
        let line = rl.readline(">>> ");
        match line {
            Ok(line) => {
                if parse_and_eval(&writer, &line, &mut state).is_ok() {
                    rl.add_history_entry(line);
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