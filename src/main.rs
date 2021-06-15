mod ast;
mod builtin;
mod entity;
mod fmt;
mod list;
mod num;
mod parse;
mod pattern;
mod runtime;
#[cfg(test)]
mod test;
mod value;

use std::path::PathBuf;

use clap::Clap;

fn main() {
    use std::process::*;

    use crate::runtime::Runtime;

    color_backtrace::install();

    let app = App::parse();

    // Parse and check
    let main_path = if let Some(mut path) = app.target {
        if path.extension().is_none() && !path.exists() {
            path = path.with_extension("bimo");
        }
        if !path.exists() {
            println!("input file \"{}\" does not exist", path.to_string_lossy());
            exit(1);
        }
        path
    } else {
        let path = PathBuf::from("main.bimo");
        if path.exists() {
            path
        } else {
            println!("No input file specified, and no \"main.bimo\" found");
            exit(1);
        }
    };
    let input = std::fs::read_to_string(&main_path).unwrap();

    let mut runtime = Runtime::new();

    if app.check {
        if let Err(errors) = runtime.check(&input, main_path) {
            for error in errors {
                println!("{}", error)
            }
            exit(1);
        } else {
            println!("Check succeeded");
        }
    } else {
        match runtime.eval(&input, main_path) {
            Ok(_) => {}
            Err(e) => {
                println!("{}", e);
                exit(1);
            }
        }
    }
}

#[derive(Clap)]
struct App {
    target: Option<PathBuf>,
    #[clap(short, long, about = "Check code validity without running")]
    check: bool,
}
