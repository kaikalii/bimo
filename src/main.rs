mod ast;
mod builtin;
mod interpret;
mod num;
mod parse;
#[cfg(test)]
mod test;
mod value;

use std::path::PathBuf;

use clap::Clap;

fn main() {
    use std::process::*;

    use crate::interpret::Runtime;

    color_backtrace::install();

    let app = App::parse();

    // Parse and check
    let main_path = if let Some(path) = app.target {
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
    let input = std::fs::read_to_string(main_path).unwrap();

    let mut runtime = Runtime::new();

    if app.check {
        if let Err(errors) = runtime.check(&input) {
            for error in errors {
                println!("{}", error)
            }
            exit(1);
        } else {
            println!("Check succeeded");
        }
    } else {
        match runtime.eval(&input) {
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
