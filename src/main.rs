mod ast;
mod builtin;
mod interpret;
mod parse;
mod value;

use std::path::PathBuf;

use clap::Clap;

fn main() {
    use std::process::*;

    color_backtrace::install();

    let app = App::parse();

    // Parse and check
    let main_path = if let Some(path) = app.target {
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
    let items = match parse::parse(&input) {
        Ok(items) => items,
        Err(errors) => {
            for error in errors {
                println!("{}", error)
            }
            exit(1);
        }
    };
    println!("Check succeeded");

    // Run
    if app.check {
        return;
    }

    println!("Execution model...");

    for item in items {
        println!("{:?}", item);
    }
}

#[derive(Clap)]
struct App {
    target: Option<PathBuf>,
    #[clap(short, long, about = "Check code validity without running")]
    check: bool,
}
