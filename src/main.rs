mod ast;
mod builtin;
mod parse;
mod value;

use clap::Clap;

fn main() {
    use std::process::*;

    color_backtrace::install();

    let _app = App::parse();

    // Parse and check
    let input = std::fs::read_to_string("test.bimo").unwrap();
    let _items = match parse::parse(&input) {
        Ok(items) => items,
        Err(errors) => {
            for error in errors {
                println!("{}", error)
            }
            exit(1);
        }
    };
    println!("Check succeeded");
}

#[derive(Clap)]
struct App {
    #[clap(subcommand)]
    _sub: Sub,
}

#[derive(Clap)]
enum Sub {
    #[clap(alias = "c")]
    Check,
    #[clap(alias = "r")]
    Run,
}
