mod ast;
mod builtin;
mod entity;
mod error;
mod fmt;
mod formatter;
mod list;
mod num;
mod parse;
mod pattern;
mod runtime;
#[cfg(test)]
mod test;
mod value;

use std::{path::PathBuf, process::*};

use clap::Clap;
use walkdir::DirEntry;

use crate::formatter::FormatSettings;

fn main() {
    use crate::runtime::Runtime;

    color_backtrace::install();

    let app = App::parse();

    if let Some(sub) = app.sub {
        match sub {
            Sub::Fmt { target } => {
                // Format
                let targets = if let Some(target) = target {
                    vec![target]
                } else {
                    walkdir::WalkDir::new(".")
                        .into_iter()
                        .filter_map(Result::ok)
                        .filter(|entry| {
                            entry.file_type().is_file()
                                && entry.path().extension().map_or(false, |ext| ext == "bimo")
                        })
                        .map(DirEntry::into_path)
                        .collect()
                };
                let settings = FormatSettings::default();
                for target in targets {
                    if let Err(e) = settings.format(&target) {
                        println!("Error formatting {}\n{}", target.to_string_lossy(), e);
                    }
                }
            }
        }
    } else {
        // Parse and check
        let main_path = if let Some(path) = app.target {
            match src_file_path(path) {
                Ok(path) => path,
                Err(e) => {
                    println!("{}", e);
                    exit(1)
                }
            }
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
}

fn src_file_path(path: impl Into<PathBuf>) -> Result<PathBuf, String> {
    let mut path = path.into();
    if path.extension().is_none() && !path.exists() {
        path = path.with_extension("bimo");
    }
    if path.exists() {
        Ok(path)
    } else {
        Err(format!(
            "Input file \"{}\" does not exist",
            path.to_string_lossy()
        ))
    }
}

#[derive(Clap)]
struct App {
    target: Option<PathBuf>,
    #[clap(short, long, about = "Check code validity without running")]
    check: bool,
    #[clap(subcommand)]
    sub: Option<Sub>,
}

#[derive(Clap)]
enum Sub {
    Fmt { target: Option<PathBuf> },
}
