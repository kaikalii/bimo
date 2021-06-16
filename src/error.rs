use std::{error::Error, fmt, io};

use itertools::Itertools;

use crate::{
    ast::FileSpan,
    parse::{format_span, CheckError},
    value::Value,
};

#[derive(Debug, Clone)]
pub struct BimoError<'i> {
    pub message: String,
    pub spans: Vec<FileSpan<'i>>,
}

impl<'i> BimoError<'i> {
    pub fn new(message: impl Into<String>, span: FileSpan<'i>) -> Self {
        BimoError::multispan(message, Some(span))
    }
    pub fn multispan(
        message: impl Into<String>,
        spans: impl IntoIterator<Item = FileSpan<'i>>,
    ) -> Self {
        BimoError {
            message: message.into(),
            spans: spans.into_iter().collect(),
        }
    }
    pub fn unspanned(message: impl Into<String>) -> Self {
        BimoError::multispan(message, None)
    }
    pub fn change_lifetime<'a>(self) -> BimoError<'a> {
        BimoError::unspanned(self.to_string())
    }
}

impl<'i> fmt::Display for BimoError<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.spans.is_empty() {
            write!(f, "{}", self.message)
        } else {
            let mut message = Some(&self.message);
            for (i, span) in self.spans.iter().enumerate() {
                if i > 0 {
                    writeln!(f)?;
                }
                format_span(message.take().cloned().unwrap_or_default(), span, f)?;
            }
            Ok(())
        }
    }
}

impl<'i> Error for BimoError<'i> {}

pub type BimoResult<'i, T = Value<'i>> = Result<T, BimoError<'i>>;

impl<'i> From<io::Error> for BimoError<'i> {
    fn from(error: io::Error) -> Self {
        BimoError::unspanned(error.to_string())
    }
}

impl<'i> From<Vec<CheckError<'i>>> for BimoError<'i> {
    #[allow(unstable_name_collisions)]
    fn from(errors: Vec<CheckError<'i>>) -> Self {
        BimoError::unspanned(
            errors
                .iter()
                .map(ToString::to_string)
                .intersperse("\n".into())
                .collect::<String>(),
        )
    }
}
