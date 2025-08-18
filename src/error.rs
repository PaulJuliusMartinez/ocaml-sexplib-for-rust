use std::fmt::{self, Display};
use std::io;
use std::sync::Arc;

use serde::{de, ser};

use crate::tokenizer;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug)]
pub enum Error {
    SerializationError(String),
    DeserializationError(String),
    // Someday: Store the location of the tokenization error.
    TokenizationError(tokenizer::Error),
    // Arc so this can be made [Clone]
    IoError(Arc<io::Error>),
}

impl Error {
    pub fn io(io_err: io::Error) -> Error {
        Error::IoError(Arc::new(io_err))
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::IoError(Arc::new(err))
    }
}

impl From<tokenizer::Error> for Error {
    fn from(err: tokenizer::Error) -> Error {
        Error::TokenizationError(err)
    }
}

impl ser::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Error::SerializationError(msg.to_string())
    }
}

impl de::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Error::DeserializationError(msg.to_string())
    }
}

impl Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::SerializationError(msg) => formatter.write_str(msg),
            Error::DeserializationError(msg) => formatter.write_str(msg),
            Error::TokenizationError(tokenization_err) => {
                write!(formatter, "{:?}", tokenization_err)
            }
            Error::IoError(io_err) => write!(formatter, "{}", io_err),
        }
    }
}

impl std::error::Error for Error {}
