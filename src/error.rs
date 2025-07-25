use std::fmt::{self, Display};
use std::io;

use serde::{de, ser};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
pub enum Error {
    SerializationError(String),
    DeserializationError(String),
    Io(io::Error),
}

impl Error {
    pub fn io(io_err: io::Error) -> Error {
        Error::Io(io_err)
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::Io(err)
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
            Error::Io(io_err) => write!(formatter, "{}", io_err),
        }
    }
}

impl std::error::Error for Error {}
