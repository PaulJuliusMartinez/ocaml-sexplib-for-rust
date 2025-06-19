// I don't like this rule because it changes the semantic
// structure of the code.
#![allow(clippy::collapsible_else_if)]
// Sometimes "x >= y + 1" is semantically clearer than "x > y"
#![allow(clippy::int_plus_one)]

mod atom;
pub mod error;
pub mod ser;
pub mod sexp;
mod token_writer;

pub use sexp::Sexp;

pub use error::{Error, Result};
pub use ser::{to_string, to_string_mach, to_writer, to_writer_mach, Serializer};
pub use sexp::de::from_sexp;
pub use sexp::ser::to_sexp;
