// I don't like this rule because it changes the semantic
// structure of the code.
#![allow(clippy::collapsible_else_if)]
// Sometimes "x >= y + 1" is semantically clearer than "x > y"
#![allow(clippy::int_plus_one)]

mod error;
mod ser;
mod sexp;

pub use sexp::Sexp;

pub use error::{Error, Result};
pub use ser::{to_sexp, Serializer};
