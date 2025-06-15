// I don't like this rule because it changes the semantic
// structure of the code.
#![allow(clippy::collapsible_else_if)]
// Sometimes "x >= y + 1" is semantically clearer than "x > y"
#![allow(clippy::int_plus_one)]

mod atom;
mod de;
mod error;
mod ser;
mod sexp;
mod token_writer;

pub use sexp::Sexp;

pub use de::{from_sexp, Deserializer};
pub use error::{Error, Result};
pub use ser::{to_sexp, Serializer};
