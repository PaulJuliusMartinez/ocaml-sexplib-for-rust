use std::borrow::Cow;

#[derive(Clone, Debug)]
pub enum Sexp<'a> {
    Atom(Cow<'a, str>),
    List(Vec<Sexp<'a>>),
}
