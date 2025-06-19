use std::io;

// sexplib0 quotes empty strings, strings containing ' ', '"', '(', ')', ';' and
// '\', as well as strings containing "#|" or "|#", containing control characters,
// or containing byte values 127-255.
//
// Since Rust supports UTF-8, we will not automatically escape non-ASCII characters
// unless they are not printable. The [sexp] CLI tool handles unescaped UTF-8 fine as
// input:
//
// $ echo "(abc 123 αβγ)" | sexp pp
// > (abc 123 "\206\177\206\178\206\179")
//
// https://github.com/janestreet/sexplib0/blob/master/src/sexp.ml#L58
pub enum Atom<'a> {
    NeedsToBeQuoted(&'a str),
    DoesNotNeedToBeQuoted(&'a str),
}

use Atom::*;

fn is_debug_printable_non_ascii_char(ch: char) -> bool {
    ch.escape_debug().count() == 1
}

impl<'a> Atom<'a> {
    pub fn new(s: &'a str) -> Atom<'a> {
        if s.is_empty() {
            return NeedsToBeQuoted(s);
        }

        let mut chars = s.chars().peekable();

        while let Some(ch) = chars.next() {
            if ch.is_ascii() {
                match ch {
                    ' ' | '"' | '(' | ')' | ';' | '\\' => {
                        return NeedsToBeQuoted(s);
                    }
                    '#' => {
                        if let Some('|') = chars.peek() {
                            return NeedsToBeQuoted(s);
                        }
                    }
                    '|' => {
                        if let Some('#') = chars.peek() {
                            return NeedsToBeQuoted(s);
                        }
                    }
                    // Control characters
                    '\x00'..='\x1f' => return NeedsToBeQuoted(s),
                    // DEL
                    '\x7f' => return NeedsToBeQuoted(s),
                    // All other ASCII chars should be fine
                    _ => (),
                }
            } else {
                if !is_debug_printable_non_ascii_char(ch) {
                    return NeedsToBeQuoted(s);
                }
            }
        }

        DoesNotNeedToBeQuoted(s)
    }

    pub fn needs_to_be_quoted(&self) -> bool {
        match self {
            Atom::NeedsToBeQuoted(_) => true,
            Atom::DoesNotNeedToBeQuoted(_) => false,
        }
    }

    pub fn write<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        match self {
            Atom::NeedsToBeQuoted(s) => {
                write!(w, "\"")?;
                write!(w, "{}", s)?;
                write!(w, "\"")
            }
            Atom::DoesNotNeedToBeQuoted(s) => write!(w, "{}", s),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn needs_to_be_quoted(s: &str) -> bool {
        Atom::new(s).needs_to_be_quoted()
    }

    #[test]
    fn test_needs_to_quoted() {
        assert!(needs_to_be_quoted(""));
        assert!(needs_to_be_quoted("a b"));
        assert!(needs_to_be_quoted("("));
        assert!(needs_to_be_quoted(")"));
        assert!(needs_to_be_quoted(";"));
        assert!(needs_to_be_quoted("#|"));
        assert!(needs_to_be_quoted("a#|"));
        assert!(needs_to_be_quoted("|#"));
        assert!(needs_to_be_quoted("a|#"));
        assert!(needs_to_be_quoted("\\"));

        assert!(!needs_to_be_quoted("a"));
        assert!(!needs_to_be_quoted("#a|"));
        assert!(!needs_to_be_quoted("|a#"));
        assert!(!needs_to_be_quoted("αβγ"));
    }
}
