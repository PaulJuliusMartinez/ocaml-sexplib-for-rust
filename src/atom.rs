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
    NeedsToBeQuoted(&'a [u8]),
    DoesNotNeedToBeQuoted(&'a str),
}

use Atom::*;

fn is_debug_printable_non_ascii_char(ch: char) -> bool {
    ch.escape_debug().count() == 1
}

fn write_hex_byte<W: io::Write>(mut w: W, b: u8) -> io::Result<()> {
    write!(w, "\\x{:02x}", b)
}

fn write_escaped_str<W: io::Write>(mut w: W, s: &str) -> io::Result<()> {
    for ch in s.chars() {
        if ch.is_ascii() {
            match ch {
                '"' => write!(w, "\\\"")?,
                '\\' => write!(w, "\\\\")?,
                '\n' => write!(w, "\\n")?,
                '\r' => write!(w, "\\r")?,
                '\t' => write!(w, "\\t")?,
                '\x08' => write!(w, "\\b")?,
                // Control characters and DEL
                '\x00'..='\x1f' | '\x7f' => {
                    write_hex_byte(&mut w, ch as u32 as u8)?;
                }
                _ => write!(w, "{}", ch)?,
            }
        } else {
            if is_debug_printable_non_ascii_char(ch) {
                write!(w, "{}", ch)?;
            } else {
                let mut utf8_bytes = [0; 4];
                for b in ch.encode_utf8(&mut utf8_bytes).as_bytes() {
                    write_hex_byte(&mut w, *b)?;
                }
            }
        }
    }

    Ok(())
}

fn write_hex_bytes<W: io::Write>(mut w: W, bytes: &[u8]) -> io::Result<()> {
    for b in bytes.iter() {
        write!(w, "\\x{:02x}", b)?;
    }

    Ok(())
}

impl<'a> Atom<'a> {
    pub fn new(bytes: &'a [u8]) -> Atom<'a> {
        if bytes.is_empty() {
            return NeedsToBeQuoted(bytes);
        }

        let Ok(s) = std::str::from_utf8(bytes) else {
            return NeedsToBeQuoted(bytes);
        };

        Self::new_from_str(s)
    }

    pub fn new_from_str(s: &'a str) -> Atom<'a> {
        let bytes = s.as_bytes();

        let mut chars = s.chars().peekable();

        while let Some(ch) = chars.next() {
            if ch.is_ascii() {
                match ch {
                    ' ' | '"' | '(' | ')' | ';' | '\\' => {
                        return NeedsToBeQuoted(bytes);
                    }
                    '#' => {
                        if let Some('|') = chars.peek() {
                            return NeedsToBeQuoted(bytes);
                        }
                    }
                    '|' => {
                        if let Some('#') = chars.peek() {
                            return NeedsToBeQuoted(bytes);
                        }
                    }
                    // Control characters
                    '\x00'..='\x1f' => return NeedsToBeQuoted(bytes),
                    // DEL
                    '\x7f' => return NeedsToBeQuoted(bytes),
                    // All other ASCII chars should be fine
                    _ => (),
                }
            } else {
                if !is_debug_printable_non_ascii_char(ch) {
                    return NeedsToBeQuoted(bytes);
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
            Atom::DoesNotNeedToBeQuoted(s) => write!(w, "{}", s),
            Atom::NeedsToBeQuoted(mut bytes) => {
                write!(w, "\"")?;

                while !bytes.is_empty() {
                    let utf8_error = match std::str::from_utf8(bytes) {
                        Ok(s) => {
                            write_escaped_str(&mut w, s)?;
                            break;
                        }
                        Err(err) => err,
                    };

                    let valid_len = utf8_error.valid_up_to();
                    let error_len = match utf8_error.error_len() {
                        Some(len) => len,
                        None => bytes.len() - valid_len,
                    };

                    let (valid_segment, rest) = bytes.split_at(valid_len);
                    let (error_segment, rest) = rest.split_at(error_len);
                    bytes = rest;

                    if valid_len > 0 {
                        // `valid_up_to` is the maximum index such that
                        // `from_utf8(&input[..index])` would return Ok(_).
                        let valid_utf8_segment =
                            unsafe { std::str::from_utf8_unchecked(valid_segment) };

                        write_escaped_str(&mut w, valid_utf8_segment)?;
                    }

                    write_hex_bytes(&mut w, error_segment)?;
                }

                write!(w, "\"")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use insta::assert_snapshot;

    fn needs_to_be_quoted(bytes: &[u8]) -> bool {
        Atom::new(bytes).needs_to_be_quoted()
    }

    #[test]
    fn test_needs_to_quoted() {
        assert!(needs_to_be_quoted(b""));
        assert!(needs_to_be_quoted(b"a b"));
        assert!(needs_to_be_quoted(b"("));
        assert!(needs_to_be_quoted(b")"));
        assert!(needs_to_be_quoted(b";"));
        assert!(needs_to_be_quoted(b"#|"));
        assert!(needs_to_be_quoted(b"a#|"));
        assert!(needs_to_be_quoted(b"|#"));
        assert!(needs_to_be_quoted(b"a|#"));
        assert!(needs_to_be_quoted(b"\\"));

        assert!(!needs_to_be_quoted(b"a"));
        assert!(!needs_to_be_quoted(b"#a|"));
        assert!(!needs_to_be_quoted(b"|a#"));
        assert!(!needs_to_be_quoted("αβγ".as_bytes()));
    }

    fn escape_bytes(bytes: &[u8]) -> String {
        let mut buf = vec![];
        let atom = Atom::new(bytes);
        atom.write(&mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }
    fn escape_str(s: &str) -> String {
        escape_bytes(s.as_bytes())
    }

    #[test]
    fn test_basic_write() {
        assert_snapshot!(escape_str(&"abc"), @"abc");
        assert_snapshot!(escape_str(&"x y z"), @"\"x y z\"");
        assert_snapshot!(escape_bytes("abc".as_bytes()), @"abc");
        assert_snapshot!(escape_bytes("x y z".as_bytes()), @r#""x y z""#);
    }

    #[test]
    fn test_escaping() {
        assert_snapshot!(escape_str(&"a\nb"), @r#""a\nb""#);
        assert_snapshot!(escape_str(&"a\tb"), @r#""a\tb""#);
        assert_snapshot!(escape_str(&"a\rb"), @r#""a\rb""#);
        assert_snapshot!(escape_str(&"a\x0bb"), @r#""a\x0bb""#);
        assert_snapshot!(escape_str(&"a\"b"), @r#""a\"b""#);
        assert_snapshot!(escape_str(&"a\\b"), @r#""a\\b""#);
        assert_snapshot!(escape_str(&"a\\b"), @r#""a\\b""#);
        assert_snapshot!(escape_str(&"a\0b"), @r#""a\x00b""#);

        // Non-breaking space
        assert_snapshot!(escape_str(&"a\u{00A0}b"), @r#""a\xc2\xa0b""#);
        // Zero-width joiner
        assert_snapshot!(escape_str(&"a\u{200D}b"), @r#""a\xe2\x80\x8db""#);
        // Bactrian Camel
        assert_snapshot!(escape_str(&"a🐫b"), @"a🐫b");

        // Random bytes (invalid UTF-8);
        assert_snapshot!(escape_bytes(&[0x00, 0x01, 0x1F, 0x7F, 0x80, 0xFF]), @r#""\x00\x01\x1f\x7f\x80\xff""#);

        // 0xF0 0x9F 0x90 0xAB is the Bactrian Camel; we'll test prefixes before a valid byte, and
        // before the end of the file.
        assert_snapshot!(escape_bytes(&[b'^', 0xF0, 0x9F, 0x90, 0xAB, b'$']), @"^🐫$");
        assert_snapshot!(escape_bytes(&[b'^', 0xF0, 0x9F, 0x90, b'$']), @r#""^\xf0\x9f\x90$""#);
        assert_snapshot!(escape_bytes(&[b'^', 0xF0, 0x9F, b'$']), @r#""^\xf0\x9f$""#);
        assert_snapshot!(escape_bytes(&[b'^', 0xF0, b'$']), @r#""^\xf0$""#);

        assert_snapshot!(escape_bytes(&[b'^', 0xF0, 0x9F, 0x90, 0xAB]), @"^🐫");
        assert_snapshot!(escape_bytes(&[b'^', 0xF0, 0x9F, 0x90]), @r#""^\xf0\x9f\x90""#);
        assert_snapshot!(escape_bytes(&[b'^', 0xF0, 0x9F]), @r#""^\xf0\x9f""#);
        assert_snapshot!(escape_bytes(&[b'^', 0xF0]), @r#""^\xf0""#);
    }
}
