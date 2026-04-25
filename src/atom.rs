use std::io;

/// This is wrapper type around the actual data in a sexp atom. If the serialized
/// version of an atom looks like this:
///
/// "a\"b\nc"
///
/// then the contents raw data inside the `AtomData` is:
///
/// [ b'a', b'"', b'b', b'\n', b'c']
#[derive(Debug)]
#[repr(transparent)]
pub struct AtomData([u8]);

impl AtomData {
    pub fn new(data: &[u8]) -> &AtomData {
        // SAFETY: AtomData is just a wrapper around [u8], enforced by #[repr(transparent)],
        // therefore converting &[u8] to &AtomData is safe.
        unsafe { &*(data as *const [u8] as *const AtomData) }
    }

    pub fn serialize_io<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        if self.needs_to_be_quoted() {
            write!(w, "\"")?;

            for chunk in self.0.utf8_chunks() {
                serialize_escaped_str(&mut w, chunk.valid())?;
                serialize_hex_bytes(&mut w, chunk.invalid())?;
            }

            write!(w, "\"")
        } else {
            w.write_all(&self.0)
        }
    }

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
    pub fn needs_to_be_quoted(&self) -> bool {
        if self.0.len() == 0 {
            return true;
        }

        let chunk = self
            .0
            .utf8_chunks()
            .next()
            .expect("slice has non-zero length");

        if chunk.invalid().len() > 0 {
            return true;
        }

        let mut chars = chunk.valid().chars().peekable();

        while let Some(ch) = chars.next() {
            if ch.is_ascii() {
                match ch {
                    ' ' | '"' | '(' | ')' | ';' | '\\' => {
                        return true;
                    }
                    '#' => {
                        if let Some('|') = chars.peek() {
                            return true;
                        }
                    }
                    '|' => {
                        if let Some('#') = chars.peek() {
                            return true;
                        }
                    }
                    // Control characters
                    '\x00'..='\x1f' => return true,
                    // DEL
                    '\x7f' => return true,
                    // All other ASCII chars should be fine
                    _ => (),
                }
            } else {
                if !is_debug_printable_non_ascii_char(ch) {
                    return true;
                }
            }
        }

        false
    }
}

/// This is a wrapper type around serialized atom data, including surrounding quotes (if any).
/// If the data is unquoted, it is a valid atom, but if it is quoted, backslash-escape
/// sequences in the data may be invalid (e.g. "\xfg", an invalid hex escape).
///
/// If it is a valid serialization of atom data, it may not be standardized, so regular
/// printable ASCII characters may be unnecessarily escaped, and it may not be valid UTF-8.
///
/// The [`RawToken`] type contains `PlausibleSerializedAtom`s.
#[derive(Debug)]
#[repr(transparent)]
pub struct PlausibleSerializedAtom([u8]);

impl PlausibleSerializedAtom {
    pub(crate) fn new(data: &[u8]) -> &PlausibleSerializedAtom {
        // SAFETY: PlausibleSerializedAtom is just a wrapper around [u8], enforced by
        // #[repr(transparent)], therefore converting &[u8] to &PlausibleSerializedAtom is safe.
        unsafe { &*(data as *const [u8] as *const PlausibleSerializedAtom) }
    }
}

/// This is a wrapper type around safely serialized atom data, including surrounding quotes
/// (if any). The following bytes will be escaped:
/// - Double quotes ("\""), backslash ("\\")
/// - Newlines ("\n"), tabs ("\t"), backspaces ("\b"), carriage returns ("\r")
/// - ASCII control characters (0x00 - 0x1F, 0x7F), encoded as hex
/// - Non-UTF-8 byte sequences
/// - Any characters that are escaped by Rust's `char::escape_debug` function, which includes
/// escapes any non-printable Unicode characters.
#[derive(Debug)]
#[repr(transparent)]
pub struct SafelySerializedAtom(str);

impl SafelySerializedAtom {
    fn new(data: &str) -> &SafelySerializedAtom {
        // SAFETY: SafelySerializedAtom is just a wrapper around str, enforced by
        // #[repr(transparent)], therefore converting &str to &UnsafeSerializedAtom is safe.
        unsafe { &*(data as *const str as *const SafelySerializedAtom) }
    }
}

fn serialize_escaped_str<W: io::Write>(mut w: W, s: &str) -> io::Result<()> {
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
                    serialize_hex_byte(&mut w, ch as u32 as u8)?;
                }
                _ => write!(w, "{}", ch)?,
            }
        } else {
            if is_debug_printable_non_ascii_char(ch) {
                write!(w, "{}", ch)?;
            } else {
                let mut utf8_bytes = [0; 4];
                for b in ch.encode_utf8(&mut utf8_bytes).as_bytes() {
                    serialize_hex_byte(&mut w, *b)?;
                }
            }
        }
    }

    Ok(())
}

fn is_debug_printable_non_ascii_char(ch: char) -> bool {
    ch.escape_debug().count() == 1
}

fn serialize_hex_byte<W: io::Write>(mut w: W, b: u8) -> io::Result<()> {
    write!(w, "\\x{:02x}", b)
}

fn serialize_hex_bytes<W: io::Write>(mut w: W, bytes: &[u8]) -> io::Result<()> {
    for b in bytes.iter() {
        write!(w, "\\x{:02x}", b)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use insta::assert_snapshot;

    fn needs_to_be_quoted(bytes: &[u8]) -> bool {
        AtomData::new(bytes).needs_to_be_quoted()
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
        let atom = AtomData::new(bytes);
        atom.serialize_io(&mut buf).unwrap();
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
