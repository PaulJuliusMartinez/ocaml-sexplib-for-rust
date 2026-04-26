use std::fmt;
use std::io;

use crate::error::TokenizationError;
use crate::Ref;

/// This is a wrapper type around the actual data in a sexp atom. If the serialized
/// version of an atom looks like this:
/// ```text
/// "a\"b\nc"
/// ```
/// then the contents raw data inside the `AtomData` is:
/// ```text
/// [ b'a', b'"', b'b', b'\n', b'c']
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct AtomData([u8]);

macro_rules! escape_hex_byte {
    ($w:expr, $b:expr) => {
        write!($w, "\\x{:02x}", $b)
    };
}

impl AtomData {
    pub fn new(data: &[u8]) -> &AtomData {
        // SAFETY: AtomData is just a wrapper around [u8], enforced by #[repr(transparent)],
        // therefore converting &[u8] to &AtomData is safe.
        unsafe { &*(data as *const [u8] as *const AtomData) }
    }

    pub fn bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn serialize_io<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        if self.needs_to_be_quoted() {
            write!(w, "\"")?;
            escape_bytes_io(&mut w, &self.0)?;
            write!(w, "\"")
        } else {
            w.write_all(&self.0)
        }
    }

    pub fn serialize_fmt<W: fmt::Write>(&self, mut w: W) -> fmt::Result {
        if !self.needs_to_be_quoted() {
            // This should always be be the case.
            if let Ok(s) = std::str::from_utf8(self.bytes()) {
                return write!(w, "{}", s);
            }
        }

        write!(w, "\"")?;
        escape_bytes_fmt(&mut w, &self.0)?;
        write!(w, "\"")?;

        Ok(())
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
/// sequences in the data may be invalid (e.g. `"\xfg"`, an invalid hex escape).
///
/// If it is a valid serialization of atom data, it may not be standardized, so regular
/// printable ASCII characters may be unnecessarily escaped, and it may not be valid UTF-8.
///
/// The [`RawToken`] type contains `PlausibleSerializedAtom`s.
#[derive(Debug)]
#[repr(transparent)]
pub struct PlausibleSerializedAtom([u8]);

impl PlausibleSerializedAtom {
    pub fn new(data: &[u8]) -> Result<&PlausibleSerializedAtom, TokenizationError> {
        if data.len() == 0 {
            return Err(TokenizationError::EmptyRawTokenBytes);
        }

        if data[0] == b'"' && (data.len() == 1 || data[data.len() - 1] != b'"') {
            return Err(TokenizationError::UnterminatedQuote);
        }

        // SAFETY: PlausibleSerializedAtom is just a wrapper around [u8], enforced by
        // #[repr(transparent)], therefore converting &[u8] to &PlausibleSerializedAtom is safe.
        Ok(unsafe { &*(data as *const [u8] as *const PlausibleSerializedAtom) })
    }

    pub fn bytes(&self) -> &[u8] {
        &self.0
    }

    /// Valid escape sequences include:
    /// - Literal character escapes \ (backslash), ' (single quote), " (double quote)
    /// - Control character escapes n (newline), t (tab), b (backspace), r (carriage return)
    /// - Decimal escapes: \ddd, where ddd when interpreted in decimal, represents a raw
    ///   byte value (i.e., 0 <= ddd < 256)
    /// - Hexadecimal escape: \xhh, where hh, when interpreted in hexadecimal, represents a
    ///   raw byte value
    /// - Line wrapping escape: \ [newline or CRLF] [spaces or tabs]; these bytes are totally
    ///   ignored and used to wrap long atoms on multiple lines
    /// - Backslashes followed by any other character is interpreted as a literal backslash
    ///   and then that character
    pub fn unescape<'b, 't>(
        &'b self,
        scratch: &'t mut Vec<u8>,
    ) -> Result<Ref<'b, 't, AtomData>, TokenizationError> {
        let bytes = self.bytes();

        if bytes[0] != b'"' {
            return Ok(Ref::Borrowed(AtomData::new(bytes)));
        }

        // Trim quotes
        let mut bytes = &bytes[1..(bytes.len() - 1)];

        // Someday: Use memchr
        let mut next_backslash = bytes.iter().position(|b| *b == b'\\');
        if next_backslash.is_none() {
            return Ok(Ref::Borrowed(AtomData::new(bytes)));
        }

        scratch.clear();

        while let Some(backslash_index) = next_backslash {
            scratch.extend_from_slice(&bytes[..backslash_index]);
            bytes = &bytes[backslash_index..];

            if bytes.len() < 2 {
                return Err(TokenizationError::UnterminatedBackslashEscape);
            }

            let mut bytes_to_skip = 2;
            let escaped_byte = bytes[1];
            match bytes[1] {
                b'\\' | b'\'' | b'"' | b' ' => scratch.push(escaped_byte),
                b'n' => scratch.push(b'\n'),
                b't' => scratch.push(b'\t'),
                b'b' => scratch.push(b'\x08'),
                b'r' => scratch.push(b'\r'),
                b'x' => {
                    if bytes.len() < 4 {
                        return Err(TokenizationError::UnterminatedHexadecimalEscape);
                    }

                    bytes_to_skip = 4;
                    let hex_value = Self::parse_hex_escape(bytes[2], bytes[3])?;
                    scratch.push(hex_value);
                }
                _ if escaped_byte.is_ascii_digit() => {
                    if bytes.len() < 4 {
                        return Err(TokenizationError::UnterminatedDecimalEscape);
                    }

                    bytes_to_skip = 4;
                    let decimal_value = Self::parse_decimal_escape(bytes[1], bytes[2], bytes[3])?;
                    scratch.push(decimal_value);
                }
                _ => {
                    if escaped_byte == b'\n'
                        || (escaped_byte == b'\r' && bytes.len() >= 3 && bytes[2] == b'\n')
                    {
                        if escaped_byte == b'\r' {
                            bytes_to_skip += 1;
                        }

                        while bytes_to_skip < bytes.len()
                            && (bytes[bytes_to_skip] == b' ' || bytes[bytes_to_skip] == b'\t')
                        {
                            bytes_to_skip += 1;
                        }
                    } else {
                        // Technically in this case we aren't actually unescaping anything,
                        // so we could return `Borrowed` if this was the only
                        // case we hit.
                        scratch.push(b'\\');
                        scratch.push(escaped_byte);
                    }
                }
            }

            bytes = &bytes[bytes_to_skip..];
            next_backslash = bytes.iter().position(|b| *b == b'\\');
        }

        scratch.extend_from_slice(bytes);

        Ok(Ref::Transient(AtomData::new(scratch.as_slice())))
    }

    /// Validate that an atom is valid.
    pub fn validate(&self) -> std::result::Result<(), TokenizationError> {
        let bytes = self.bytes();

        if bytes[0] != b'"' {
            return Ok(());
        }

        Self::validate_quote_escaping(&bytes[1..(bytes.len() - 1)])
    }

    pub(crate) fn validate_quote_escaping(mut bytes: &[u8]) -> Result<(), TokenizationError> {
        // Someday: Use memchr.
        while let Some(backslash_index) = bytes.iter().position(|b| *b == b'\\') {
            bytes = &bytes[backslash_index..];

            let mut bytes_to_skip = 2;
            if bytes.len() < 2 {
                return Err(TokenizationError::UnterminatedBackslashEscape);
            }

            let escaped_byte = bytes[1];
            match bytes[1] {
                b'\\' | b'\'' | b'"' | b' ' => (), // Literal character escape
                b'n' | b't' | b'b' | b'r' => (),   // Control character escape
                b'x' => {
                    if bytes.len() < 4 {
                        return Err(TokenizationError::UnterminatedHexadecimalEscape);
                    }

                    bytes_to_skip = 4;
                    let _ = Self::parse_hex_escape(bytes[2], bytes[3])?;
                }
                _ if escaped_byte.is_ascii_digit() => {
                    if bytes.len() < 4 {
                        return Err(TokenizationError::UnterminatedDecimalEscape);
                    }

                    bytes_to_skip = 4;
                    let _ = Self::parse_decimal_escape(bytes[1], bytes[2], bytes[3])?;
                }
                _ => (), // Newline / CRLF escapes, and non-escapes
            }

            bytes = &bytes[bytes_to_skip..];
        }

        Ok(())
    }

    fn parse_hex_escape(b1: u8, b2: u8) -> Result<u8, TokenizationError> {
        fn of_hexdigit(b: u8) -> Option<u32> {
            if b.is_ascii() {
                (b as char).to_digit(16)
            } else {
                None
            }
        }

        let h1 = of_hexdigit(b1);
        let h2 = of_hexdigit(b2);

        let (Some(h1), Some(h2)) = (h1, h2) else {
            return Err(TokenizationError::InvalidHexadecimalEscape);
        };

        Ok((h1 * 16 + h2) as u8)
    }

    fn parse_decimal_escape(b1: u8, b2: u8, b3: u8) -> Result<u8, TokenizationError> {
        fn of_digit(b: u8) -> Option<u32> {
            if b.is_ascii_digit() {
                Some((b - b'0') as u32)
            } else {
                None
            }
        }

        let d1 = of_digit(b1);
        let d2 = of_digit(b2);
        let d3 = of_digit(b3);

        let (Some(d1), Some(d2), Some(d3)) = (d1, d2, d3) else {
            return Err(TokenizationError::InvalidDecimalEscape);
        };

        let b = d1 * 100 + d2 * 10 + d3;
        if b > 255 {
            return Err(TokenizationError::OutOfRangeDecimalEscape);
        }

        Ok(b as u8)
    }

    /// For valid atoms, this is the same as `AtomData::serialize_fmt`. Otherwise, invalid
    /// escape sequences will be passed through unchanged (unless they are invalid UTF-8).
    /// Explicitly, the output may still not be a valid serialization.
    pub fn normalize_serialization_even_if_invalid<W: fmt::Write>(&self, mut w: W) -> fmt::Result {
        let bytes = self.bytes();

        if bytes.len() == 0 {
            return write!(w, "\"\"");
        }

        if bytes[0] != b'"' {
            return AtomData::new(&bytes).serialize_fmt(w);
        }

        // Trim quotes
        let mut bytes = &bytes[1..bytes.len() - 1];

        write!(w, "\"")?;

        // Someday: Use memchr
        let mut next_backslash = bytes.iter().position(|b| *b == b'\\');

        while let Some(backslash_index) = next_backslash {
            // Nothing is escaped here, but maybe some of they bytes here should be escaped.
            escape_bytes_fmt(&mut w, &bytes[..backslash_index])?;
            bytes = &bytes[backslash_index + 1..];

            // Unterminated backslash, we'll just keep it like that.
            if bytes.is_empty() {
                write!(w, "\\")?;
                break;
            }

            let mut bytes_to_skip = 1;

            match bytes[0] {
                // These characters can be escaped, but don't need to be
                b'\'' => write!(w, "'")?,
                b' ' => write!(w, " ")?,
                // These do need to be escaped
                b'\\' => write!(w, "\\\\")?,
                b'\"' => write!(w, "\\\"")?,
                // Keep these control character escapes too
                b'n' => write!(w, "\\n")?,
                b't' => write!(w, "\\t")?,
                b'b' => write!(w, "\\b")?,
                b'r' => write!(w, "\\r")?,
                _ => {
                    if bytes[0] == b'x' || bytes[0].is_ascii_digit() {
                        // We'll try to get the escaped byte value out of hex or decimal escape,
                        // but if we can't, we want to pass through the bytes as untouched as
                        // possible, while also preserving some sort of intent of the backslashes.
                        // So something like "\xf\xab" might just be a missed hex character, and
                        // we'll pass it along as is.
                        let escape_sequence = &bytes[0..(usize::min(bytes.len(), 3))];
                        if let Some(another_backslash) =
                            escape_sequence.iter().position(|b| *b == b'\\')
                        {
                            write!(w, "\\")?;
                            bytes_to_skip = another_backslash;
                            escape_bytes_fmt(&mut w, &escape_sequence[0..another_backslash])?;
                        } else {
                            if bytes.len() < 3 {
                                // Incomplete escape sequence (and no backslashes), we'll just
                                // escape them as normal.
                                write!(w, "\\")?;
                                escape_bytes_fmt(&mut w, &*bytes)?;
                                bytes_to_skip = bytes.len()
                            } else {
                                bytes_to_skip = 3;
                                let ch1 = bytes[0];
                                let ch2 = bytes[1];
                                let ch3 = bytes[2];

                                let escaped_byte_val = if ch1 == b'x' {
                                    Self::parse_hex_escape(ch2, ch3).ok()
                                } else {
                                    Self::parse_decimal_escape(ch1, ch2, ch3).ok()
                                };

                                if let Some(escaped_byte_val) = escaped_byte_val {
                                    escape_bytes_fmt(&mut w, &[escaped_byte_val])?;
                                } else {
                                    // Invalid escape, no backslashes; we'll just write it as
                                    // is and move on.
                                    write!(w, "\\")?;
                                    escape_bytes_fmt(&mut w, &bytes[..3])?;
                                }
                            }
                        }
                    } else if bytes[0] == b'\n'
                        || (bytes[0] == b'\r' && bytes.len() > 2 && bytes[1] == b'\n')
                    {
                        // If there's an escaped newline, we'll just strip it out like we do
                        // when normally unescaping.
                        if bytes[0] == b'\r' {
                            bytes_to_skip += 1;
                        }

                        while bytes_to_skip < bytes.len()
                            && (bytes[bytes_to_skip] == b' ' || bytes[bytes_to_skip] == b'\t')
                        {
                            bytes_to_skip += 1;
                        }
                    } else {
                        // Normally this interpreted as a literal backslash and then the next
                        // character. So we want to explicitly escape the backslash, then
                        // escape the next byte.
                        write!(w, "\\\\")?;
                        escape_bytes_fmt(&mut w, &[bytes[0]])?;
                    }
                }
            }

            bytes = &bytes[bytes_to_skip..];
            next_backslash = bytes.iter().position(|b| *b == b'\\');
        }

        escape_bytes_fmt(&mut w, bytes)?;

        write!(w, "\"")
    }
}

macro_rules! escape_bytes {
    ($escape_bytes_fn:ident, $write_trait:path, $write_result:ty) => {
        fn $escape_bytes_fn<W: $write_trait>(mut w: W, bytes: &[u8]) -> $write_result {
            for chunk in bytes.utf8_chunks() {
                // Escape UTF-8 part
                for ch in chunk.valid().chars() {
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
                                escape_hex_byte!(w, ch as u32 as u8)?;
                            }
                            _ => write!(w, "{}", ch)?,
                        }
                    } else {
                        if is_debug_printable_non_ascii_char(ch) {
                            write!(w, "{}", ch)?;
                        } else {
                            let mut utf8_bytes = [0; 4];
                            for b in ch.encode_utf8(&mut utf8_bytes).as_bytes() {
                                escape_hex_byte!(&mut w, *b)?;
                            }
                        }
                    }
                }

                // Hex escape any invalid UTF-8
                for b in chunk.invalid().iter() {
                    escape_hex_byte!(w, b)?;
                }
            }

            Ok(())
        }
    };
}

escape_bytes!(escape_bytes_io, io::Write, io::Result<()>);
escape_bytes!(escape_bytes_fmt, fmt::Write, fmt::Result);

fn is_debug_printable_non_ascii_char(ch: char) -> bool {
    ch.escape_debug().count() == 1
}

#[cfg(test)]
mod tests {
    use super::*;

    use bstr::ByteSlice;
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
        let mut byte_buf = vec![];
        let atom = AtomData::new(bytes);
        atom.serialize_io(&mut byte_buf).unwrap();

        let mut str_buf = String::new();
        atom.serialize_fmt(&mut str_buf).unwrap();

        assert_eq!(byte_buf.as_slice(), str_buf.as_bytes());

        let mut normalized_buf = String::new();
        PlausibleSerializedAtom::new(str_buf.as_bytes())
            .unwrap()
            .normalize_serialization_even_if_invalid(&mut normalized_buf)
            .unwrap();

        assert_eq!(str_buf, normalized_buf);

        str_buf
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

    fn u(bytes: &[u8]) -> String {
        let serialized = match PlausibleSerializedAtom::new(bytes) {
            Ok(serialized) => serialized,
            Err(err) => return format!("> ERROR: {err:?}"),
        };

        let mut scratch = vec![];

        match (serialized.unescape(&mut scratch), serialized.validate()) {
            (Ok(Ref::Borrowed(atom_data)), Ok(())) => {
                format!("> {:?} (no unescaping)", atom_data.bytes().as_bstr())
            }
            (Ok(Ref::Transient(atom_data)), Ok(())) => {
                format!("> {:?} (escaped)", atom_data.bytes().as_bstr())
            }
            (Err(unescape_err), Err(validate_err)) => {
                if unescape_err == validate_err {
                    format!("> ERROR: {:?}", unescape_err)
                } else {
                    panic!(
                        "PlausibleSerializedAtom::unescape and PlausibleSerializedAtom::validate returned different errors.\n  unescape error: {:?}\n  validation error: {:?}\n  raw bytes: {:?}",
                        unescape_err,
                        validate_err,
                        bytes.as_bstr(),
                    );
                }
            }
            (Ok(_), Err(validate_err)) => {
                panic!(
                    "PlausibleSerializedAtom::unescape returned valid data, but PlausibleSerializedAtom::validate returned an error.\n  validation error: {:?}\n  raw bytes: {:?}",
                    validate_err,
                    bytes.as_bstr(),
                );
            }
            (Err(unescape_err), Ok(())) => {
                panic!(
                    "PlausibleSerializedAtom::unescape returned an error, but PlausibleSerializedAtom::validate returned Ok.\n  unescape error: {:?}\n  raw bytes: {:?}",
                    unescape_err,
                    bytes.as_bstr(),
                );
            }
        }
    }

    #[test]
    fn test_unescaping_atoms_basic() {
        assert_snapshot!(u(b""),                     @"> ERROR: EmptyRawTokenBytes");
        assert_snapshot!(u(b"a"),                  @r#"> "a" (no unescaping)"#);
        assert_snapshot!(u(br#"""#),                 @"> ERROR: UnterminatedQuote");
        assert_snapshot!(u(br#""""#),              @r#"> "" (no unescaping)"#);
        assert_snapshot!(u(br#""abc"#),              @"> ERROR: UnterminatedQuote");
        assert_snapshot!(u(br#""\"""#),            @r#"> "\"" (escaped)"#);
        assert_snapshot!(u(br#""a\\ \' \" \ z""#), @r#"> "a\\ \' \"  z" (escaped)"#);
        assert_snapshot!(u(br#""\n \t \b \r""#),   @r#"> "\n \t \x08 \r" (escaped)"#);
        assert_snapshot!(u(b"\"\\\""),              @"> ERROR: UnterminatedBackslashEscape");
    }

    #[test]
    fn test_unescaping_atoms_decimal_escapes() {
        assert_snapshot!(u(br#""\000 \255""#), @r#"> "\0 \xff" (escaped)"#);
        assert_snapshot!(u(br#""a \256""#),      @"> ERROR: OutOfRangeDecimalEscape");
        assert_snapshot!(u(br#""a \999""#),      @"> ERROR: OutOfRangeDecimalEscape");
        assert_snapshot!(u(br#""a \99""#),       @"> ERROR: UnterminatedDecimalEscape");
    }

    #[test]
    fn test_unescaping_atoms_hexadecimal_escapes() {
        assert_snapshot!(u(br#""\x00 \xab \xFF""#), @r#"> "\0 \xab \xff" (escaped)"#);
        assert_snapshot!(u(br#""\x0""#),              @"> ERROR: UnterminatedHexadecimalEscape");
        assert_snapshot!(u(br#""\xgg""#),             @"> ERROR: InvalidHexadecimalEscape");
    }

    #[test]
    fn test_unescaping_atoms_newline_escapes() {
        // Spaces after escape newline or CRLF (but not raw `\r`) are removed.
        assert_snapshot!(u(b"\"abc\\\n   z\""),   @r#"> "abcz" (escaped)"#);
        assert_snapshot!(u(b"\"abc\\\r\n   z\""), @r#"> "abcz" (escaped)"#);
        assert_snapshot!(u(b"\"abc\r   z\""),     @r#"> "abc\r   z" (no unescaping)"#);
        assert_snapshot!(u(b"\"abc\\\r   z\""),   @r#"> "abc\\\r   z" (escaped)"#);
        assert_snapshot!(u(b"\"abc\\\rd  z\""),   @r#"> "abc\\\rd  z" (escaped)"#);
        assert_snapshot!(u(b"\"abc\\\r\""),       @r#"> "abc\\\r" (escaped)"#);
    }

    #[test]
    fn test_unescape_atom_non_escapes_still_use_scratch_space() {
        // We could return the original data here, but this case is probably rare.
        assert_snapshot!(u(b"\"\\a\""), @r#"> "\\a" (escaped)"#);
    }

    #[test]
    fn test_unescape_atom_assumes_validation_from_raw_tokenizer() {
        // If not quoted, might have spaces
        assert_snapshot!(u(b" "), @r#"> " " (no unescaping)"#);
    }

    #[test]
    fn test_normalize_serialization() {
        fn n(unnormalized_bytes: &[u8]) -> String {
            let unnormalized_atom = PlausibleSerializedAtom::new(unnormalized_bytes).unwrap();
            let mut s = String::new();
            unnormalized_atom
                .normalize_serialization_even_if_invalid(&mut s)
                .unwrap();
            s
        }

        assert_eq!(n(br#""""#), r#""""#);
        assert_eq!(n(br#""\\\""#), r#""\\\""#);

        // Unnecessary escapes:
        assert_eq!(n(br#""a\ b\'c""#), "\"a b'c\"");
        assert_eq!(n(br#""\n\t\b\r""#), "\"\\n\\t\\b\\r\"");
        assert_eq!(n(br#""a\x20b\032c""#), "\"a b c\"");

        // Invalid hex escape:
        assert_eq!(n(br#""\x""#), "\"\\x\"");
        assert_eq!(n(br#""\xa""#), "\"\\xa\"");
        assert_eq!(n(b"\"\\x\xa0\""), "\"\\x\\xa0\"");
        assert_eq!(n(b"\"\\xf\xa0\""), "\"\\xf\\xa0\"");
        assert_eq!(n(br#""\xfg""#), "\"\\xfg\"");

        // Process the \x20 escape as a space.
        assert_eq!(n(br#""\xf\x20""#), "\"\\xf \"");

        // Invalid decimal escape:
        assert_eq!(n(br#""\9""#), "\"\\9\"");
        assert_eq!(n(br#""\8a""#), "\"\\8a\"");
        assert_eq!(n(b"\"\\7\xa0\""), "\"\\7\\xa0\"");
        assert_eq!(n(b"\"\\76\xa0\""), "\"\\76\\xa0\"");
        assert_eq!(n(br#""\256""#), "\"\\256\"");

        // Escaped newlines removed:
        assert_eq!(n(b"\"\\x a\\\n \tb\""), "\"\\x ab\"");
        assert_eq!(n(b"\"\\x a\\\r\n \t  b\""), "\"\\x ab\"");

        // Backslash non-escapes get made explicit:
        assert_eq!(n(b"\"\\a\\\xa0\""), r#""\\a\\\xa0""#);
    }
}
