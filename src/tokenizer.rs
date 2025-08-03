use std::borrow::Cow;
use std::collections::VecDeque;
use std::io;
use std::ops::Range;

use crate::input::{Input, InputChunk, InputRef};

// Someday: This should maybe be called `DataToken` (as opposed to `DocToken`, which
// would include comments?
#[derive(Debug)]
pub enum Token<'de> {
    LeftParen,
    Atom(Cow<'de, [u8]>),
    RightParen,
}

pub trait TokenIterator<'de> {
    fn next(&mut self) -> io::Result<Option<Token<'de>>>;

    fn peek(&mut self) -> io::Result<Option<&Token<'de>>>;
}

#[derive(Copy, Clone, Debug)]
pub enum VarTokenKind {
    Atom,
    LineComment,
    BlockComment,
}

pub enum RawToken<'de, 't> {
    LeftParen,
    RightParen,
    Atom(InputRef<'de, 't>),
    LineComment(InputRef<'de, 't>),
    BlockComment(InputRef<'de, 't>),
    SexpComment,
}

impl<'de, 't> RawToken<'de, 't> {
    fn from_token_bytes_and_kind(
        token_bytes: InputRef<'de, 't>,
        kind: VarTokenKind,
    ) -> RawToken<'de, 't> {
        match kind {
            VarTokenKind::Atom => RawToken::Atom(token_bytes),
            VarTokenKind::LineComment => RawToken::LineComment(token_bytes),
            VarTokenKind::BlockComment => RawToken::BlockComment(token_bytes),
        }
    }
}

#[derive(Debug)]
enum RawTokenRefData {
    Range(Range<usize>),
    Scratch,
}

#[derive(Debug)]
enum RawTokenRef {
    LeftParen,
    RightParen,
    SexpComment,
    VarToken(RawTokenRefData, VarTokenKind),
}

// Sexplib lexer: https://github.com/janestreet/sexplib/blob/master/src/lexer.mll
//
// Rules:
// - Special characters:
//   - Parentheses: '(' and ')'
//   - Start of line comment: ';'
//   - Start of quoted atom: '"'
//   - Whitespace:
//     - Space: ' '
//     - Tab: '\t' (hex: 0x09)
//     - Newline: '\n' (hex: 0x0a)
//     - CRLF: "\r\n" (hex: 0x0d 0x0a)
//     - Naked carriage returns (0x0d) are a lexer ERROR
// - Unquoted atoms:
//   - Backslashes ('\\') do nothing (just another character)
//   - Cannot contain '#|' or '|#' (start or end of block comment)
//   - A '#;' in an unquoted atom is treated as end of atom and then a line comment
// - Quoted atoms:
//   - Backslash escapes:
//     - character escapes: \ ' " (backlash, single/double quote)
//     - control escapes: n t b r (newline, tab, backspace, tab)
//     - decimal escape: \ddd -> ddd (in decimal) as a byte
//       - it is a _lexer_ error if ddd > 255 (this seems silly; we won't do this)
//     - hexadecimal escape: \xhh -> hh (in hexadecimal) as a byte
//     - line wrapping escape: \ (Newline or CRLF) (Space or tab)
//       - these bytes are totally ignored by the parser
//     - a backslash followed by any other character is just treated as
//       a literal backslash and then that character
//   - Newlines (0x0a) do not get special treatment
//     - CRLF is also not special
//     - Naked carriage returns (0x0d) are permitted
// - Line comments:
//   - Start with ';', go until newline or CRLF
// - Sexp comment: "#;"
//   - Immediately goes back to start state
//   - Within an unquoted atom, '#' is treated as part of the atom + line comment
// - Block comments:
//   - Start with "#|", end with "|#"
//   - Can be nested
//   - Strings within quoted atoms follow exact same escaping rules as normal quoted atoms
//   - Naked carriage returns _are_ allowed

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum TokenizationState {
    Start,
    CarriageReturn,
    InUnquotedAtom,
    InUnquotedAtomPoundSign,
    InUnquotedAtomBar,
    InQuotedAtom,
    InQuotedAtomEscape,
    LineComment,
    PoundSign,
    Bar,
    BlockComment,
    BlockCommentPoundSign,
    BlockCommentBar,
    BlockCommentInQuotedString,
    BlockCommentInQuotedStringEscape,
}

struct TokenizerInner {
    // None when done tokenizing.
    // Someday: indicate EOF vs error states separately?
    state: Option<TokenizationState>,
    scratch_buffer_for_a_previous_token: Vec<u8>,
    scratch_buffer_for_current_token: Vec<u8>,
    using_scratch_buffer_for_current_token: bool,
    raw_token_refs: VecDeque<Result<RawTokenRef, Error>>,
    // byte_offset: u64,
    // line_num: u64,
    // col_num: u64,
    block_comment_depth: i64,
    // Only valid during one iteration
    start_of_current_token: usize,
}

pub struct Tokenizer<I> {
    input: I,
    inner: TokenizerInner,
}

#[derive(Debug)]
pub enum Error {
    NakedCarriageReturn,
    BlockCommentStartTokenInUnquotedAtom,
    BlockCommentEndTokenInUnquotedAtom,
    UnexpectedEndOfBlockComment,
    UnexpectedEofWhileInInQuotedAtom,
    UnexpectedEofWhileInBlockComment,
    TriedToProcessMoreDataAfterEof,
    EofCalledMultipleTimes,
}

macro_rules! whitespace {
    () => {
        b' ' | b'\n' | b'\t' | b'\x0c'
    };
}

impl<I> Tokenizer<I> {
    pub fn new(input: I) -> Tokenizer<I> {
        Tokenizer {
            input,
            inner: TokenizerInner {
                state: Some(TokenizationState::Start),
                scratch_buffer_for_a_previous_token: vec![],
                scratch_buffer_for_current_token: vec![],
                using_scratch_buffer_for_current_token: false,
                raw_token_refs: VecDeque::new(),
                // byte_offset: 0,
                // line_num: 1,
                // col_num: 0,
                block_comment_depth: 0,
                start_of_current_token: 0,
            },
        }
    }
}

impl<'de, I> Tokenizer<I>
where
    I: Input<'de>,
{
    pub fn next_token<'t>(&'t mut self) -> Result<Option<RawToken<'de, 't>>, Error> {
        while self.inner.need_more_data_to_produce_tokens() {
            match self.input.next_chunk() {
                InputChunk::Data(chunk) => self.inner.process_more_data(chunk),
                InputChunk::Eof => self.inner.eof(),
            }
        }

        match self.inner.raw_token_refs.pop_front() {
            None => Ok(None),
            Some(Err(error)) => Err(error),
            Some(Ok(raw_token_ref)) => {
                let raw_token = match raw_token_ref {
                    RawTokenRef::LeftParen => RawToken::LeftParen,
                    RawTokenRef::RightParen => RawToken::RightParen,
                    RawTokenRef::SexpComment => RawToken::SexpComment,
                    RawTokenRef::VarToken(raw_token_ref_data, token_kind) => {
                        let raw_token_bytes = match raw_token_ref_data {
                            RawTokenRefData::Scratch => InputRef::Transient(
                                self.inner.scratch_buffer_for_a_previous_token.as_slice(),
                            ),
                            RawTokenRefData::Range(range) => self.input.last_chunk().index(range),
                        };

                        RawToken::from_token_bytes_and_kind(raw_token_bytes, token_kind)
                    }
                };

                Ok(Some(raw_token))
            }
        }
    }
}

impl TokenizerInner {
    fn need_more_data_to_produce_tokens(&self) -> bool {
        self.raw_token_refs.is_empty() && self.state.is_some()
    }

    fn start_new_token(&mut self, pos: usize, state: TokenizationState) {
        self.using_scratch_buffer_for_current_token = false;
        self.start_of_current_token = pos;
        self.state = Some(state);
    }

    fn copy_partial_token_to_scratch_buffer(&mut self, buffer: &[u8]) {
        let partial_token = &buffer[self.start_of_current_token..];
        if !self.using_scratch_buffer_for_current_token {
            self.scratch_buffer_for_current_token.clear();
            self.using_scratch_buffer_for_current_token = true;
        }
        self.scratch_buffer_for_current_token
            .extend_from_slice(partial_token);
    }

    fn finish_token(&mut self, kind: VarTokenKind, ends_before: usize, buffer: &[u8]) {
        let range = self.start_of_current_token..ends_before;
        let raw_token_ref_data = if self.using_scratch_buffer_for_current_token {
            let partial_token = &buffer[range];
            self.scratch_buffer_for_current_token
                .extend_from_slice(partial_token);
            self.complete_token_in_scratch_buffer();
            RawTokenRefData::Scratch
        } else {
            RawTokenRefData::Range(range)
        };

        self.raw_token_refs
            .push_back(Ok(RawTokenRef::VarToken(raw_token_ref_data, kind)));
    }

    fn complete_token_in_scratch_buffer(&mut self) {
        // Make the scratch buffer for the current token into the scratch
        // buffer for a previous token.
        std::mem::swap(
            &mut self.scratch_buffer_for_a_previous_token,
            &mut self.scratch_buffer_for_current_token,
        );
        self.scratch_buffer_for_current_token.clear();
    }

    pub fn process_more_data(&mut self, buffer: &[u8]) {
        // Immediately return if no data to process
        if buffer.is_empty() {
            return;
        }

        if self.state.is_none() {
            self.raw_token_refs
                .push_back(Err(Error::TriedToProcessMoreDataAfterEof));
            return;
        };

        self.start_of_current_token = 0;

        for (pos, ch) in buffer.iter().enumerate() {
            // We only ever set `self.state` to `None` in `eof`.
            match self.state.unwrap() {
                TokenizationState::Start => match *ch {
                    whitespace!() => (),
                    b'(' => self.raw_token_refs.push_back(Ok(RawTokenRef::LeftParen)),
                    b')' => self.raw_token_refs.push_back(Ok(RawTokenRef::RightParen)),
                    b'\r' => self.state = Some(TokenizationState::CarriageReturn),
                    b'"' => self.start_new_token(pos, TokenizationState::InQuotedAtom),
                    b';' => self.start_new_token(pos, TokenizationState::LineComment),
                    b'#' => self.start_new_token(pos, TokenizationState::PoundSign),
                    b'|' => self.start_new_token(pos, TokenizationState::Bar),
                    _ => self.start_new_token(pos, TokenizationState::InUnquotedAtom),
                },
                TokenizationState::CarriageReturn => {
                    if *ch != b'\n' {
                        self.raw_token_refs
                            .push_back(Err(Error::NakedCarriageReturn));
                        // Someday: Make `state` be `Eof`, `Error` or `Some`.
                        self.state = None;
                        return;
                    }
                    self.state = Some(TokenizationState::Start);
                }
                TokenizationState::InUnquotedAtom
                | TokenizationState::InUnquotedAtomPoundSign
                | TokenizationState::InUnquotedAtomBar
                | TokenizationState::PoundSign
                | TokenizationState::Bar => match *ch {
                    whitespace!() => {
                        self.finish_token(VarTokenKind::Atom, pos, buffer);
                        self.state = Some(TokenizationState::Start);
                    }
                    b'(' => {
                        self.finish_token(VarTokenKind::Atom, pos, buffer);
                        self.raw_token_refs.push_back(Ok(RawTokenRef::LeftParen));
                        self.state = Some(TokenizationState::Start);
                    }
                    b')' => {
                        self.finish_token(VarTokenKind::Atom, pos, buffer);
                        self.raw_token_refs.push_back(Ok(RawTokenRef::RightParen));
                        self.state = Some(TokenizationState::Start);
                    }
                    b'\r' => {
                        self.finish_token(VarTokenKind::Atom, pos, buffer);
                        self.state = Some(TokenizationState::CarriageReturn);
                    }
                    b'"' => {
                        self.finish_token(VarTokenKind::Atom, pos, buffer);
                        self.start_new_token(pos, TokenizationState::InQuotedAtom);
                    }
                    b';' => match self.state.unwrap() {
                        TokenizationState::PoundSign => {
                            self.raw_token_refs.push_back(Ok(RawTokenRef::SexpComment));
                            self.state = Some(TokenizationState::Start);
                        }
                        _ => {
                            self.finish_token(VarTokenKind::Atom, pos, buffer);
                            self.start_new_token(pos, TokenizationState::LineComment);
                        }
                    },
                    b'#' => match self.state.unwrap() {
                        TokenizationState::InUnquotedAtomBar => {
                            self.raw_token_refs
                                .push_back(Err(Error::BlockCommentEndTokenInUnquotedAtom));
                            self.state = None;
                            return;
                        }
                        TokenizationState::Bar => {
                            self.raw_token_refs
                                .push_back(Err(Error::UnexpectedEndOfBlockComment));
                            self.state = None;
                            return;
                        }
                        _ => self.state = Some(TokenizationState::InUnquotedAtomPoundSign),
                    },
                    b'|' => match self.state.unwrap() {
                        TokenizationState::InUnquotedAtomPoundSign => {
                            self.raw_token_refs
                                .push_back(Err(Error::BlockCommentStartTokenInUnquotedAtom));
                            self.state = None;
                            return;
                        }
                        TokenizationState::PoundSign => {
                            self.state = Some(TokenizationState::BlockComment);
                            self.block_comment_depth = 1;
                        }
                        _ => self.state = Some(TokenizationState::InUnquotedAtomBar),
                    },
                    _ => self.state = Some(TokenizationState::InUnquotedAtom),
                },
                // Processing quoted atoms and quoted strings in block comments is the same
                // (other than what state we return to after the '"' or escaped character).
                TokenizationState::InQuotedAtom | TokenizationState::BlockCommentInQuotedString => {
                    match *ch {
                        b'"' => {
                            if self.state.unwrap() == TokenizationState::InQuotedAtom {
                                self.finish_token(VarTokenKind::Atom, pos + 1, buffer);
                                self.state = Some(TokenizationState::Start);
                            } else {
                                self.state = Some(TokenizationState::BlockComment);
                            }
                        }
                        b'\\' => {
                            if self.state.unwrap() == TokenizationState::InQuotedAtom {
                                self.state = Some(TokenizationState::InQuotedAtomEscape);
                            } else {
                                self.state =
                                    Some(TokenizationState::BlockCommentInQuotedStringEscape);
                            }
                        }
                        _ => (),
                    }
                }
                TokenizationState::InQuotedAtomEscape => {
                    self.state = Some(TokenizationState::InQuotedAtom);
                }
                TokenizationState::BlockCommentInQuotedStringEscape => {
                    self.state = Some(TokenizationState::BlockCommentInQuotedString);
                }
                TokenizationState::LineComment => match *ch {
                    b'\n' => {
                        self.finish_token(VarTokenKind::LineComment, pos, buffer);
                        self.state = Some(TokenizationState::Start);
                    }
                    b'\r' => {
                        self.finish_token(VarTokenKind::LineComment, pos, buffer);
                        self.state = Some(TokenizationState::CarriageReturn);
                    }
                    _ => (),
                },
                TokenizationState::BlockComment => match *ch {
                    b'"' => self.state = Some(TokenizationState::BlockCommentInQuotedString),
                    b'#' => self.state = Some(TokenizationState::BlockCommentPoundSign),
                    b'|' => self.state = Some(TokenizationState::BlockCommentBar),
                    _ => (),
                },
                TokenizationState::BlockCommentPoundSign => match *ch {
                    b'"' => self.state = Some(TokenizationState::BlockCommentInQuotedString),
                    b'#' => self.state = Some(TokenizationState::BlockCommentPoundSign),
                    b'|' => {
                        self.block_comment_depth += 1;
                        self.state = Some(TokenizationState::BlockComment);
                    }
                    _ => self.state = Some(TokenizationState::BlockComment),
                },
                TokenizationState::BlockCommentBar => match *ch {
                    b'"' => self.state = Some(TokenizationState::BlockCommentInQuotedString),
                    b'|' => self.state = Some(TokenizationState::BlockCommentBar),
                    b'#' => {
                        self.block_comment_depth -= 1;
                        if self.block_comment_depth == 0 {
                            self.finish_token(VarTokenKind::BlockComment, pos + 1, buffer);
                            self.state = Some(TokenizationState::Start);
                        } else {
                            self.state = Some(TokenizationState::BlockComment);
                        }
                    }
                    _ => self.state = Some(TokenizationState::BlockComment),
                },
            }
        }

        // If in the middle of a token, output `StartOfToken` or `MiddleOfToken`.
        match self.state.unwrap() {
            TokenizationState::Start | TokenizationState::CarriageReturn => (),
            // Maybe starting an atom; it's fine if we don't end up using this.
            TokenizationState::PoundSign
            // Starting an atom
            | TokenizationState::InUnquotedAtom
            | TokenizationState::InUnquotedAtomPoundSign
            | TokenizationState::InUnquotedAtomBar
            | TokenizationState::Bar
            | TokenizationState::InQuotedAtom
            | TokenizationState::InQuotedAtomEscape
            // Started a line comment
            | TokenizationState::LineComment
            // Started a block comment
            | TokenizationState::BlockComment
            | TokenizationState::BlockCommentPoundSign
            | TokenizationState::BlockCommentBar
            | TokenizationState::BlockCommentInQuotedString
            | TokenizationState::BlockCommentInQuotedStringEscape => {
                self.copy_partial_token_to_scratch_buffer(buffer);
            }
        }
    }

    pub fn eof(&mut self) {
        // Set `self.state` to `None`, indicating that we've seen EOF.
        let Some(final_state) = self.state.take() else {
            self.raw_token_refs
                .push_back(Err(Error::EofCalledMultipleTimes));
            return;
        };

        // If we push a new token when we see EOF, that will always be contained
        // in the scratch buffer.
        let raw_token_ref_data = RawTokenRefData::Scratch;

        let final_token_ref = match final_state {
            TokenizationState::Start => return,
            TokenizationState::InUnquotedAtom
            | TokenizationState::InUnquotedAtomBar
            | TokenizationState::InUnquotedAtomPoundSign
            | TokenizationState::Bar => {
                assert!(self.using_scratch_buffer_for_current_token);
                self.complete_token_in_scratch_buffer();
                Ok(RawTokenRef::VarToken(
                    raw_token_ref_data,
                    VarTokenKind::Atom,
                ))
            }
            TokenizationState::LineComment => {
                assert!(self.using_scratch_buffer_for_current_token);
                self.complete_token_in_scratch_buffer();
                Ok(RawTokenRef::VarToken(
                    raw_token_ref_data,
                    VarTokenKind::LineComment,
                ))
            }
            TokenizationState::PoundSign => {
                assert!(self.using_scratch_buffer_for_current_token);
                self.complete_token_in_scratch_buffer();
                Ok(RawTokenRef::VarToken(
                    raw_token_ref_data,
                    VarTokenKind::Atom,
                ))
            }
            TokenizationState::CarriageReturn => Err(Error::NakedCarriageReturn),
            TokenizationState::InQuotedAtom | TokenizationState::InQuotedAtomEscape => {
                Err(Error::UnexpectedEofWhileInInQuotedAtom)
            }
            TokenizationState::BlockComment
            | TokenizationState::BlockCommentPoundSign
            | TokenizationState::BlockCommentBar
            | TokenizationState::BlockCommentInQuotedString
            | TokenizationState::BlockCommentInQuotedStringEscape => {
                Err(Error::UnexpectedEofWhileInBlockComment)
            }
        };

        self.raw_token_refs.push_back(final_token_ref);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::tests::ExplicitChunksInput;
    use crate::input::{InputRef, SliceInput};

    use bstr::ByteSlice;
    use insta::assert_snapshot;

    use std::fmt::Write;

    fn tokenize_fragments(buffers: &[&'static [u8]]) -> String {
        let input = ExplicitChunksInput::new(buffers);
        let mut tokenizer = Tokenizer::new(input);

        let mut output = String::new();
        let o = &mut output;

        loop {
            let _ = match tokenizer.next_token() {
                Ok(None) => break,
                Ok(Some(raw_token)) => writeln!(o, "{}", format_raw_token(raw_token)),
                Err(err) => writeln!(o, "{}", format_error(err)),
            };
        }

        output
    }

    fn tokenize_str(buffer: &[u8]) -> String {
        let input = SliceInput::new(buffer);
        let mut tokenizer = Tokenizer::new(input);

        let mut output = String::new();
        let o = &mut output;

        loop {
            let _ = match tokenizer.next_token() {
                Ok(None) => break,
                Ok(Some(raw_token)) => writeln!(o, "{}", format_raw_token(raw_token)),
                Err(err) => writeln!(o, "{}", format_error(err)),
            };
        }

        output
    }

    fn format_error(err: Error) -> String {
        format!("ERROR: {:?}", err)
    }

    fn format_raw_token(raw_token: RawToken<'_, '_>) -> String {
        fn borrowed_or_owned(token_bytes: &InputRef<'_, '_>) -> &'static str {
            match token_bytes {
                InputRef::Borrowed(_) => "borrowed",
                InputRef::Transient(_) => "transient",
            }
        }

        match raw_token {
            RawToken::LeftParen => "LeftParen: (".to_owned(),
            RawToken::RightParen => "RightParen: )".to_owned(),
            RawToken::SexpComment => "SexpComment: #;".to_owned(),
            RawToken::Atom(token_bytes) => {
                let ref_kind = borrowed_or_owned(&token_bytes);
                let bytes = token_bytes.as_bstr();
                format!("Atom: {:?} ({})", bytes, ref_kind)
            }
            RawToken::LineComment(token_bytes) => {
                let ref_kind = borrowed_or_owned(&token_bytes);
                let bytes = token_bytes.as_bstr();
                format!("LineComment: {:?} ({})", bytes, ref_kind)
            }
            RawToken::BlockComment(token_bytes) => {
                let ref_kind = borrowed_or_owned(&token_bytes);
                let bytes = token_bytes.as_bstr();
                format!("BlockComment: {:?} ({})", bytes, ref_kind)
            }
        }
    }

    #[test]
    fn test_basics() {
        assert_snapshot!(tokenize_str(b"a bc 123 "), @r#"
        Atom: "a" (borrowed)
        Atom: "bc" (borrowed)
        Atom: "123" (borrowed)
        "#);

        assert_snapshot!(tokenize_str(b"a\"123\"b \"\""), @r#"
        Atom: "a" (borrowed)
        Atom: "\"123\"" (borrowed)
        Atom: "b" (borrowed)
        Atom: "\"\"" (borrowed)
        "#);

        assert_snapshot!(tokenize_str(b"## #a #( #) #\"#\" #\r\n#\n| #;|\n# "), @r###"
        Atom: "##" (borrowed)
        Atom: "#a" (borrowed)
        Atom: "#" (borrowed)
        LeftParen: (
        Atom: "#" (borrowed)
        RightParen: )
        Atom: "#" (borrowed)
        Atom: "\"#\"" (borrowed)
        Atom: "#" (borrowed)
        Atom: "#" (borrowed)
        Atom: "|" (borrowed)
        SexpComment: #;
        Atom: "|" (borrowed)
        Atom: "#" (borrowed)
        "###);

        assert_snapshot!(tokenize_str(b"z#a z#( z#) z#\"#\" z#\r\nz#\n| z#;|\n"), @r##"
        Atom: "z#a" (borrowed)
        Atom: "z#" (borrowed)
        LeftParen: (
        Atom: "z#" (borrowed)
        RightParen: )
        Atom: "z#" (borrowed)
        Atom: "\"#\"" (borrowed)
        Atom: "z#" (borrowed)
        Atom: "z#" (borrowed)
        Atom: "|" (borrowed)
        Atom: "z#" (borrowed)
        LineComment: ";|" (borrowed)
        "##);

        assert_snapshot!(tokenize_str(b"|| |a |( |) |\"|\" |\r\n|\n# |;|\n| "), @r##"
        Atom: "||" (borrowed)
        Atom: "|a" (borrowed)
        Atom: "|" (borrowed)
        LeftParen: (
        Atom: "|" (borrowed)
        RightParen: )
        Atom: "|" (borrowed)
        Atom: "\"|\"" (borrowed)
        Atom: "|" (borrowed)
        Atom: "|" (borrowed)
        Atom: "#" (borrowed)
        Atom: "|" (borrowed)
        LineComment: ";|" (borrowed)
        Atom: "|" (borrowed)
        "##);

        assert_snapshot!(tokenize_str(b"z|a z|( z|) z|\"|\" z|\r\nz|\n# z|;|\n"), @r##"
        Atom: "z|a" (borrowed)
        Atom: "z|" (borrowed)
        LeftParen: (
        Atom: "z|" (borrowed)
        RightParen: )
        Atom: "z|" (borrowed)
        Atom: "\"|\"" (borrowed)
        Atom: "z|" (borrowed)
        Atom: "z|" (borrowed)
        Atom: "#" (borrowed)
        Atom: "z|" (borrowed)
        LineComment: ";|" (borrowed)
        "##);
    }

    #[test]
    fn test_quoted_string_escapes() {
        assert_snapshot!(
            tokenize_str(b"\"\\\n \\n \\123 \\\\ \\x01 \\x0\""),
            @r#"Atom: "\"\\\n \\n \\123 \\\\ \\x01 \\x0\"" (borrowed)"#);
    }

    #[test]
    fn test_line_comments() {
        assert_snapshot!(
            tokenize_str(b";\"\"\n;abc\r\n;\n "),
            @r#"
        LineComment: ";\"\"" (borrowed)
        LineComment: ";abc" (borrowed)
        LineComment: ";" (borrowed)
        "#);
    }

    #[test]
    fn test_block_comments() {
        assert_snapshot!(
            tokenize_str(b"#|a|# _ #|# |# _ #|\"|#\\\"\"|# _ #| #| a |#| |#"),
            @r##"
        BlockComment: "#|a|#" (borrowed)
        Atom: "_" (borrowed)
        BlockComment: "#|# |#" (borrowed)
        Atom: "_" (borrowed)
        BlockComment: "#|\"|#\\\"\"|#" (borrowed)
        Atom: "_" (borrowed)
        BlockComment: "#| #| a |#| |#" (borrowed)
        "##,
        );
    }

    #[test]
    fn test_block_comment_errors() {
        assert_snapshot!(tokenize_str(b"a#|b"), @"ERROR: BlockCommentStartTokenInUnquotedAtom");
        assert_snapshot!(tokenize_str(b"a##|b"), @"ERROR: BlockCommentStartTokenInUnquotedAtom");
        assert_snapshot!(tokenize_str(b"a|#b"), @"ERROR: BlockCommentEndTokenInUnquotedAtom");
        assert_snapshot!(tokenize_str(b"a||#b"), @"ERROR: BlockCommentEndTokenInUnquotedAtom");
        assert_snapshot!(tokenize_str(b"|#"), @"ERROR: UnexpectedEndOfBlockComment");
    }

    #[test]
    fn test_sexp_comments() {
        assert_snapshot!(tokenize_str(b"#; a#;x\n##;y\n"), @r###"
        SexpComment: #;
        Atom: "a#" (borrowed)
        LineComment: ";x" (borrowed)
        Atom: "##" (borrowed)
        LineComment: ";y" (borrowed)
        "###);
    }

    #[test]
    fn test_partial_tokens() {
        assert_snapshot!(
            tokenize_fragments(&[b"abc", b"", b"def", b"ghi "]),
            @r#"Atom: "abcdefghi" (transient)"#,
        );

        assert_snapshot!(
            tokenize_fragments(&[b";abc", b"def", b"ghi\n"]),
            @r#"LineComment: ";abcdefghi" (transient)"#,
        );

        assert_snapshot!(
            tokenize_fragments(&[b"#| abc", b"def", b"ghi |# "]),
            @r##"BlockComment: "#| abcdefghi |#" (transient)"##,
        );
    }

    #[test]
    fn test_handling_of_pounds_across_buffers() {
        // #;
        // #| |#
        // #a
        // ##
        assert_snapshot!(
            tokenize_fragments(&[b"#", b"; #", b"| |# #", b"a #", b"# "]),
            @r###"
        SexpComment: #;
        BlockComment: "#| |#" (transient)
        Atom: "#a" (transient)
        Atom: "##" (transient)
        "###,
        );
    }

    #[test]
    fn test_eof() {
        assert_snapshot!(tokenize_fragments(&[b"a\r"]), @r#"
        Atom: "a" (transient)
        ERROR: NakedCarriageReturn
        "#);

        assert_snapshot!(tokenize_fragments(&[b"a"]), @r#"Atom: "a" (transient)"#);

        assert_snapshot!(tokenize_fragments(&[b"a|"]), @r#"Atom: "a|" (transient)"#);

        assert_snapshot!(tokenize_fragments(&[b"a#"]), @r#"Atom: "a#" (transient)"#);

        assert_snapshot!(tokenize_fragments(&[b"|"]), @r#"Atom: "|" (transient)"#);

        assert_snapshot!(tokenize_fragments(&[b";"]), @r#"LineComment: ";" (transient)"#);

        assert_snapshot!(tokenize_fragments(&[b";"]), @r#"LineComment: ";" (transient)"#);

        assert_snapshot!(tokenize_fragments(&[b"#"]), @r##"Atom: "#" (transient)"##);
    }

    #[test]
    fn test_eof_errors() {
        assert_snapshot!(tokenize_fragments(&[b"#|"]), @"ERROR: UnexpectedEofWhileInBlockComment");
        assert_snapshot!(tokenize_fragments(&[b"#| #"]), @"ERROR: UnexpectedEofWhileInBlockComment");
        assert_snapshot!(tokenize_fragments(&[b"#| |"]), @"ERROR: UnexpectedEofWhileInBlockComment");
        assert_snapshot!(tokenize_fragments(&[b"#| \""]), @"ERROR: UnexpectedEofWhileInBlockComment");
        assert_snapshot!(tokenize_fragments(&[b"#| \"\\"]), @"ERROR: UnexpectedEofWhileInBlockComment");
    }

    #[test]
    fn test_tokenizer() {
        assert_snapshot!(
            tokenize_fragments(&[b"a1 a2", b" a3"]),
            @r#"
        Atom: "a1" (transient)
        Atom: "a2" (transient)
        Atom: "a3" (transient)
        "#,
        );

        assert_snapshot!(
            tokenize_fragments(&[b"abc", b"def", b"ghi"]),
            @r#"Atom: "abcdefghi" (transient)"#,
        );

        assert_snapshot!(
            tokenize_fragments(&[b"; lc1\n ; lc2", b"\n ; lc3"]),
            @r#"
        LineComment: "; lc1" (transient)
        LineComment: "; lc2" (transient)
        LineComment: "; lc3" (transient)
        "#,
        );

        assert_snapshot!(
            tokenize_fragments(&[b"; abc", b"def", b"ghi"]),
            @r#"LineComment: "; abcdefghi" (transient)"#,
        );

        assert_snapshot!(
            tokenize_fragments(&[b"#| bc1 |# #| bc2 ", b"|#"]),
            @r##"
        BlockComment: "#| bc1 |#" (transient)
        BlockComment: "#| bc2 |#" (transient)
        "##,
        );

        assert_snapshot!(
            tokenize_fragments(&[b"#| abc", b"def", b"ghi |#"]),
            @r##"BlockComment: "#| abcdefghi |#" (transient)"##,
        );
    }
}
