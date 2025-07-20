use std::borrow::Cow;
use std::io;

// Someday: This should maybe be called `DataToken` (as opposed to `DocToken`, which
// would include comments?
#[derive(Debug)]
pub enum Token<'de> {
    LeftParen,
    Atom(&'de [u8]),
    RightParen,
}

pub trait TokenIterator<'de> {
    fn next(&mut self) -> io::Result<Option<Token<'de>>>;

    fn peek(&mut self) -> io::Result<Option<&Token<'de>>>;
}

pub enum RawToken<'de> {
    LeftParen,
    RightParen,
    Atom(Cow<'de, [u8]>),
    LineComment(Cow<'de, [u8]>),
    BlockComment(Cow<'de, [u8]>),
    SexpComment,
}

impl<'de> RawToken<'de> {
    fn from_data_and_kind(data: Cow<'de, [u8]>, kind: VariableLengthTokenKind) -> RawToken<'de> {
        match kind {
            VariableLengthTokenKind::Atom => RawToken::Atom(data),
            VariableLengthTokenKind::LineComment => RawToken::LineComment(data),
            VariableLengthTokenKind::BlockComment => RawToken::BlockComment(data),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum VariableLengthTokenKind {
    Atom,
    LineComment,
    BlockComment,
}

pub enum RawTokenFragment<'de> {
    LeftParen,
    RightParen,
    Atom(&'de [u8]),
    LineComment(&'de [u8]),
    BlockComment(&'de [u8]),
    SexpComment,
    StartOfToken(&'de [u8], VariableLengthTokenKind),
    MiddleOfToken(&'de [u8]),
    EndOfToken(&'de [u8]),
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

pub struct StreamingFragmentTokenizer {
    state: TokenizationState,
    byte_offset: u64,
    line_num: u64,
    col_num: u64,
    block_comment_depth: i64,
    already_emitted_start_of_current_token: bool,
    // Only valid during one iteration
    start_of_current_token: usize,
}

#[derive(Debug)]
pub enum Error {
    NakedCarriageReturn,
    BlockCommentStartTokenInUnquotedAtom,
    BlockCommentEndTokenInUnquotedAtom,
    UnexpectedEndOfBlockComment,
    UnexpectedEofWhileInInQuotedAtom,
    UnexpectedEofWhileInBlockComment,
    // Returned by `StreamingTokenizer`
    UnexpectedTokenContinuation,
    UnexpectedTokenStartStillProcessingPreviousToken,
    UnexpectedEofWhileConstructingTokenFragments,
}

macro_rules! whitespace {
    () => {
        b' ' | b'\n' | b'\t' | b'\x0c'
    };
}

impl StreamingFragmentTokenizer {
    pub fn new() -> StreamingFragmentTokenizer {
        StreamingFragmentTokenizer {
            state: TokenizationState::Start,
            byte_offset: 0,
            line_num: 1,
            col_num: 0,
            block_comment_depth: 0,
            already_emitted_start_of_current_token: false,
            start_of_current_token: 0,
        }
    }

    fn start_new_token(&mut self, pos: usize, state: TokenizationState) {
        self.already_emitted_start_of_current_token = false;
        self.start_of_current_token = pos;
        self.state = state;
    }

    fn fragment<'st, 'de>(&'st self, buffer: &'de [u8], ends_before: usize) -> &'de [u8] {
        &buffer[self.start_of_current_token..ends_before]
    }

    fn finish_atom<'st, 'de>(
        &'st mut self,
        buffer: &'de [u8],
        ends_before: usize,
        tokens: &mut Vec<Result<RawTokenFragment<'de>, Error>>,
    ) {
        let atom = self.fragment(buffer, ends_before);
        if self.already_emitted_start_of_current_token {
            tokens.push(Ok(RawTokenFragment::EndOfToken(atom)));
        } else {
            tokens.push(Ok(RawTokenFragment::Atom(atom)));
        }
    }

    fn finish_line_comment<'st, 'de>(
        &'st mut self,
        buffer: &'de [u8],
        ends_before: usize,
        tokens: &mut Vec<Result<RawTokenFragment<'de>, Error>>,
    ) {
        let line_comment = self.fragment(buffer, ends_before);
        if self.already_emitted_start_of_current_token {
            tokens.push(Ok(RawTokenFragment::EndOfToken(line_comment)));
        } else {
            tokens.push(Ok(RawTokenFragment::LineComment(line_comment)));
        }
    }

    fn finish_block_comment<'st, 'de>(
        &'st mut self,
        buffer: &'de [u8],
        ends_before: usize,
        tokens: &mut Vec<Result<RawTokenFragment<'de>, Error>>,
    ) {
        let block_comment = self.fragment(buffer, ends_before);
        if self.already_emitted_start_of_current_token {
            tokens.push(Ok(RawTokenFragment::EndOfToken(block_comment)));
        } else {
            tokens.push(Ok(RawTokenFragment::BlockComment(block_comment)));
        }
    }

    fn start_or_continue_token<'st, 'de>(
        &'st mut self,
        kind: VariableLengthTokenKind,
        buffer: &'de [u8],
        tokens: &mut Vec<Result<RawTokenFragment<'de>, Error>>,
    ) {
        let fragment = &buffer[self.start_of_current_token..];
        if self.already_emitted_start_of_current_token {
            tokens.push(Ok(RawTokenFragment::MiddleOfToken(fragment)));
        } else {
            tokens.push(Ok(RawTokenFragment::StartOfToken(fragment, kind)));
            self.already_emitted_start_of_current_token = true;
        }
    }

    pub fn iter_raw_token_fragments<'st, 'de>(
        &'st mut self,
        mut buffer: &'de [u8],
    ) -> impl Iterator<Item = Result<RawTokenFragment<'de>, Error>> {
        // Immediately return if no data to process
        if buffer.is_empty() {
            return vec![].into_iter();
        }

        let mut tokens = vec![];

        // Handle leftover state and possibly emit a token for the last character
        // we saw, based on peeking at the next char.
        if self.state == TokenizationState::PoundSign {
            match buffer[0] {
                b';' => {
                    tokens.push(Ok(RawTokenFragment::SexpComment));
                    // Don't process ';' again
                    buffer = &buffer[1..];
                    self.state = TokenizationState::Start;
                }
                b'|' => {
                    tokens.push(Ok(RawTokenFragment::StartOfToken(
                        b"#",
                        VariableLengthTokenKind::BlockComment,
                    )));
                    self.state = TokenizationState::BlockComment;
                    self.block_comment_depth = 1;
                    self.already_emitted_start_of_current_token = true;
                }
                _ => {
                    tokens.push(Ok(RawTokenFragment::StartOfToken(
                        b"#",
                        VariableLengthTokenKind::Atom,
                    )));
                    self.state = TokenizationState::InUnquotedAtomPoundSign;
                    self.already_emitted_start_of_current_token = true;
                }
            }
        }

        self.start_of_current_token = 0;

        for (pos, ch) in buffer.iter().enumerate() {
            eprintln!(
                "iter {}: ch {:?}, state: {:?}",
                pos, *ch as char, self.state
            );
            match self.state {
                TokenizationState::Start => match *ch {
                    whitespace!() => (),
                    b'(' => tokens.push(Ok(RawTokenFragment::LeftParen)),
                    b')' => tokens.push(Ok(RawTokenFragment::RightParen)),
                    b'\r' => self.state = TokenizationState::CarriageReturn,
                    b'"' => self.start_new_token(pos, TokenizationState::InQuotedAtom),
                    b';' => self.start_new_token(pos, TokenizationState::LineComment),
                    b'#' => self.start_new_token(pos, TokenizationState::PoundSign),
                    b'|' => self.start_new_token(pos, TokenizationState::Bar),
                    _ => self.start_new_token(pos, TokenizationState::InUnquotedAtom),
                },
                TokenizationState::CarriageReturn => {
                    if *ch != b'\n' {
                        tokens.push(Err(Error::NakedCarriageReturn));
                        return tokens.into_iter();
                    }
                    self.state = TokenizationState::Start;
                }
                TokenizationState::InUnquotedAtom
                | TokenizationState::InUnquotedAtomPoundSign
                | TokenizationState::InUnquotedAtomBar
                | TokenizationState::PoundSign
                | TokenizationState::Bar => match *ch {
                    whitespace!() => {
                        self.finish_atom(buffer, pos, &mut tokens);
                        self.state = TokenizationState::Start;
                    }
                    b'(' => {
                        self.finish_atom(buffer, pos, &mut tokens);
                        tokens.push(Ok(RawTokenFragment::LeftParen));
                        self.state = TokenizationState::Start;
                    }
                    b')' => {
                        self.finish_atom(buffer, pos, &mut tokens);
                        tokens.push(Ok(RawTokenFragment::RightParen));
                        self.state = TokenizationState::Start;
                    }
                    b'\r' => {
                        self.finish_atom(buffer, pos, &mut tokens);
                        self.state = TokenizationState::CarriageReturn;
                    }
                    b'"' => {
                        self.finish_atom(buffer, pos, &mut tokens);
                        self.start_new_token(pos, TokenizationState::InQuotedAtom);
                    }
                    b';' => match self.state {
                        TokenizationState::PoundSign => {
                            tokens.push(Ok(RawTokenFragment::SexpComment));
                            self.state = TokenizationState::Start;
                        }
                        _ => {
                            self.finish_atom(buffer, pos, &mut tokens);
                            self.start_new_token(pos, TokenizationState::LineComment);
                        }
                    },
                    b'#' => match self.state {
                        TokenizationState::InUnquotedAtomBar => {
                            tokens.push(Err(Error::BlockCommentEndTokenInUnquotedAtom));
                            return tokens.into_iter();
                        }
                        TokenizationState::Bar => {
                            tokens.push(Err(Error::UnexpectedEndOfBlockComment));
                            return tokens.into_iter();
                        }
                        _ => self.state = TokenizationState::InUnquotedAtomPoundSign,
                    },
                    b'|' => match self.state {
                        TokenizationState::InUnquotedAtomPoundSign => {
                            tokens.push(Err(Error::BlockCommentStartTokenInUnquotedAtom));
                            return tokens.into_iter();
                        }
                        TokenizationState::PoundSign => {
                            self.state = TokenizationState::BlockComment;
                            self.block_comment_depth = 1;
                        }
                        _ => self.state = TokenizationState::InUnquotedAtomBar,
                    },
                    _ => self.state = TokenizationState::InUnquotedAtom,
                },
                // Processing quoted atoms and quoted strings in block comments is the same
                // (other than what state we return to after the '"' or escaped character).
                TokenizationState::InQuotedAtom | TokenizationState::BlockCommentInQuotedString => {
                    match *ch {
                        b'"' => {
                            if self.state == TokenizationState::InQuotedAtom {
                                self.finish_atom(buffer, pos + 1, &mut tokens);
                                self.state = TokenizationState::Start;
                            } else {
                                self.state = TokenizationState::BlockComment;
                            }
                        }
                        b'\\' => {
                            if self.state == TokenizationState::InQuotedAtom {
                                self.state = TokenizationState::InQuotedAtomEscape;
                            } else {
                                self.state = TokenizationState::BlockCommentInQuotedStringEscape;
                            }
                        }
                        _ => (),
                    }
                }
                TokenizationState::InQuotedAtomEscape => {
                    self.state = TokenizationState::InQuotedAtom;
                }
                TokenizationState::BlockCommentInQuotedStringEscape => {
                    self.state = TokenizationState::BlockCommentInQuotedString;
                }
                TokenizationState::LineComment => match *ch {
                    b'\n' => {
                        self.finish_line_comment(buffer, pos, &mut tokens);
                        self.state = TokenizationState::Start;
                    }
                    b'\r' => {
                        self.finish_line_comment(buffer, pos, &mut tokens);
                        self.state = TokenizationState::CarriageReturn;
                    }
                    _ => (),
                },
                TokenizationState::BlockComment => match *ch {
                    b'"' => self.state = TokenizationState::BlockCommentInQuotedString,
                    b'#' => self.state = TokenizationState::BlockCommentPoundSign,
                    b'|' => self.state = TokenizationState::BlockCommentBar,
                    _ => (),
                },
                TokenizationState::BlockCommentPoundSign => match *ch {
                    b'"' => self.state = TokenizationState::BlockCommentInQuotedString,
                    b'#' => self.state = TokenizationState::BlockCommentPoundSign,
                    b'|' => {
                        self.block_comment_depth += 1;
                        self.state = TokenizationState::BlockComment;
                    }
                    _ => self.state = TokenizationState::BlockComment,
                },
                TokenizationState::BlockCommentBar => match *ch {
                    b'"' => self.state = TokenizationState::BlockCommentInQuotedString,
                    b'|' => self.state = TokenizationState::BlockCommentBar,
                    b'#' => {
                        self.block_comment_depth -= 1;
                        if self.block_comment_depth == 0 {
                            self.finish_block_comment(buffer, pos + 1, &mut tokens);
                            self.state = TokenizationState::Start;
                        } else {
                            self.state = TokenizationState::BlockComment;
                        }
                    }
                    _ => self.state = TokenizationState::BlockComment,
                },
            }
        }

        eprintln!("Done with buffer, state: {:?}", self.state);

        // If in the middle of a token, output `StartOfToken` or `MiddleOfToken`.
        match self.state {
            TokenizationState::Start | TokenizationState::CarriageReturn => (),
            // We *don't* write a `StartOfToken` in this state, since we don't
            // know yet if it's a block comment, sexp comment, or a regular atom.
            TokenizationState::PoundSign => (),
            // These are all the start of an atom
            TokenizationState::InUnquotedAtom
            | TokenizationState::InUnquotedAtomPoundSign
            | TokenizationState::InUnquotedAtomBar
            | TokenizationState::Bar
            | TokenizationState::InQuotedAtom
            | TokenizationState::InQuotedAtomEscape => {
                self.start_or_continue_token(VariableLengthTokenKind::Atom, buffer, &mut tokens);
            }
            // Started a line comment
            TokenizationState::LineComment => {
                self.start_or_continue_token(
                    VariableLengthTokenKind::LineComment,
                    buffer,
                    &mut tokens,
                );
            }
            TokenizationState::BlockComment
            | TokenizationState::BlockCommentPoundSign
            | TokenizationState::BlockCommentBar
            | TokenizationState::BlockCommentInQuotedString
            | TokenizationState::BlockCommentInQuotedStringEscape => {
                self.start_or_continue_token(
                    VariableLengthTokenKind::BlockComment,
                    buffer,
                    &mut tokens,
                );
            }
        }

        tokens.into_iter()
    }

    pub fn eof(self) -> Result<Option<RawTokenFragment<'static>>, Error> {
        match self.state {
            TokenizationState::Start => Ok(None),
            TokenizationState::CarriageReturn => Err(Error::NakedCarriageReturn),
            TokenizationState::InUnquotedAtom
            | TokenizationState::InUnquotedAtomBar
            | TokenizationState::InUnquotedAtomPoundSign
            | TokenizationState::Bar
            | TokenizationState::LineComment => Ok(Some(RawTokenFragment::EndOfToken(b""))),
            TokenizationState::PoundSign => Ok(Some(RawTokenFragment::Atom(b"#"))),
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
        }
    }
}

pub struct StreamingTokenizer {
    fragment_tokenizer: StreamingFragmentTokenizer,
    current_reconstructed_token: Option<(Vec<u8>, VariableLengthTokenKind)>,
}

impl StreamingTokenizer {
    pub fn new() -> StreamingTokenizer {
        StreamingTokenizer {
            fragment_tokenizer: StreamingFragmentTokenizer::new(),
            current_reconstructed_token: None,
        }
    }

    pub fn iter_raw_tokens<'st, 'de>(
        &'st mut self,
        buffer: &'de [u8],
    ) -> impl Iterator<Item = Result<RawToken<'de>, Error>> {
        let mut tokens = vec![];

        for raw_token_fragment in self.fragment_tokenizer.iter_raw_token_fragments(buffer) {
            match raw_token_fragment {
                Err(error) => tokens.push(Err(error)),
                Ok(RawTokenFragment::LeftParen) => tokens.push(Ok(RawToken::LeftParen)),
                Ok(RawTokenFragment::RightParen) => tokens.push(Ok(RawToken::RightParen)),
                Ok(RawTokenFragment::SexpComment) => tokens.push(Ok(RawToken::SexpComment)),
                Ok(RawTokenFragment::Atom(atom)) => {
                    tokens.push(Ok(RawToken::Atom(Cow::Borrowed(atom))))
                }
                Ok(RawTokenFragment::LineComment(line_comment)) => {
                    tokens.push(Ok(RawToken::LineComment(Cow::Borrowed(line_comment))))
                }
                Ok(RawTokenFragment::BlockComment(block_comment)) => {
                    tokens.push(Ok(RawToken::BlockComment(Cow::Borrowed(block_comment))))
                }
                Ok(RawTokenFragment::StartOfToken(fragment, kind)) => {
                    if self.current_reconstructed_token.is_some() {
                        tokens.push(Err(Error::UnexpectedTokenStartStillProcessingPreviousToken));
                        return tokens.into_iter();
                    }
                    self.current_reconstructed_token = Some((fragment.to_vec(), kind));
                }
                Ok(RawTokenFragment::MiddleOfToken(fragment)) => {
                    let Some((token_data, _)) = &mut self.current_reconstructed_token else {
                        tokens.push(Err(Error::UnexpectedTokenContinuation));
                        return tokens.into_iter();
                    };

                    token_data.extend_from_slice(fragment);
                }
                Ok(RawTokenFragment::EndOfToken(fragment)) => {
                    let Some((mut token_data, kind)) = self.current_reconstructed_token.take()
                    else {
                        tokens.push(Err(Error::UnexpectedTokenContinuation));
                        return tokens.into_iter();
                    };

                    token_data.extend_from_slice(fragment);
                    tokens.push(Ok(RawToken::from_data_and_kind(
                        Cow::Owned(token_data),
                        kind,
                    )));
                }
            }
        }

        tokens.into_iter()
    }

    pub fn eof(self) -> Result<Option<RawToken<'static>>, Error> {
        match self.fragment_tokenizer.eof() {
            Err(error) => Err(error),
            Ok(None) => Ok(None),
            Ok(Some(raw_token_fragment)) => match raw_token_fragment {
                RawTokenFragment::LeftParen => Ok(Some(RawToken::LeftParen)),
                RawTokenFragment::RightParen => Ok(Some(RawToken::RightParen)),
                RawTokenFragment::SexpComment => Ok(Some(RawToken::SexpComment)),
                RawTokenFragment::Atom(atom) => Ok(Some(RawToken::Atom(Cow::Borrowed(atom)))),
                RawTokenFragment::LineComment(_)
                | RawTokenFragment::BlockComment(_)
                | RawTokenFragment::StartOfToken(_, _)
                | RawTokenFragment::MiddleOfToken(_) => {
                    Err(Error::UnexpectedEofWhileConstructingTokenFragments)
                }
                RawTokenFragment::EndOfToken(fragment) => {
                    let Some((mut token_data, kind)) = self.current_reconstructed_token else {
                        return Err(Error::UnexpectedTokenContinuation);
                    };

                    token_data.extend_from_slice(fragment);

                    Ok(Some(RawToken::from_data_and_kind(
                        Cow::Owned(token_data),
                        kind,
                    )))
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::fmt::Write;

    use bstr::ByteSlice;
    use insta::assert_snapshot;

    fn format_error(err: Error) -> String {
        format!("ERROR: {:?}", err)
    }

    fn format_raw_token_fragment(token: RawTokenFragment<'_>) -> String {
        match token {
            RawTokenFragment::LeftParen => "LeftParen: (".to_owned(),
            RawTokenFragment::RightParen => "RightParen: )".to_owned(),
            RawTokenFragment::SexpComment => "SexpComment: #;".to_owned(),
            RawTokenFragment::Atom(buf) => format!("Atom: {:?}", buf.as_bstr()),
            RawTokenFragment::LineComment(buf) => format!("LineComment: {:?}", buf.as_bstr()),
            RawTokenFragment::BlockComment(buf) => format!("BlockComment: {:?}", buf.as_bstr()),
            RawTokenFragment::StartOfToken(buf, kind) => {
                format!("Start of {:?}: {:?}", kind, buf.as_bstr())
            }
            RawTokenFragment::MiddleOfToken(buf) => format!("Middle of token: {:?}", buf.as_bstr()),
            RawTokenFragment::EndOfToken(buf) => format!("End of token: {:?}", buf.as_bstr()),
        }
    }

    fn write_raw_token_fragments(
        tokenizer: &mut StreamingFragmentTokenizer,
        buffer: &[u8],
    ) -> String {
        let mut output = String::new();
        let o = &mut output;

        for token in tokenizer.iter_raw_token_fragments(buffer) {
            let _ = match token {
                Err(err) => writeln!(o, "{}", format_error(err)),
                Ok(token) => writeln!(o, "{}", format_raw_token_fragment(token)),
            };
        }

        output
    }

    fn raw_fragments(buffer: &[u8]) -> String {
        let mut tokenizer = StreamingFragmentTokenizer::new();
        write_raw_token_fragments(&mut tokenizer, buffer)
    }

    fn streamed_fragments(buffers: &[&[u8]]) -> String {
        let mut tokenizer = StreamingFragmentTokenizer::new();
        let mut fragments = buffers
            .iter()
            .map(|buf| write_raw_token_fragments(&mut tokenizer, buf))
            .collect::<Vec<_>>();

        match tokenizer.eof() {
            Ok(None) => (),
            Ok(Some(token)) => fragments.push(format_raw_token_fragment(token)),
            Err(err) => fragments.push(format!("ERROR: {:?}", err)),
        }

        fragments.join("---\n")
    }

    fn format_raw_token(token: Result<RawToken<'_>, Error>) -> String {
        fn borrowed_or_owned(cow: &Cow<'_, [u8]>) -> &'static str {
            match cow {
                Cow::Borrowed(_) => "borrowed",
                Cow::Owned(_) => "owned",
            }
        }

        let token = match token {
            Err(err) => return format_error(err),
            Ok(token) => token,
        };

        match token {
            RawToken::LeftParen => "LeftParen: (".to_owned(),
            RawToken::RightParen => "RightParen: )".to_owned(),
            RawToken::SexpComment => "SexpComment: #;".to_owned(),
            RawToken::Atom(atom) => {
                format!("Atom: {:?} ({})", atom.as_bstr(), borrowed_or_owned(&atom))
            }
            RawToken::LineComment(line_comment) => {
                format!(
                    "LineComment: {:?} ({})",
                    line_comment.as_bstr(),
                    borrowed_or_owned(&line_comment)
                )
            }
            RawToken::BlockComment(block_comment) => {
                format!(
                    "BlockComment: {:?} ({})",
                    block_comment.as_bstr(),
                    borrowed_or_owned(&block_comment)
                )
            }
        }
    }

    fn streamed_tokens(buffers: &[&[u8]]) -> String {
        let mut tokenizer = StreamingTokenizer::new();
        let mut tokens = vec![];

        for buffer in buffers {
            tokens.extend(tokenizer.iter_raw_tokens(buffer));
        }

        match tokenizer.eof() {
            Ok(None) => (),
            Ok(Some(token)) => tokens.push(Ok(token)),
            Err(err) => tokens.push(Err(err)),
        }

        tokens
            .into_iter()
            .map(format_raw_token)
            .collect::<Vec<_>>()
            .join("\n---\n")
    }

    #[test]
    fn test_basics() {
        assert_snapshot!(raw_fragments(b"a bc 123 "), @r#"
        Atom: "a"
        Atom: "bc"
        Atom: "123"
        "#);

        assert_snapshot!(raw_fragments(b"a\"123\"b \"\""), @r#"
        Atom: "a"
        Atom: "\"123\""
        Atom: "b"
        Atom: "\"\""
        "#);

        assert_snapshot!(raw_fragments(b"## #a #( #) #\"#\" #\r\n#\n| #;|\n# "), @r###"
        Atom: "##"
        Atom: "#a"
        Atom: "#"
        LeftParen: (
        Atom: "#"
        RightParen: )
        Atom: "#"
        Atom: "\"#\""
        Atom: "#"
        Atom: "#"
        Atom: "|"
        SexpComment: #;
        Atom: "|"
        Atom: "#"
        "###);

        assert_snapshot!(raw_fragments(b"z#a z#( z#) z#\"#\" z#\r\nz#\n| z#;|\n"), @r##"
        Atom: "z#a"
        Atom: "z#"
        LeftParen: (
        Atom: "z#"
        RightParen: )
        Atom: "z#"
        Atom: "\"#\""
        Atom: "z#"
        Atom: "z#"
        Atom: "|"
        Atom: "z#"
        LineComment: ";|"
        "##);

        assert_snapshot!(raw_fragments(b"|| |a |( |) |\"|\" |\r\n|\n# |;|\n| "), @r##"
        Atom: "||"
        Atom: "|a"
        Atom: "|"
        LeftParen: (
        Atom: "|"
        RightParen: )
        Atom: "|"
        Atom: "\"|\""
        Atom: "|"
        Atom: "|"
        Atom: "#"
        Atom: "|"
        LineComment: ";|"
        Atom: "|"
        "##);

        assert_snapshot!(raw_fragments(b"z|a z|( z|) z|\"|\" z|\r\nz|\n# z|;|\n"), @r##"
        Atom: "z|a"
        Atom: "z|"
        LeftParen: (
        Atom: "z|"
        RightParen: )
        Atom: "z|"
        Atom: "\"|\""
        Atom: "z|"
        Atom: "z|"
        Atom: "#"
        Atom: "z|"
        LineComment: ";|"
        "##);
    }

    #[test]
    fn test_quoted_string_escapes() {
        assert_snapshot!(
            raw_fragments(b"\"\\\n \\n \\123 \\\\ \\x01 \\x0\""),
            @r#"Atom: "\"\\\n \\n \\123 \\\\ \\x01 \\x0\"""#);
    }

    #[test]
    fn test_line_comments() {
        assert_snapshot!(
            raw_fragments(b";\"\"\n;abc\r\n;\n "),
            @r#"
        LineComment: ";\"\""
        LineComment: ";abc"
        LineComment: ";"
        "#);
    }

    #[test]
    fn test_block_comments() {
        assert_snapshot!(
            raw_fragments(b"#|a|# _ #|# |# _ #|\"|#\\\"\"|# _ #| #| a |#| |#"),
            @r##"
        BlockComment: "#|a|#"
        Atom: "_"
        BlockComment: "#|# |#"
        Atom: "_"
        BlockComment: "#|\"|#\\\"\"|#"
        Atom: "_"
        BlockComment: "#| #| a |#| |#"
        "##,
        );
    }

    #[test]
    fn test_block_comment_errors() {
        assert_snapshot!(raw_fragments(b"a#|b"), @"ERROR: BlockCommentStartTokenInUnquotedAtom");
        assert_snapshot!(raw_fragments(b"a##|b"), @"ERROR: BlockCommentStartTokenInUnquotedAtom");
        assert_snapshot!(raw_fragments(b"a|#b"), @"ERROR: BlockCommentEndTokenInUnquotedAtom");
        assert_snapshot!(raw_fragments(b"a||#b"), @"ERROR: BlockCommentEndTokenInUnquotedAtom");
        assert_snapshot!(raw_fragments(b"|#"), @"ERROR: UnexpectedEndOfBlockComment");
    }

    #[test]
    fn test_sexp_comments() {
        assert_snapshot!(raw_fragments(b"#; a#;x\n##;y\n"), @r###"
        SexpComment: #;
        Atom: "a#"
        LineComment: ";x"
        Atom: "##"
        LineComment: ";y"
        "###);
    }

    #[test]
    fn test_partial_tokens() {
        assert_snapshot!(
            streamed_fragments(&[b"abc", b"", b"def", b"ghi "]),
            @r#"
        Start of Atom: "abc"
        ---
        ---
        Middle of token: "def"
        ---
        End of token: "ghi"
        "#,
        );

        assert_snapshot!(
            streamed_fragments(&[b";abc", b"def", b"ghi\n"]),
            @r#"
        Start of LineComment: ";abc"
        ---
        Middle of token: "def"
        ---
        End of token: "ghi"
        "#,
        );

        assert_snapshot!(
            streamed_fragments(&[b"#| abc", b"def", b"ghi |# "]),
            @r##"
        Start of BlockComment: "#| abc"
        ---
        Middle of token: "def"
        ---
        End of token: "ghi |#"
        "##,
        );
    }

    #[test]
    fn test_handling_of_pounds_across_buffers() {
        assert_snapshot!(
            streamed_fragments(&[b"#", b"; #", b"| |# #", b"a #", b"# "]),
            @r##"
        ---
        SexpComment: #;
        ---
        Start of BlockComment: "#"
        End of token: "| |#"
        ---
        Start of Atom: "#"
        End of token: "a"
        ---
        Start of Atom: "#"
        End of token: "#"
        "##,
        );
    }

    #[test]
    fn test_eof() {
        assert_snapshot!(streamed_fragments(&[b"a\r"]), @r#"
        Atom: "a"
        ---
        ERROR: NakedCarriageReturn
        "#);

        assert_snapshot!(streamed_fragments(&[b"a"]), @r#"
        Start of Atom: "a"
        ---
        End of token: ""
        "#);

        assert_snapshot!(streamed_fragments(&[b"a|"]), @r#"
        Start of Atom: "a|"
        ---
        End of token: ""
        "#);

        assert_snapshot!(streamed_fragments(&[b"a#"]), @r#"
        Start of Atom: "a#"
        ---
        End of token: ""
        "#);

        assert_snapshot!(streamed_fragments(&[b"|"]), @r#"
        Start of Atom: "|"
        ---
        End of token: ""
        "#);

        assert_snapshot!(streamed_fragments(&[b";"]), @r#"
        Start of LineComment: ";"
        ---
        End of token: ""
        "#);

        assert_snapshot!(streamed_fragments(&[b";"]), @r#"
        Start of LineComment: ";"
        ---
        End of token: ""
        "#);

        assert_snapshot!(streamed_fragments(&[b"#"]), @r##"
        ---
        Atom: "#"
        "##);
    }

    #[test]
    fn test_eof_errors() {
        assert_snapshot!(streamed_fragments(&[b"#|"]), @r##"
        Start of BlockComment: "#|"
        ---
        ERROR: UnexpectedEofWhileInBlockComment
        "##);
        assert_snapshot!(streamed_fragments(&[b"#| #"]), @r##"
        Start of BlockComment: "#| #"
        ---
        ERROR: UnexpectedEofWhileInBlockComment
        "##);
        assert_snapshot!(streamed_fragments(&[b"#| |"]), @r##"
        Start of BlockComment: "#| |"
        ---
        ERROR: UnexpectedEofWhileInBlockComment
        "##);
        assert_snapshot!(streamed_fragments(&[b"#| \""]), @r##"
        Start of BlockComment: "#| \""
        ---
        ERROR: UnexpectedEofWhileInBlockComment
        "##);
        assert_snapshot!(streamed_fragments(&[b"#| \"\\"]), @r##"
        Start of BlockComment: "#| \"\\"
        ---
        ERROR: UnexpectedEofWhileInBlockComment
        "##);
    }

    #[test]
    fn test_tokenizer() {
        assert_snapshot!(
            streamed_tokens(&[b"a1 a2", b" a3"]),
            @r#"
        Atom: "a1" (borrowed)
        ---
        Atom: "a2" (owned)
        ---
        Atom: "a3" (owned)
        "#,
        );

        assert_snapshot!(
            streamed_tokens(&[b"abc", b"def", b"ghi"]),
            @r#"Atom: "abcdefghi" (owned)"#,
        );

        assert_snapshot!(
            streamed_tokens(&[b"; lc1\n ; lc2", b"\n ; lc3"]),
            @r#"
        LineComment: "; lc1" (borrowed)
        ---
        LineComment: "; lc2" (owned)
        ---
        LineComment: "; lc3" (owned)
        "#,
        );

        assert_snapshot!(
            streamed_tokens(&[b"; abc", b"def", b"ghi"]),
            @r#"LineComment: "; abcdefghi" (owned)"#,
        );

        assert_snapshot!(
            streamed_tokens(&[b"#| bc1 |# #| bc2 ", b"|#"]),
            @r##"
        BlockComment: "#| bc1 |#" (borrowed)
        ---
        BlockComment: "#| bc2 |#" (owned)
        "##,
        );

        assert_snapshot!(
            streamed_tokens(&[b"#| abc", b"def", b"ghi |#"]),
            @r##"BlockComment: "#| abcdefghi |#" (owned)"##,
        );
    }
}
