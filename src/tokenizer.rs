use std::io;

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
