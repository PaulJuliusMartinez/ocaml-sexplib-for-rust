pub enum Token<'de> {
    LeftParen,
    Atom(&'de [u8]),
    RightParen,
}
