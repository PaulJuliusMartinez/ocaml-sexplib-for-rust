pub enum Token {
    LeftParen,
    Atom(Vec<u8>),
    RightParen,
}
