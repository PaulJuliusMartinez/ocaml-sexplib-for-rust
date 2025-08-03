use std::ops::{Deref, Range};

pub trait Input<'de>: private::Sealed {
    /// Returns the next chunk of input data to be processed by the tokenizer,
    /// or `Eof` to indicate that no more data is available.
    // Someday: This needs to return `io::Result`.
    fn next_chunk(&mut self) -> InputChunk<'_>;

    /// Returns a reference to the same data returned by the last call to
    /// `next_chunk`. It is an error for the tokenizer to call this function
    /// before calling `next_chunk`, or to call it after `next_chunk`
    /// returns `Eof`.
    fn last_chunk<'s>(&'s self) -> InputRef<'de, 's>;
}

mod private {
    pub trait Sealed {}
}

pub enum InputChunk<'t> {
    Data(&'t [u8]),
    Eof,
}

pub enum InputRef<'de, 't> {
    Borrowed(&'de [u8]),
    Transient(&'t [u8]),
}

impl<'de, 't> InputRef<'de, 't> {
    pub fn bytes(&self) -> &[u8] {
        match self {
            InputRef::Borrowed(bytes) => bytes,
            InputRef::Transient(bytes) => bytes,
        }
    }

    pub fn index(&self, range: Range<usize>) -> InputRef<'de, 't> {
        match self {
            InputRef::Borrowed(bytes) => InputRef::Borrowed(&bytes[range]),
            InputRef::Transient(bytes) => InputRef::Transient(&bytes[range]),
        }
    }
}

impl<'de, 't> Deref for InputRef<'de, 't> {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        match *self {
            InputRef::Borrowed(de) => de,
            InputRef::Transient(t) => t,
        }
    }
}

/// Input source that reads from a slice of bytes.
pub struct SliceInput<'de> {
    bytes: &'de [u8],
    curr_offset: Option<usize>,
    curr_chunk: &'de [u8],
    chunk_size: usize,
    next_chunk_has_been_called: bool,
    has_returned_eof: bool,
}

const DEFAULT_CHUNK_SIZE: usize = 4 * 1024; // 4 kb

impl<'de> SliceInput<'de> {
    pub fn new(bytes: &'de [u8]) -> Self {
        Self::new_with_chunk_size(bytes, DEFAULT_CHUNK_SIZE)
    }

    pub fn new_with_chunk_size(bytes: &'de [u8], chunk_size: usize) -> Self {
        if chunk_size == 0 {
            panic!("chunk_size passed to SliceInput must be non-zero");
        }

        SliceInput {
            bytes,
            curr_offset: None,
            curr_chunk: &bytes[0..0],
            chunk_size,
            next_chunk_has_been_called: false,
            has_returned_eof: false,
        }
    }

    fn set_current_chunk(&mut self, starting_at_offset: usize) {
        self.curr_offset = Some(starting_at_offset);
        let end = usize::min(starting_at_offset + self.chunk_size, self.bytes.len());
        self.curr_chunk = &self.bytes[starting_at_offset..end];
    }
}

impl<'de> private::Sealed for SliceInput<'de> {}

impl<'de> Input<'de> for SliceInput<'de> {
    fn next_chunk(&mut self) -> InputChunk<'_> {
        self.next_chunk_has_been_called = true;

        match self.curr_offset {
            None => {
                // Getting the first chunk
                if self.bytes.len() == 0 {
                    // Degenerate case; input was empty
                    self.has_returned_eof = true;
                    InputChunk::Eof
                } else {
                    // Someday: Pick a smaller first chunk size so that subsequent
                    // chunks are suitably aligned for SIMD operations.
                    self.set_current_chunk(0);
                    InputChunk::Data(self.curr_chunk)
                }
            }
            Some(curr_offset) => {
                if curr_offset + self.chunk_size >= self.bytes.len() {
                    self.has_returned_eof = true;
                    InputChunk::Eof
                } else {
                    self.set_current_chunk(curr_offset + self.chunk_size);
                    InputChunk::Data(self.curr_chunk)
                }
            }
        }
    }

    fn last_chunk<'s>(&'s self) -> InputRef<'de, 's> {
        if !self.next_chunk_has_been_called {
            panic!("Called `SliceInput::last_chunk` before `next_chunk`.");
        }

        if self.has_returned_eof {
            panic!("Called `SliceInput::last_chunk` after `next_chunk` returned `Eof`.");
        }

        InputRef::Borrowed(self.curr_chunk)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub struct ExplicitChunksInput {
        remaining_chunks: Vec<&'static [u8]>,
        last_chunk: Option<&'static [u8]>,
    }

    impl super::private::Sealed for ExplicitChunksInput {}

    impl ExplicitChunksInput {
        pub fn new(chunks: &[&'static [u8]]) -> ExplicitChunksInput {
            let mut chunks = chunks.to_vec();
            chunks.reverse();

            ExplicitChunksInput {
                remaining_chunks: chunks,
                last_chunk: None,
            }
        }
    }

    impl<'a> Input<'a> for ExplicitChunksInput {
        fn next_chunk(&mut self) -> InputChunk<'_> {
            match self.remaining_chunks.pop() {
                None => {
                    self.last_chunk = None;
                    InputChunk::Eof
                }
                Some(chunk) => {
                    self.last_chunk = Some(chunk);
                    InputChunk::Data(chunk)
                }
            }
        }

        fn last_chunk<'s>(&'s self) -> InputRef<'a, 's> {
            InputRef::Transient(self.last_chunk.unwrap())
        }
    }
}
