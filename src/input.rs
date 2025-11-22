use std::io;
use std::ops::{Deref, Range};

pub trait Input<'de>: private::Sealed {
    /// Returns the next chunk of input data to be processed by the tokenizer,
    /// or `Eof` to indicate that no more data is available.
    fn next_chunk(&mut self) -> io::Result<InputChunk<'_>>;

    /// Returns a reference to the same data returned by the last call to
    /// `next_chunk` if `next_chunk` returned `Data`. Returns `None` if
    /// `next_chunk` return `Eof`.
    fn current_chunk<'s>(&'s self) -> Option<InputRef<'de, 's, [u8]>>;
}

mod private {
    pub trait Sealed {}
}

pub enum InputChunk<'t> {
    Data(&'t [u8]),
    Eof,
}

#[derive(Debug)]
pub enum InputRef<'de, 't, T>
where
    T: ?Sized,
{
    Borrowed(&'de T),
    Transient(&'t T),
}

impl<'de, 't> InputRef<'de, 't, [u8]> {
    pub fn index(&self, range: Range<usize>) -> InputRef<'de, 't, [u8]> {
        match self {
            InputRef::Borrowed(bytes) => InputRef::Borrowed(&bytes[range]),
            InputRef::Transient(bytes) => InputRef::Transient(&bytes[range]),
        }
    }
}

impl<'de, 't, T> Deref for InputRef<'de, 't, T>
where
    T: ?Sized,
{
    type Target = T;

    fn deref(&self) -> &T {
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

const DEFAULT_SLICE_CHUNK_SIZE: usize = 4 * 1024; // 4 kb

impl<'de> SliceInput<'de> {
    pub fn new(bytes: &'de [u8]) -> Self {
        Self::new_with_chunk_size(bytes, DEFAULT_SLICE_CHUNK_SIZE)
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
    fn next_chunk(&mut self) -> io::Result<InputChunk<'_>> {
        self.next_chunk_has_been_called = true;

        let next_chunk = match self.curr_offset {
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
        };

        Ok(next_chunk)
    }

    fn current_chunk<'s>(&'s self) -> Option<InputRef<'de, 's, [u8]>> {
        if !self.next_chunk_has_been_called {
            panic!("Called `SliceInput::current_chunk` before `next_chunk`.");
        }

        if self.has_returned_eof {
            None
        } else {
            Some(InputRef::Borrowed(self.curr_chunk))
        }
    }
}

/// Input source that rades from a std::io input stream.
pub struct IoInput<R>
where
    R: io::Read,
{
    reader: R,
    buffer: Vec<u8>,
    curr_used_bytes: usize,
    next_chunk_has_been_called: bool,
    has_returned_eof: bool,
    // Someday: Add support for tailing a file.
}

const DEFAULT_IO_CHUNK_SIZE: usize = 4 * 1024; // 4 kb

impl<R> IoInput<R>
where
    R: io::Read,
{
    pub fn new(reader: R) -> Self {
        Self::new_with_buffer_size(reader, DEFAULT_IO_CHUNK_SIZE)
    }

    pub fn new_with_buffer_size(reader: R, buffer_size: usize) -> Self {
        if buffer_size == 0 {
            panic!("buffer_size passed to IoInput must be non-zero");
        }

        IoInput {
            reader,
            buffer: vec![0; buffer_size],
            curr_used_bytes: 0,
            next_chunk_has_been_called: false,
            has_returned_eof: false,
        }
    }

    fn read_chunk(&mut self) -> io::Result<usize> {
        let bytes_read = self.reader.read(&mut self.buffer)?;
        self.curr_used_bytes = bytes_read;
        Ok(bytes_read)
    }

    fn curr_chunk(&self) -> &[u8] {
        &self.buffer[0..self.curr_used_bytes]
    }
}

impl<R> private::Sealed for IoInput<R> where R: io::Read {}

impl<'de, R> Input<'de> for IoInput<R>
where
    R: io::Read,
{
    fn next_chunk(&mut self) -> io::Result<InputChunk<'_>> {
        self.next_chunk_has_been_called = true;
        let bytes_read = self.read_chunk()?;

        let chunk = if bytes_read == 0 {
            self.has_returned_eof = true;
            InputChunk::Eof
        } else {
            InputChunk::Data(self.curr_chunk())
        };

        Ok(chunk)
    }

    fn current_chunk<'s>(&'s self) -> Option<InputRef<'de, 's, [u8]>> {
        if !self.next_chunk_has_been_called {
            panic!("Called `SliceInput::current_chunk` before `next_chunk`.");
        }

        if self.has_returned_eof {
            None
        } else {
            Some(InputRef::Transient(self.curr_chunk()))
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub struct ExplicitChunksInput {
        remaining_chunks: Vec<&'static [u8]>,
        current_chunk: Option<&'static [u8]>,
    }

    impl super::private::Sealed for ExplicitChunksInput {}

    impl ExplicitChunksInput {
        pub fn new(chunks: &[&'static [u8]]) -> ExplicitChunksInput {
            let mut chunks = chunks.to_vec();
            chunks.reverse();

            ExplicitChunksInput {
                remaining_chunks: chunks,
                current_chunk: None,
            }
        }
    }

    impl<'a> Input<'a> for ExplicitChunksInput {
        fn next_chunk(&mut self) -> io::Result<InputChunk<'_>> {
            match self.remaining_chunks.pop() {
                None => {
                    self.current_chunk = None;
                    Ok(InputChunk::Eof)
                }
                Some(chunk) => {
                    self.current_chunk = Some(chunk);
                    Ok(InputChunk::Data(chunk))
                }
            }
        }

        fn current_chunk<'s>(&'s self) -> Option<InputRef<'a, 's, [u8]>> {
            match self.current_chunk {
                None => None,
                Some(chunk) => Some(InputRef::Transient(chunk)),
            }
        }
    }
}
