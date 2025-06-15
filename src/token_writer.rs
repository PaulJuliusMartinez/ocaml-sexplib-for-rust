use std::io;

use crate::atom::Atom;

struct StandardWriter {
    just_started_new_list: bool,
}

impl StandardWriter {
    fn new() -> StandardWriter {
        StandardWriter {
            // This feels wrong, so maybe there's a better name for this...
            just_started_new_list: true,
        }
    }

    fn start_list<W: io::Write>(&mut self, mut w: W) -> io::Result<()> {
        if !self.just_started_new_list {
            write!(w, "{}", ' ')?;
        }
        self.just_started_new_list = true;
        write!(w, "{}", '(')
    }

    fn write_atom<W: io::Write>(&mut self, mut w: W, atom: Atom) -> io::Result<()> {
        if !self.just_started_new_list {
            write!(w, "{}", ' ')?;
        }
        self.just_started_new_list = false;
        atom.write(w)
    }

    fn end_list<W: io::Write>(&mut self, mut w: W) -> io::Result<()> {
        self.just_started_new_list = false;
        write!(w, "{}", ')')
    }
}

struct MachineWriter {
    need_space_before_next_unquoted_atom: bool,
}

impl MachineWriter {
    fn new() -> MachineWriter {
        MachineWriter {
            need_space_before_next_unquoted_atom: false,
        }
    }

    fn start_list<W: io::Write>(&mut self, mut w: W) -> io::Result<()> {
        self.need_space_before_next_unquoted_atom = false;
        write!(w, "{}", '(')
    }

    fn write_atom<W: io::Write>(&mut self, mut w: W, atom: Atom) -> io::Result<()> {
        let is_unquoted = !atom.needs_to_be_quoted();
        if self.need_space_before_next_unquoted_atom && is_unquoted {
            write!(w, "{}", ' ')?;
        }
        self.need_space_before_next_unquoted_atom = is_unquoted;
        atom.write(w)
    }

    fn end_list<W: io::Write>(&mut self, mut w: W) -> io::Result<()> {
        self.need_space_before_next_unquoted_atom = false;
        write!(w, "{}", ')')
    }
}

enum Writer {
    Standard(StandardWriter),
    Machine(MachineWriter),
}

pub struct TokenWriter<W> {
    w: W,
    writer: Writer,
}

pub enum Style {
    Standard,
    Machine,
}

impl<W: io::Write> TokenWriter<W> {
    pub fn new(w: W, style: Style) -> TokenWriter<W> {
        let writer = match style {
            Style::Standard => Writer::Standard(StandardWriter::new()),
            Style::Machine => Writer::Machine(MachineWriter::new()),
        };

        TokenWriter { w, writer }
    }

    pub fn start_list(&mut self) -> io::Result<()> {
        match self.writer {
            Writer::Standard(ref mut writer) => writer.start_list(&mut self.w),
            Writer::Machine(ref mut writer) => writer.start_list(&mut self.w),
        }
    }

    pub fn write_atom(&mut self, s: &str) -> io::Result<()> {
        let atom = Atom::new(s);
        match self.writer {
            Writer::Standard(ref mut writer) => writer.write_atom(&mut self.w, atom),
            Writer::Machine(ref mut writer) => writer.write_atom(&mut self.w, atom),
        }
    }

    pub fn end_list(&mut self) -> io::Result<()> {
        match self.writer {
            Writer::Standard(ref mut writer) => writer.end_list(&mut self.w),
            Writer::Machine(ref mut writer) => writer.end_list(&mut self.w),
        }
    }

    pub fn write_unit(&mut self) -> io::Result<()> {
        self.start_list()?;
        self.end_list()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use insta::assert_snapshot;

    fn with_style<F>(style: Style, f: F) -> io::Result<String>
    where
        F: FnOnce(&mut TokenWriter<&mut Vec<u8>>) -> io::Result<()>,
    {
        let mut v = Vec::new();
        let mut w = TokenWriter::new(&mut v, style);
        f(&mut w)?;
        Ok(String::from_utf8(v).unwrap())
    }

    #[test]
    fn test_standard() -> io::Result<()> {
        let s = with_style(Style::Standard, |w| w.write_atom("a"))?;
        assert_snapshot!(s, @"a");

        let s = with_style(Style::Standard, |w| w.write_atom("a b"))?;
        assert_snapshot!(s, @r#""a b""#);

        let s = with_style(Style::Standard, |w| {
            w.start_list()?;
            w.write_atom("a")?;
            w.write_atom("b c")?;
            w.write_atom("d")?;
            w.start_list()?;
            w.write_atom("e f")?;
            w.start_list()?;
            w.start_list()?;
            w.end_list()?;
            w.end_list()?;
            w.end_list()?;
            w.write_atom("z")?;
            w.end_list()
        })?;

        assert_snapshot!(s, @r#"(a "b c" d ("e f" (())) z)"#);

        Ok(())
    }

    #[test]
    fn test_machine() -> io::Result<()> {
        let s = with_style(Style::Machine, |w| w.write_atom("a"))?;
        assert_snapshot!(s, @"a");

        let s = with_style(Style::Machine, |w| w.write_atom("a b"))?;
        assert_snapshot!(s, @r#""a b""#);

        let s = with_style(Style::Machine, |w| {
            w.start_list()?;
            w.write_atom("a")?;
            w.write_atom("b")?;
            w.write_atom("c d")?;
            w.write_atom("e")?;
            w.write_atom("f g")?;
            w.write_atom("h i")?;
            w.end_list()
        })?;

        assert_snapshot!(s, @r#"(a b"c d"e"f g""h i")"#);

        Ok(())
    }
}
