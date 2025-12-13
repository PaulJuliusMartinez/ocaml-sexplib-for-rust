use std::io;

use serde::{ser, Serialize};

use crate::error::{Error, Result};
use crate::token_writer::{Style, TokenWriter};

pub struct Serializer<W> {
    token_writer: TokenWriter<W>,
}

pub fn to_writer<W, T>(writer: W, value: &T) -> Result<()>
where
    W: io::Write,
    T: ?Sized + Serialize,
{
    let token_writer = TokenWriter::new(writer, Style::Standard);
    let mut ser = Serializer { token_writer };
    value.serialize(&mut ser)
}

pub fn to_writer_mach<W, T>(writer: W, value: &T) -> Result<()>
where
    W: io::Write,
    T: ?Sized + Serialize,
{
    let token_writer = TokenWriter::new(writer, Style::Machine);
    let mut ser = Serializer { token_writer };
    value.serialize(&mut ser)
}

pub fn to_string<T>(value: &T) -> Result<String>
where
    T: ?Sized + Serialize,
{
    let mut vec = Vec::new();
    to_writer(&mut vec, value)?;
    // Someday: call `from_utf8_unchecked` / make sure we don't write invalid UTF-8
    Ok(String::from_utf8(vec).unwrap())
}

pub fn to_string_mach<T>(value: &T) -> Result<String>
where
    T: ?Sized + Serialize,
{
    let mut vec = Vec::new();
    to_writer_mach(&mut vec, value)?;
    // Someday: call `from_utf8_unchecked` / make sure we don't write invalid UTF-8
    Ok(String::from_utf8(vec).unwrap())
}

impl<'a, W> ser::Serializer for &'a mut Serializer<W>
where
    W: io::Write,
{
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Self;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;

    fn serialize_bool(self, v: bool) -> Result<()> {
        let atom = if v { "true" } else { "false" };
        self.token_writer.write_str_atom(atom).map_err(Error::io)
    }

    fn serialize_i64(self, v: i64) -> Result<()> {
        // Someday: Maybe use itoa crate?
        let atom = v.to_string();
        self.token_writer.write_str_atom(&atom).map_err(Error::io)
    }

    fn serialize_i32(self, v: i32) -> Result<()> {
        self.serialize_i64(i64::from(v))
    }

    fn serialize_i16(self, v: i16) -> Result<()> {
        self.serialize_i64(i64::from(v))
    }

    fn serialize_i8(self, v: i8) -> Result<()> {
        self.serialize_i64(i64::from(v))
    }

    fn serialize_u64(self, v: u64) -> Result<()> {
        // Someday: Maybe use itoa crate?
        let atom = v.to_string();
        self.token_writer.write_str_atom(&atom).map_err(Error::io)
    }

    fn serialize_u32(self, v: u32) -> Result<()> {
        self.serialize_u64(u64::from(v))
    }

    fn serialize_u16(self, v: u16) -> Result<()> {
        self.serialize_u64(u64::from(v))
    }

    fn serialize_u8(self, v: u8) -> Result<()> {
        self.serialize_u64(u64::from(v))
    }

    fn serialize_f64(self, v: f64) -> Result<()> {
        let atom = v.to_string();
        self.token_writer.write_str_atom(&atom).map_err(Error::io)
    }

    fn serialize_f32(self, v: f32) -> Result<()> {
        let atom = v.to_string();
        self.token_writer.write_str_atom(&atom).map_err(Error::io)
    }

    fn serialize_str(self, v: &str) -> Result<()> {
        self.token_writer.write_str_atom(v).map_err(Error::io)
    }

    fn serialize_char(self, v: char) -> Result<()> {
        // Someday: Do this without allocating?
        let ch = v.to_string();
        self.token_writer.write_str_atom(&ch).map_err(Error::io)
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<()> {
        self.token_writer.write_bytes_atom(v).map_err(Error::io)
    }

    fn serialize_unit(self) -> Result<()> {
        self.token_writer.write_unit().map_err(Error::io)
    }

    fn serialize_none(self) -> Result<()> {
        self.serialize_unit()
    }

    fn serialize_some<T>(self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        self.token_writer.start_list().map_err(Error::io)?;
        value.serialize(&mut *self)?;
        self.token_writer.end_list().map_err(Error::io)
    }

    // e.g. `struct Foo;`
    fn serialize_unit_struct(self, name: &'static str) -> Result<()> {
        self.token_writer.write_str_atom(name).map_err(Error::io)
    }

    // e.g. `E::A` in `enum { A, B(i64), C(i32, i32), D { x: bool, y: char } }`
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<()> {
        self.token_writer.write_str_atom(variant).map_err(Error::io)
    }

    // e.g. `struct PhoneNumber(String)`
    fn serialize_newtype_struct<T>(self, _name: &'static str, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    // e.g. `E::B` in `enum { A, B(i64), C(i32, i32), D { x: bool, y: char } }`
    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        self.token_writer.start_list().map_err(Error::io)?;
        self.token_writer
            .write_str_atom(variant)
            .map_err(Error::io)?;
        value.serialize(&mut *self)?;
        self.token_writer.end_list().map_err(Error::io)
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq> {
        self.token_writer.start_list().map_err(Error::io)?;
        Ok(self)
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple> {
        self.serialize_seq(Some(len))
    }

    // e.g. `struct Rgb(u8, u8, u8)`
    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct> {
        self.serialize_seq(Some(len))
    }

    // e.g. `E::C` in `enum { A, B(i64), C(i32, i32), D { x: bool, y: char } }`
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        self.token_writer.start_list().map_err(Error::io)?;
        self.token_writer
            .write_str_atom(variant)
            .map_err(Error::io)?;
        Ok(self)
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap> {
        self.serialize_seq(len)
    }

    fn serialize_struct(self, _name: &'static str, len: usize) -> Result<Self::SerializeStruct> {
        self.serialize_seq(Some(len))
    }

    // e.g. `E::D` in `enum { A, B(i64), C(i32, i32), D { x: bool, y: char } }`
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant> {
        self.token_writer.start_list().map_err(Error::io)?;
        self.token_writer
            .write_str_atom(variant)
            .map_err(Error::io)?;
        Ok(self)
    }
}

macro_rules! impl_list_serializer {
    ($serializer:ident, $serialize_elem:ident) => {
        impl<'a, W: io::Write> ser::$serializer for &'a mut Serializer<W> {
            type Ok = ();
            type Error = Error;

            fn $serialize_elem<T>(&mut self, value: &T) -> Result<()>
            where
                T: ?Sized + Serialize,
            {
                value.serialize(&mut **self)
            }

            fn end(self) -> Result<()> {
                self.token_writer.end_list().map_err(Error::io)
            }
        }
    };
}

impl_list_serializer!(SerializeSeq, serialize_element);
impl_list_serializer!(SerializeTuple, serialize_element);
impl_list_serializer!(SerializeTupleStruct, serialize_field);
impl_list_serializer!(SerializeTupleVariant, serialize_field);

macro_rules! impl_key_value_pair_serializer {
    ($serializer:ident) => {
        impl<'a, W: io::Write> ser::$serializer for &'a mut Serializer<W> {
            type Ok = ();
            type Error = Error;

            fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<()>
            where
                T: ?Sized + Serialize,
            {
                self.token_writer.start_list().map_err(Error::io)?;
                self.token_writer.write_str_atom(key).map_err(Error::io)?;
                value.serialize(&mut **self)?;
                self.token_writer.end_list().map_err(Error::io)
            }

            fn end(self) -> Result<()> {
                self.token_writer.end_list().map_err(Error::io)
            }
        }
    };
}

impl_key_value_pair_serializer!(SerializeStruct);
impl_key_value_pair_serializer!(SerializeStructVariant);

impl<'a, W: io::Write> ser::SerializeMap for &'a mut Serializer<W> {
    type Ok = ();
    type Error = Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        self.token_writer.start_list().map_err(Error::io)?;
        key.serialize(&mut **self)
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(&mut **self)?;
        self.token_writer.end_list().map_err(Error::io)
    }

    fn end(self) -> Result<()> {
        self.token_writer.end_list().map_err(Error::io)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use insta::assert_snapshot;

    #[allow(clippy::approx_constant)]
    #[test]
    fn test_primitives() {
        assert_snapshot!(to_string(&true).unwrap(), @"true");
        assert_snapshot!(to_string(&false).unwrap(), @"false");

        assert_snapshot!(to_string(&-127i8).unwrap(), @"-127");
        assert_snapshot!(to_string(&-32_768i16).unwrap(), @"-32768");
        assert_snapshot!(to_string(&-2_000_000_000i32).unwrap(), @"-2000000000");
        assert_snapshot!(to_string(&0i64).unwrap(), @"0");

        assert_snapshot!(to_string(&255u8).unwrap(), @"255");
        assert_snapshot!(to_string(&65_535u16).unwrap(), @"65535");
        assert_snapshot!(to_string(&4_000_000_000u32).unwrap(), @"4000000000");
        assert_snapshot!(to_string(&0u64).unwrap(), @"0");

        assert_snapshot!(to_string(&-3.14f32).unwrap(), @"-3.14");
        assert_snapshot!(to_string(&2.718f64).unwrap(), @"2.718");

        assert_snapshot!(to_string(&'a').unwrap(), @"a");
        assert_snapshot!(to_string(&'α').unwrap(), @"α");
    }

    #[test]
    fn test_strings() {
        assert_snapshot!(to_string(&"abc").unwrap(), @"abc");
        assert_snapshot!(to_string(&"x y z").unwrap(), @"\"x y z\"");
        // byte strings are serialized as arrays of bytes by default due to limitations in Rust.
        assert_snapshot!(to_string(&b"abc").unwrap(), @"(97 98 99)");
    }

    #[test]
    fn test_string_escaping() {
        assert_snapshot!(to_string(&"a\nb").unwrap(), @r#""a\nb""#);
        assert_snapshot!(to_string(&"a\tb").unwrap(), @r#""a\tb""#);
        assert_snapshot!(to_string(&"a\rb").unwrap(), @r#""a\rb""#);
        assert_snapshot!(to_string(&"a\x0bb").unwrap(), @r#""a\x0bb""#);
        assert_snapshot!(to_string(&"a\"b").unwrap(), @r#""a\"b""#);
        assert_snapshot!(to_string(&"a\\b").unwrap(), @r#""a\\b""#);
        assert_snapshot!(to_string(&"a\\b").unwrap(), @r#""a\\b""#);
        assert_snapshot!(to_string(&"a\0b").unwrap(), @r#""a\x00b""#);

        // Non-breaking space
        assert_snapshot!(to_string(&"a\u{00A0}b").unwrap(), @r#""a\xc2\xa0b""#);
        // Zero-width joiner
        assert_snapshot!(to_string(&"a\u{200D}b").unwrap(), @r#""a\xe2\x80\x8db""#);
        // Bactrian Camel
        assert_snapshot!(to_string(&"a🐫b").unwrap(), @"a🐫b");
    }

    #[test]
    fn test_bytes() {
        #[derive(Serialize)]
        struct ByteStruct<'a> {
            #[serde(with = "serde_bytes")]
            bytes: &'a [u8],
            #[serde(with = "serde_bytes")]
            byte_vec: Vec<u8>,
            #[serde(with = "serde_bytes")]
            byte_array: [u8; 2],
        }

        let byte1 = 0xCE;
        let byte2 = 0xB1;
        let good_bytes = [byte1, byte2];
        assert_snapshot!(to_string(serde_bytes::Bytes::new(&good_bytes)).unwrap(), @"α");

        let byte_struct = ByteStruct {
            bytes: &good_bytes,
            byte_vec: good_bytes.to_vec(),
            byte_array: [byte1, byte2],
        };
        assert_snapshot!(to_string(&byte_struct).unwrap(), @"((bytes α) (byte_vec α) (byte_array α))");

        let byte3 = b'a';
        let bad_bytes = [byte3, byte2];
        let byte_struct = ByteStruct {
            bytes: &bad_bytes,
            byte_vec: bad_bytes.to_vec(),
            byte_array: [byte3, byte2],
        };
        assert_snapshot!(to_string(&byte_struct).unwrap(), @r#"((bytes "a\xb1") (byte_vec "a\xb1") (byte_array "a\xb1"))"#);
    }

    #[test]
    fn test_option() {
        assert_snapshot!(to_string(&Some(1i32)).unwrap(), @"(1)");
        assert_snapshot!(to_string(&None::<i32>).unwrap(), @"()");
    }

    #[test]
    fn test_tuple() {
        assert_snapshot!(to_string(&(1, 2)).unwrap(), @"(1 2)");
    }

    #[test]
    fn test_seq() {
        assert_snapshot!(to_string(&vec![1, 2]).unwrap(), @"(1 2)");
    }

    #[test]
    fn test_unit() {
        assert_snapshot!(to_string(&()).unwrap(), @"()");
    }

    #[test]
    fn test_unit_struct() {
        #[derive(Serialize)]
        struct UnitStruct;
        assert_snapshot!(to_string(&UnitStruct).unwrap(), @"UnitStruct");
    }

    #[test]
    fn test_newtype_struct() {
        #[derive(Serialize)]
        struct NewtypeStruct(u8);
        assert_snapshot!(to_string(&NewtypeStruct(1)).unwrap(), @"1");
    }

    #[test]
    fn test_tuple_struct() {
        #[derive(Serialize)]
        struct TupleStruct(u8, u8);
        assert_snapshot!(to_string(&TupleStruct(1, 2)).unwrap(), @"(1 2)");
    }

    #[test]
    fn test_variants() {
        #[derive(Serialize)]
        enum Variant {
            Unit,
            Newtype(i32),
            Tuple(i32, i32),
            Struct { x: i32 },
        }

        assert_snapshot!(to_string(&Variant::Unit).unwrap(), @"Unit");
        assert_snapshot!(to_string(&Variant::Newtype(1)).unwrap(), @"(Newtype 1)");
        assert_snapshot!(to_string(&Variant::Tuple(1, 2)).unwrap(), @"(Tuple 1 2)");
        assert_snapshot!(to_string(&Variant::Struct { x: 1 }).unwrap(), @"(Struct (x 1))");
    }

    #[test]
    fn test_struct() {
        #[derive(Serialize)]
        struct Basic {
            x: i32,
        }
        assert_snapshot!(to_string(&Basic { x: 1 }).unwrap(), @"((x 1))");
    }

    #[test]
    fn test_map() {
        let mut hash_map = std::collections::HashMap::new();
        // Note that iteration order is not guaranteed to match insertion order,
        // so inserting multiple values leads to non-deterministic output.
        hash_map.insert((1, 2), 3);
        assert_snapshot!(to_string(&hash_map).unwrap(), @"(((1 2) 3))");
    }
}
