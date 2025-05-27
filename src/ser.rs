use std::borrow::Cow;

use serde::{ser, Serialize};

use crate::error::{Error, Result};
use crate::Sexp;

pub struct Serializer;
pub struct CompoundSerializer(Vec<Sexp<'static>>);

pub fn to_sexp<T>(value: &T) -> Result<Sexp<'static>>
where
    T: Serialize,
{
    value.serialize(Serializer)
}

impl ser::Serializer for Serializer {
    type Ok = Sexp<'static>;
    type Error = Error;
    type SerializeSeq = CompoundSerializer;
    type SerializeTuple = CompoundSerializer;
    type SerializeTupleStruct = CompoundSerializer;
    type SerializeTupleVariant = CompoundSerializer;
    type SerializeMap = CompoundSerializer;
    type SerializeStruct = CompoundSerializer;
    type SerializeStructVariant = CompoundSerializer;

    fn serialize_bool(self, v: bool) -> Result<Sexp<'static>> {
        let atom = if v { "true" } else { "false" };
        Ok(Sexp::Atom(Cow::from(atom)))
    }

    fn serialize_i64(self, v: i64) -> Result<Sexp<'static>> {
        // Someday: Maybe use itoa crate?
        Ok(Sexp::Atom(Cow::Owned(v.to_string())))
    }

    fn serialize_i32(self, v: i32) -> Result<Sexp<'static>> {
        self.serialize_i64(i64::from(v))
    }

    fn serialize_i16(self, v: i16) -> Result<Sexp<'static>> {
        self.serialize_i64(i64::from(v))
    }

    fn serialize_i8(self, v: i8) -> Result<Sexp<'static>> {
        self.serialize_i64(i64::from(v))
    }

    fn serialize_u64(self, v: u64) -> Result<Sexp<'static>> {
        Ok(Sexp::Atom(Cow::Owned(v.to_string())))
    }

    fn serialize_u32(self, v: u32) -> Result<Sexp<'static>> {
        self.serialize_u64(u64::from(v))
    }

    fn serialize_u16(self, v: u16) -> Result<Sexp<'static>> {
        self.serialize_u64(u64::from(v))
    }

    fn serialize_u8(self, v: u8) -> Result<Sexp<'static>> {
        self.serialize_u64(u64::from(v))
    }

    fn serialize_f64(self, v: f64) -> Result<Sexp<'static>> {
        Ok(Sexp::Atom(Cow::Owned(v.to_string())))
    }

    fn serialize_f32(self, v: f32) -> Result<Sexp<'static>> {
        Ok(Sexp::Atom(Cow::Owned(v.to_string())))
    }

    fn serialize_str(self, v: &str) -> Result<Sexp<'static>> {
        Ok(Sexp::Atom(Cow::Owned(v.to_string())))
    }

    fn serialize_char(self, v: char) -> Result<Sexp<'static>> {
        Ok(Sexp::Atom(Cow::Owned(v.to_string())))
    }

    fn is_human_readable(&self) -> bool {
        false
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Sexp<'static>> {
        // Someday: This should always return an error and encourage
        // using bytes::Sexp instead.
        match std::str::from_utf8(dbg!(v)) {
            Ok(s) => self.serialize_str(dbg!(s)),
            Err(_) => Err(Error::SerializationError(
                "non-UTF-8 bytes are not supported".to_string(),
            )),
        }
    }

    fn serialize_unit(self) -> Result<Sexp<'static>> {
        Ok(Sexp::List(vec![]))
    }

    fn serialize_none(self) -> Result<Sexp<'static>> {
        self.serialize_unit()
    }

    fn serialize_some<T>(self, value: &T) -> Result<Sexp<'static>>
    where
        T: ?Sized + Serialize,
    {
        let sexp = value.serialize(self)?;
        Ok(Sexp::List(vec![sexp]))
    }

    // e.g. `struct Foo;`
    fn serialize_unit_struct(self, name: &'static str) -> Result<Sexp<'static>> {
        Ok(Sexp::Atom(Cow::from(name)))
    }

    // e.g. `E::A` in `enum { A, B(i64), C(i32, i32), D { x: bool, y: char } }`
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Sexp<'static>> {
        Ok(Sexp::Atom(Cow::from(variant)))
    }

    // e.g. `struct PhoneNumber(String)`
    fn serialize_newtype_struct<T>(self, _name: &'static str, value: &T) -> Result<Sexp<'static>>
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
    ) -> Result<Sexp<'static>>
    where
        T: ?Sized + Serialize,
    {
        let constructor = self.serialize_str(variant)?;
        let value = value.serialize(Serializer)?;
        Ok(Sexp::List(vec![constructor, value]))
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq> {
        let vec = match len {
            None => vec![],
            Some(len) => Vec::with_capacity(len),
        };
        Ok(CompoundSerializer(vec))
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
        // Is this
        self.serialize_seq(Some(len))
    }

    // e.g. `E::C` in `enum { A, B(i64), C(i32, i32), D { x: bool, y: char } }`
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        let mut vec = Vec::with_capacity(len + 1);
        let constructor = self.serialize_str(variant)?;
        vec.push(constructor);
        Ok(CompoundSerializer(vec))
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
        len: usize,
    ) -> Result<Self::SerializeStructVariant> {
        let mut vec = Vec::with_capacity(len + 1);
        let constructor = self.serialize_str(variant)?;
        vec.push(constructor);
        Ok(CompoundSerializer(vec))
    }
}

impl CompoundSerializer {
    fn push(&mut self, value: Sexp<'static>) -> Result<()> {
        self.0.push(value);
        Ok(())
    }

    fn serialize_key_value_pair<T>(&mut self, key: &'static str, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let key = Sexp::Atom(Cow::from(key));
        let value = value.serialize(Serializer)?;
        self.push(Sexp::List(vec![key, value]))
    }

    fn end(self) -> Result<Sexp<'static>> {
        Ok(Sexp::List(self.0))
    }
}

macro_rules! impl_list_serializer {
    ($serializer:ident, $serialize_elem:ident) => {
        impl ser::$serializer for CompoundSerializer {
            type Ok = Sexp<'static>;
            type Error = Error;

            fn $serialize_elem<T>(&mut self, value: &T) -> Result<()>
            where
                T: ?Sized + Serialize,
            {
                let elem = value.serialize(Serializer)?;
                self.push(elem)
            }

            fn end(self) -> Result<Sexp<'static>> {
                self.end()
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
        impl ser::$serializer for CompoundSerializer {
            type Ok = Sexp<'static>;
            type Error = Error;

            fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<()>
            where
                T: ?Sized + Serialize,
            {
                self.serialize_key_value_pair(key, value)
            }

            fn end(self) -> Result<Sexp<'static>> {
                self.end()
            }
        }
    };
}

impl_key_value_pair_serializer!(SerializeStruct);
impl_key_value_pair_serializer!(SerializeStructVariant);

impl ser::SerializeMap for CompoundSerializer {
    type Ok = Sexp<'static>;
    type Error = Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        // Serialize the key and push it to the end of the vec as a temporary holding place.
        let key = key.serialize(Serializer)?;
        self.push(key)
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let key = self.0.pop().unwrap();
        let value = value.serialize(Serializer)?;
        self.push(Sexp::List(vec![key, value]))
    }

    fn end(self) -> Result<Sexp<'static>> {
        self.end()
    }
}

#[cfg(test)]
mod tests {
    use std::fmt;

    use super::*;

    use insta::{assert_debug_snapshot, assert_snapshot};

    impl<'a> fmt::Display for Sexp<'a> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Sexp::Atom(s) => write!(f, "{}", s)?,
                Sexp::List(sexps) => {
                    write!(f, "[")?;
                    for (i, sexp) in sexps.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", sexp)?;
                    }
                    write!(f, "]")?;
                }
            }

            Ok(())
        }
    }

    #[test]
    fn test_primitives() {
        assert_snapshot!(to_sexp(&true).unwrap(), @"true");
        assert_snapshot!(to_sexp(&false).unwrap(), @"false");

        assert_snapshot!(to_sexp(&-127i8).unwrap(), @"-127");
        assert_snapshot!(to_sexp(&-32_768i16).unwrap(), @"-32768");
        assert_snapshot!(to_sexp(&-2_000_000_000i32).unwrap(), @"-2000000000");
        assert_snapshot!(to_sexp(&0i64).unwrap(), @"0");

        assert_snapshot!(to_sexp(&255u8).unwrap(), @"255");
        assert_snapshot!(to_sexp(&65_535u16).unwrap(), @"65535");
        assert_snapshot!(to_sexp(&4_000_000_000u32).unwrap(), @"4000000000");
        assert_snapshot!(to_sexp(&0u64).unwrap(), @"0");

        assert_snapshot!(to_sexp(&-3.14f32).unwrap(), @"-3.14");
        assert_snapshot!(to_sexp(&2.718f64).unwrap(), @"2.718");

        assert_snapshot!(to_sexp(&'a').unwrap(), @"a");
        assert_snapshot!(to_sexp(&'α').unwrap(), @"α");
    }

    #[test]
    fn test_strings_and_bytes() {
        assert_snapshot!(to_sexp(&"abc").unwrap(), @"abc");
        // byte strings are serialized as arrays of bytes by default due to limitations in Rust.
        assert_snapshot!(to_sexp(&b"abc").unwrap(), @"[97, 98, 99]");

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
        assert_snapshot!(to_sexp(&std::str::from_utf8(good_bytes.as_ref()).unwrap()).unwrap(), @"α");

        let byte_struct = ByteStruct {
            bytes: &good_bytes,
            byte_vec: good_bytes.to_vec(),
            byte_array: [byte1, byte2],
        };
        assert_snapshot!(to_sexp(&byte_struct).unwrap(), @"[[bytes, α], [byte_vec, α], [byte_array, α]]");

        let byte3 = b'a';
        let bad_bytes = [byte3, byte2];
        let byte_struct = ByteStruct {
            bytes: &bad_bytes,
            byte_vec: bad_bytes.to_vec(),
            byte_array: [byte3, byte2],
        };
        assert_debug_snapshot!(to_sexp(&byte_struct), @r#"
        Err(
            SerializationError(
                "non-UTF-8 bytes are not supported",
            ),
        )
        "#);
    }

    #[test]
    fn test_option() {
        assert_snapshot!(to_sexp(&Some(1i32)).unwrap(), @"[1]");
        assert_snapshot!(to_sexp(&None::<i32>).unwrap(), @"[]");
    }

    #[test]
    fn test_tuple() {
        assert_snapshot!(to_sexp(&(1, 2)).unwrap(), @"[1, 2]");
    }

    #[test]
    fn test_seq() {
        assert_snapshot!(to_sexp(&vec![1, 2]).unwrap(), @"[1, 2]");
    }

    #[test]
    fn test_unit() {
        assert_snapshot!(to_sexp(&()).unwrap(), @"[]");
    }

    #[test]
    fn test_unit_struct() {
        #[derive(Serialize)]
        struct UnitStruct;
        assert_snapshot!(to_sexp(&UnitStruct).unwrap(), @"UnitStruct");
    }

    #[test]
    fn test_newtype_struct() {
        #[derive(Serialize)]
        struct NewtypeStruct(u8);
        assert_snapshot!(to_sexp(&NewtypeStruct(1)).unwrap(), @"1");
    }

    #[test]
    fn test_tuple_struct() {
        #[derive(Serialize)]
        struct TupleStruct(u8, u8);
        assert_snapshot!(to_sexp(&TupleStruct(1, 2)).unwrap(), @"[1, 2]");
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

        assert_snapshot!(to_sexp(&Variant::Unit).unwrap(), @"Unit");
        assert_snapshot!(to_sexp(&Variant::Newtype(1)).unwrap(), @"[Newtype, 1]");
        assert_snapshot!(to_sexp(&Variant::Tuple(1, 2)).unwrap(), @"[Tuple, 1, 2]");
        assert_snapshot!(to_sexp(&Variant::Struct { x: 1 }).unwrap(), @"[Struct, [x, 1]]");
    }

    #[test]
    fn test_struct() {
        #[derive(Serialize)]
        struct Basic {
            x: i32,
        }
        assert_snapshot!(to_sexp(&Basic { x: 1 }).unwrap(), @"[[x, 1]]");
    }

    #[test]
    fn test_map() {
        let mut hash_map = std::collections::HashMap::new();
        // Note that iteration order is not guaranteed to match insertion order,
        // so inserting multiple values leads to non-deterministic output.
        hash_map.insert((1, 2), 3);
        assert_snapshot!(to_sexp(&hash_map).unwrap(), @"[[[1, 2], 3]]");
    }
}
