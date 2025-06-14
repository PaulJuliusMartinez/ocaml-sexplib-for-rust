use std::borrow::Cow;
use std::num::{ParseFloatError, ParseIntError};
use std::str::FromStr;

use serde::de::{
    self, DeserializeSeed, EnumAccess, IntoDeserializer, MapAccess, SeqAccess, VariantAccess,
    Visitor,
};
use serde::Deserialize;

use crate::error::{Error, Result};
use crate::Sexp;

fn error<V>(s: &str) -> Result<V> {
    Err(Error::DeserializationError(s.to_string()))
}

fn error_string<V>(s: String) -> Result<V> {
    Err(Error::DeserializationError(s))
}

fn parse_int_error(err: ParseIntError) -> Error {
    Error::DeserializationError(format!("unable to parse int: {:#?}", err))
}

fn parse_float_error(err: ParseFloatError) -> Error {
    Error::DeserializationError(format!("unable to parse float: {:#?}", err))
}

// 'a: Lifetime of the data in the Sexp<'a>
// 'de: Lifetime of the thing that is deserializing the Sexp<'a>
#[derive(Debug)]
pub struct Deserializer<'a: 'de, 'de> {
    input_sexp: &'de Sexp<'a>,
    cursor: Vec<(&'de [Sexp<'a>], usize)>,
}

// Someday: This should just be `{ sexps: &'de [Sexp<'a>}, index: usize }` maybe,
// rather than relying on `cursor` always pointing to the correct thing when functions
// are called on this.
// 'a: Lifetime of the data in the Sexp<'a>
// 'de: Lifetime of the thing that is deserializing the Sexp<'a>
// 'b: Lifetime of the reference to the Deserializer<'a, 'de>
pub struct SeqDeserializer<'a: 'de + 'b, 'de: 'b, 'b>(&'b mut Deserializer<'a, 'de>);
pub struct MapDeserializer<'a: 'de + 'b, 'de: 'b, 'b>(&'b mut Deserializer<'a, 'de>);
pub struct EnumDeserializer<'a: 'de + 'b, 'de: 'b, 'b>(&'b mut Deserializer<'a, 'de>);

impl<'a: 'de, 'de> Deserializer<'a, 'de> {
    pub fn from_sexp(sexp: &'de Sexp<'a>) -> Self {
        Deserializer {
            input_sexp: sexp,
            cursor: vec![(std::array::from_ref(sexp).as_slice(), 0)],
        }
    }

    fn next_atom(&mut self) -> Result<&'de Cow<'a, str>> {
        let cursor = self.cursor.last_mut().unwrap();
        match cursor.0.get(cursor.1) {
            None => error("exhausted current input"),
            Some(Sexp::List(_)) => error("expected atom"),
            Some(Sexp::Atom(atom)) => {
                cursor.1 += 1;
                Ok(atom)
            }
        }
    }

    fn parse_int_atom<T>(&mut self) -> Result<T>
    where
        T: FromStr<Err = ParseIntError>,
    {
        self.next_atom()?
            .as_ref()
            .parse::<T>()
            .map_err(parse_int_error)
    }

    fn parse_float_atom<T>(&mut self) -> Result<T>
    where
        T: FromStr<Err = ParseFloatError>,
    {
        self.next_atom()?
            .as_ref()
            .parse::<T>()
            .map_err(parse_float_error)
    }

    fn step_into_list(&mut self) -> Result<()> {
        let cursor = self.cursor.last_mut().unwrap();
        match cursor.0.get(cursor.1) {
            None => return error("exhaused current input"),
            Some(Sexp::Atom(_)) => error("expected list"),
            Some(Sexp::List(list)) => {
                cursor.1 += 1;
                self.cursor.push((list.as_slice(), 0));
                Ok(())
            }
        }
    }

    fn step_out_of_list(&mut self) {
        self.cursor.pop();
    }

    fn start_deserializing_seq<'b>(&'b mut self) -> Result<SeqDeserializer<'a, 'de, 'b>> {
        self.step_into_list()?;
        Ok(SeqDeserializer(self))
    }

    fn finish_deserializing_seq(&mut self) {
        self.step_out_of_list();
    }

    fn start_deserializing_map<'b>(&'b mut self) -> Result<MapDeserializer<'a, 'de, 'b>> {
        self.step_into_list()?;
        Ok(MapDeserializer(self))
    }

    fn finish_deserializing_map(&mut self) {
        self.step_out_of_list();
    }

    fn start_deserializing_non_unit_enum<'b>(
        &'b mut self,
    ) -> Result<EnumDeserializer<'a, 'de, 'b>> {
        self.step_into_list()?;
        Ok(EnumDeserializer(self))
    }

    fn finish_deserializing_non_unit_enum(&mut self) {
        self.step_out_of_list();
    }

    fn curr_list_len(&self) -> usize {
        let (sexps, _) = self.cursor.last().unwrap();
        sexps.len()
    }

    fn num_remaining_elems_to_process(&self) -> usize {
        let (sexps, index) = self.cursor.last().unwrap();
        sexps.len() - *index
    }

    fn have_more_elems_to_process(&self) -> bool {
        self.num_remaining_elems_to_process() > 0
    }
}

pub fn from_sexp<'a: 'de, 'de, T>(sexp: &'de Sexp<'a>) -> Result<T>
where
    T: Deserialize<'de>,
{
    let mut deserializer = Deserializer::from_sexp(sexp);
    let t = T::deserialize(&mut deserializer)?;
    // Someday: Check `deserializer` for unprocessed data
    Ok(t)
}

macro_rules! impl_deserialize_int {
    ($deserialize_int:ident, $visit_int:ident) => {
        fn $deserialize_int<V>(self, visitor: V) -> Result<V::Value>
        where
            V: Visitor<'de>,
        {
            visitor.$visit_int(self.parse_int_atom()?)
        }
    };
}

macro_rules! impl_deserialize_float {
    ($deserialize_float:ident, $visit_float:ident) => {
        fn $deserialize_float<V>(self, visitor: V) -> Result<V::Value>
        where
            V: Visitor<'de>,
        {
            visitor.$visit_float(self.parse_float_atom()?)
        }
    };
}

impl<'a: 'de + 'b, 'de: 'b, 'b> de::Deserializer<'de> for &'b mut Deserializer<'a, 'de> {
    type Error = Error;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let cursor = self.cursor.last_mut().unwrap();
        match cursor.0.get(cursor.1) {
            None => error("exhaused current input"),
            Some(Sexp::Atom(_)) => self.deserialize_str(visitor),
            Some(Sexp::List(_)) => self.deserialize_seq(visitor),
        }
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let b = match self.next_atom()?.as_ref() {
            "true" => true,
            "false" => false,
            _ => return error("expected `true` or `false`"),
        };
        visitor.visit_bool(b)
    }

    impl_deserialize_int!(deserialize_i8, visit_i8);
    impl_deserialize_int!(deserialize_i16, visit_i16);
    impl_deserialize_int!(deserialize_i32, visit_i32);
    impl_deserialize_int!(deserialize_i64, visit_i64);
    impl_deserialize_int!(deserialize_i128, visit_i128);

    impl_deserialize_int!(deserialize_u8, visit_u8);
    impl_deserialize_int!(deserialize_u16, visit_u16);
    impl_deserialize_int!(deserialize_u32, visit_u32);
    impl_deserialize_int!(deserialize_u64, visit_u64);
    impl_deserialize_int!(deserialize_u128, visit_u128);

    impl_deserialize_float!(deserialize_f32, visit_f32);
    impl_deserialize_float!(deserialize_f64, visit_f64);

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let mut chars = self.next_atom()?.chars();
        match chars.next() {
            None => error("Expected char but got empty string"),
            Some(ch) => {
                if chars.next().is_some() {
                    error("Expected single char but got multi-char string")
                } else {
                    visitor.visit_char(ch)
                }
            }
        }
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_borrowed_str(self.next_atom()?.as_ref())
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_borrowed_str(self.next_atom()?.as_ref())
    }

    fn deserialize_bytes<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_bytes` not implemented yet")
    }

    fn deserialize_byte_buf<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_byte_buf` not implemented yet")
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.step_into_list()?;
        match self.curr_list_len() {
            0 => visitor.visit_none(),
            1 => visitor.visit_some(self),
            _ => error("Expected Some value for option (single-element-list), but got list with multiple elements"),
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.step_into_list()?;
        match self.curr_list_len() {
            0 => {
                self.step_out_of_list();
                visitor.visit_unit()
            }
            _ => error("Expected empty list for (), i.e,. unit, but list contained values"),
        }
    }

    fn deserialize_unit_struct<V>(self, name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let atom = self.next_atom()?;
        if atom.as_ref() == name {
            visitor.visit_unit()
        } else {
            error_string(format!("Expected atom: {:?}, got: {:?}", name, atom))
        }
    }

    fn deserialize_newtype_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let seq_access = self.start_deserializing_seq()?;
        match visitor.visit_seq(seq_access) {
            Ok(value) => {
                // Someday: Make sure we've processed all of the elements?
                // Or is this guaranteed by impl of `SeqDeserializer`?
                self.finish_deserializing_seq();
                Ok(value)
            }
            Err(err) => Err(err),
        }
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let seq_access = self.start_deserializing_seq()?;
        // Someday: This is silly that I have to access self via `seq_access.0`...
        // Maybe this goes away if `seq_access` is improved?
        let curr_list_len = seq_access.0.curr_list_len();
        if curr_list_len != len {
            error_string(format!(
                "Expected list of length {len} for tuple, but got list of length {curr_list_len}"
            ))
        } else {
            match visitor.visit_seq(seq_access) {
                Ok(value) => {
                    // Someday: Make sure we've processed all of the elements?
                    // Or is this guaranteed by impl of `SeqDeserializer`?
                    self.finish_deserializing_seq();
                    Ok(value)
                }
                Err(err) => Err(err),
            }
        }
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_tuple(len, visitor)
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let map_access = self.start_deserializing_map()?;
        match visitor.visit_map(map_access) {
            Ok(value) => {
                // Someday: Make sure we've processed all of the elements?
                // Or is this guaranteed by impl of `MapDeserializer`?
                self.finish_deserializing_map();
                Ok(value)
            }
            Err(err) => Err(err),
        }
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_map(visitor)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let cursor = self.cursor.last_mut().unwrap();
        match cursor.0.get(cursor.1) {
            None => error("exhausted current input"),
            Some(Sexp::Atom(atom)) => {
                // `IntoDeserializer` is implemented for `&str` and returns a
                // `StrDeserializer`, which implements a special `EnumAccess`
                // that only knows how to handle unit variants.
                cursor.1 += 1;
                visitor.visit_enum(atom.as_ref().into_deserializer())
            }
            Some(Sexp::List(_)) => {
                let enum_access = self.start_deserializing_non_unit_enum()?;
                match visitor.visit_enum(enum_access) {
                    Ok(value) => {
                        self.finish_deserializing_non_unit_enum();
                        Ok(value)
                    }
                    Err(err) => Err(err),
                }
            }
        }
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_any(visitor)
    }
}

impl<'a: 'de + 'b, 'de: 'b, 'b> SeqAccess<'de> for SeqDeserializer<'a, 'de, 'b> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>>
    where
        T: DeserializeSeed<'de>,
    {
        if self.0.have_more_elems_to_process() {
            seed.deserialize(&mut *self.0).map(Some)
        } else {
            Ok(None)
        }
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.0.num_remaining_elems_to_process())
    }
}

impl<'a: 'de + 'b, 'de: 'b, 'b> MapAccess<'de> for MapDeserializer<'a, 'de, 'b> {
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: DeserializeSeed<'de>,
    {
        if self.0.have_more_elems_to_process() {
            self.0.step_into_list()?;
            match self.0.curr_list_len() {
                2 => seed.deserialize(&mut *self.0).map(Some),
                _ => error("Expected two-element list for key-value-pair"),
            }
        } else {
            Ok(None)
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: DeserializeSeed<'de>,
    {
        let result = seed.deserialize(&mut *self.0);
        if result.is_ok() {
            self.0.step_out_of_list();
        }
        result
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.0.num_remaining_elems_to_process())
    }
}

impl<'a: 'de + 'b, 'de: 'b, 'b> EnumAccess<'de> for EnumDeserializer<'a, 'de, 'b> {
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: DeserializeSeed<'de>,
    {
        let val = seed.deserialize(&mut *self.0)?;
        Ok((val, self))
    }
}

impl<'a: 'de + 'b, 'de: 'b, 'b> VariantAccess<'de> for EnumDeserializer<'a, 'de, 'b> {
    type Error = Error;

    fn unit_variant(self) -> Result<()> {
        error("`EnumDeserializer::unit_variant` not implemented yet")
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value>
    where
        T: DeserializeSeed<'de>,
    {
        let curr_list_len = self.0.curr_list_len();
        if curr_list_len != 2 {
            error_string(format!(
                "expected list of length 2 for newtype variant; got length {curr_list_len}"
            ))
        } else {
            seed.deserialize(&mut *self.0)
        }
    }

    fn tuple_variant<V>(self, len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let curr_list_len = self.0.curr_list_len();
        if curr_list_len != 1 + len {
            error_string(format!(
                "expected list of length {len} for tuple variant; got length {curr_list_len}"
            ))
        } else {
            let seq_access = SeqDeserializer(self.0);
            visitor.visit_seq(seq_access)
        }
    }

    fn struct_variant<V>(self, _fields: &'static [&'static str], visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let map_access = MapDeserializer(self.0);
        visitor.visit_map(map_access)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use insta::assert_debug_snapshot;

    fn a(s: &str) -> Sexp {
        Sexp::Atom(Cow::from(s))
    }

    fn l(sexps: Vec<Sexp>) -> Sexp {
        Sexp::List(sexps)
    }

    #[test]
    fn test_primitives() {
        assert_eq!(true, from_sexp(&a("true")).unwrap());
        assert_eq!(false, from_sexp(&a("false")).unwrap());

        assert_eq!(-128i8, from_sexp(&a("-128")).unwrap());
        assert_eq!(-32_738i16, from_sexp(&a("-32738")).unwrap());
        assert_eq!(-2_000_000_000i32, from_sexp(&a("-2000000000")).unwrap());
        assert_eq!(-1i64, from_sexp(&a("-1")).unwrap());
        assert_eq!(0i128, from_sexp(&a("0")).unwrap());

        assert_eq!(255u8, from_sexp(&a("255")).unwrap());
        assert_eq!(65_535u16, from_sexp(&a("65535")).unwrap());
        assert_eq!(2_000_000_000u32, from_sexp(&a("2000000000")).unwrap());
        assert_eq!(1u64, from_sexp(&a("1")).unwrap());
        assert_eq!(0u128, from_sexp(&a("0")).unwrap());

        assert_eq!(0.1f32, from_sexp(&a("0.1")).unwrap());
        assert_eq!(-3.2f32, from_sexp(&a("-3.2")).unwrap());
    }

    #[test]
    fn test_char() {
        assert_eq!('a', from_sexp(&a("a")).unwrap());
        assert_eq!('α', from_sexp(&a("α")).unwrap());

        assert_debug_snapshot!(from_sexp::<char>(&a("")), @r#"
        Err(
            DeserializationError(
                "Expected char but got empty string",
            ),
        )
        "#);

        assert_debug_snapshot!(from_sexp::<char>(&a("abc")), @r#"
        Err(
            DeserializationError(
                "Expected single char but got multi-char string",
            ),
        )
        "#);
    }

    #[test]
    fn test_strings() {
        assert_eq!("abc", from_sexp::<&str>(&a("abc")).unwrap());
        assert_eq!("123", from_sexp::<String>(&a("123")).unwrap());
    }

    #[test]
    fn test_option() {
        assert_eq!(None, from_sexp::<Option<i32>>(&l(vec![])).unwrap());
        assert_eq!(Some(3), from_sexp::<Option<i32>>(&l(vec![a("3")])).unwrap());

        assert_debug_snapshot!(from_sexp::<Option<i32>>(&a("1")), @r#"
        Err(
            DeserializationError(
                "expected list",
            ),
        )
        "#);

        assert_debug_snapshot!(from_sexp::<Option<i32>>(&l(vec![a("1"), a("2")])), @r#"
        Err(
            DeserializationError(
                "Expected Some value for option (single-element-list), but got list with multiple elements",
            ),
        )
        "#);
    }

    #[test]
    fn test_unit() {
        assert_eq!((), from_sexp::<()>(&l(vec![])).unwrap());

        assert_debug_snapshot!(from_sexp::<()>(&a("unit")), @r#"
        Err(
            DeserializationError(
                "expected list",
            ),
        )
        "#);

        assert_debug_snapshot!(from_sexp::<()>(&l(vec![a("unit")])), @r#"
        Err(
            DeserializationError(
                "Expected empty list for (), i.e,. unit, but list contained values",
            ),
        )
        "#);
    }

    #[test]
    fn test_unit_struct() {
        #[derive(Debug, Deserialize, PartialEq, Eq)]
        struct UnitStruct;
        assert_eq!(
            UnitStruct,
            from_sexp::<UnitStruct>(&a("UnitStruct")).unwrap()
        );

        assert_debug_snapshot!(from_sexp::<UnitStruct>(&a("unit_struct")), @r#"
        Err(
            DeserializationError(
                "Expected atom: \"UnitStruct\", got: \"unit_struct\"",
            ),
        )
        "#);

        assert_debug_snapshot!(from_sexp::<UnitStruct>(&l(vec![])), @r#"
        Err(
            DeserializationError(
                "expected atom",
            ),
        )
        "#);
    }

    #[test]
    fn test_newtype_struct() {
        #[derive(Debug, Deserialize, PartialEq, Eq)]
        struct NewtypeStruct(u8);
        assert_eq!(
            NewtypeStruct(1),
            from_sexp::<NewtypeStruct>(&a("1")).unwrap()
        );

        assert_debug_snapshot!(from_sexp::<NewtypeStruct>(&l(vec![a("NewtypeStruct"), a("1")])), @r#"
        Err(
            DeserializationError(
                "expected atom",
            ),
        )
        "#);
    }

    #[test]
    fn test_seq() {
        assert_eq!(
            vec![true, false],
            from_sexp::<Vec<bool>>(&l(vec![a("true"), a("false")])).unwrap()
        );

        assert_eq!(
            vec![1u8, 2u8],
            from_sexp::<Vec<u8>>(&l(vec![a("1"), a("2")])).unwrap()
        );

        assert_eq!(
            vec![(), (), ()],
            from_sexp::<Vec<()>>(&l(vec![l(vec![]), l(vec![]), l(vec![])])).unwrap()
        );
    }

    #[test]
    fn test_tuple_and_tuple_struct() {
        #[derive(Debug, Deserialize, PartialEq, Eq)]
        struct TupleStruct<'a>(i8, (bool, i8), &'a str);

        let sexp = l(vec![a("1"), l(vec![a("true"), a("2")]), a("abc")]);

        assert_eq!(
            (1, (true, 2), "abc"),
            from_sexp::<(i8, (bool, i8), &str)>(&sexp).unwrap(),
        );
        assert_eq!(
            TupleStruct(1, (true, 2), "abc"),
            from_sexp::<TupleStruct>(&sexp).unwrap(),
        );

        assert_debug_snapshot!(from_sexp::<(i8, bool, String)>(&l(vec![a("0"), a("false")])), @r#"
        Err(
            DeserializationError(
                "Expected list of length 3 for tuple, but got list of length 2",
            ),
        )
        "#);

        assert_debug_snapshot!(from_sexp::<TupleStruct>(&l(vec![a("0"), a("false")])), @r#"
        Err(
            DeserializationError(
                "Expected list of length 3 for tuple, but got list of length 2",
            ),
        )
        "#);
    }

    #[test]
    fn test_map() {
        use std::collections::BTreeMap;

        let test = l(vec![
            l(vec![l(vec![a("1"), a("foo")]), l(vec![a("2"), a("two")])]),
            a("true"),
        ]);

        assert_debug_snapshot!(from_sexp::<(BTreeMap<i32, &str>, bool)>(&test).unwrap(), @r#"
        (
            {
                1: "foo",
                2: "two",
            },
            true,
        )
        "#);

        fn f(sexp: &Sexp) -> Result<BTreeMap<i32, i32>> {
            from_sexp::<BTreeMap<i32, i32>>(sexp)
        }

        assert_debug_snapshot!(f(&l(vec![])).unwrap(), @r#"{}"#);

        let atom_kvp = l(vec![a("1")]);
        assert_debug_snapshot!(f(&atom_kvp).unwrap_err(), @r#"
        DeserializationError(
            "expected list",
        )
        "#);

        let unit_kvp = l(vec![l(vec![])]);
        assert_debug_snapshot!(f(&unit_kvp).unwrap_err(), @r#"
        DeserializationError(
            "Expected two-element list for key-value-pair",
        )
        "#);

        let one_element_kvp = l(vec![l(vec![a("1")])]);
        assert_debug_snapshot!(f(&one_element_kvp).unwrap_err(), @r#"
        DeserializationError(
            "Expected two-element list for key-value-pair",
        )
        "#);

        let three_element_kvp = l(vec![l(vec![a("1"), a("2"), a("3")])]);
        assert_debug_snapshot!(f(&three_element_kvp).unwrap_err(), @r#"
        DeserializationError(
            "Expected two-element list for key-value-pair",
        )
        "#);
    }

    #[test]
    fn test_struct() {
        #[derive(Debug, Deserialize, PartialEq, Eq)]
        struct Struct {
            x: i32,
            y: bool,
        }

        let sexp = l(vec![
            a("start"),
            l(vec![l(vec![a("x"), a("1")]), l(vec![a("y"), a("true")])]),
            a("end"),
        ]);

        assert_eq!(
            ("start", Struct { x: 1, y: true }, "end"),
            from_sexp::<(&str, Struct, &str)>(&sexp).unwrap(),
        );

        let atom_kvp = l(vec![a("key: value")]);
        let unit_kvp = l(vec![l(vec![])]);
        let one_element_kvp = l(vec![l(vec![a("x")])]);
        let unknown_one_element_kvp = l(vec![l(vec![a("z")])]);
        let three_element_kvp = l(vec![l(vec![a("x"), a("1"), a("true")])]);

        assert_debug_snapshot!(from_sexp::<Struct>(&atom_kvp), @r#"
        Err(
            DeserializationError(
                "expected list",
            ),
        )
        "#);

        assert_debug_snapshot!(from_sexp::<Struct>(&unit_kvp), @r#"
        Err(
            DeserializationError(
                "Expected two-element list for key-value-pair",
            ),
        )
        "#);

        assert_debug_snapshot!(from_sexp::<Struct>(&one_element_kvp), @r#"
        Err(
            DeserializationError(
                "Expected two-element list for key-value-pair",
            ),
        )
        "#);

        assert_debug_snapshot!(from_sexp::<Struct>(&unknown_one_element_kvp), @r#"
        Err(
            DeserializationError(
                "Expected two-element list for key-value-pair",
            ),
        )
        "#);

        assert_debug_snapshot!(from_sexp::<Struct>(&three_element_kvp), @r#"
        Err(
            DeserializationError(
                "Expected two-element list for key-value-pair",
            ),
        )
        "#);

        // Mostly testing serde's internals here.

        // Missing keys
        assert_debug_snapshot!(from_sexp::<Struct>(&l(vec![])), @r#"
        Err(
            DeserializationError(
                "missing field `x`",
            ),
        )
        "#);

        // Duplicate key
        assert_debug_snapshot!(from_sexp::<Struct>(&l(vec![l(vec![a("x"), a("1")]), l(vec![a("x"), a("1")])])), @r#"
        Err(
            DeserializationError(
                "duplicate field `x`",
            ),
        )
        "#);

        // Extra_key is ignored
        let sexp = l(vec![
            l(vec![a("x"), a("1")]),
            l(vec![a("y"), a("true")]),
            l(vec![a("z"), a("0")]),
        ]);
        assert_debug_snapshot!(from_sexp::<Struct>(&sexp), @r"
        Ok(
            Struct {
                x: 1,
                y: true,
            },
        )
        ");
    }

    #[test]
    fn test_variant() {
        #[derive(Debug, Deserialize, PartialEq, Eq)]
        enum Variant {
            Unit,
            Newtype(i32),
            Tuple(i32, i32),
            Struct { x: i32 },
        }

        // Check Unit

        let unit_sexp = l(vec![a("start"), a("Unit"), a("end")]);

        assert_eq!(
            Ok(("start", Variant::Unit, "end")),
            from_sexp::<(&str, Variant, &str)>(&unit_sexp),
        );

        assert_debug_snapshot!(from_sexp::<Variant>(&a("Newtype")), @r#"
        Err(
            DeserializationError(
                "invalid type: unit variant, expected newtype variant",
            ),
        )
        "#);

        // Check Newtype

        let newtype_sexp = l(vec![a("start"), l(vec![a("Newtype"), a("1")]), a("end")]);

        assert_eq!(
            Ok(("start", Variant::Newtype(1), "end")),
            from_sexp::<(&str, Variant, &str)>(&newtype_sexp),
        );

        assert_debug_snapshot!(from_sexp::<Variant>(&l(vec![a("Newtype")])), @r#"
        Err(
            DeserializationError(
                "expected list of length 2 for newtype variant; got length 1",
            ),
        )
        "#);

        assert_debug_snapshot!(from_sexp::<Variant>(&l(vec![a("Newtype"), a("1"), a("2")])), @r#"
        Err(
            DeserializationError(
                "expected list of length 2 for newtype variant; got length 3",
            ),
        )
        "#);

        // Check Tuple

        let tuple_sexp = l(vec![
            a("start"),
            l(vec![a("Tuple"), a("1"), a("2")]),
            a("end"),
        ]);

        assert_eq!(
            Ok(("start", Variant::Tuple(1, 2), "end")),
            from_sexp::<(&str, Variant, &str)>(&tuple_sexp),
        );

        assert_debug_snapshot!(from_sexp::<Variant>(&l(vec![a("Tuple"), a("1")])), @r#"
        Err(
            DeserializationError(
                "expected list of length 2 for tuple variant; got length 2",
            ),
        )
        "#);

        // Check Struct

        let struct_sexp = l(vec![
            a("start"),
            l(vec![a("Struct"), l(vec![a("x"), a("1")])]),
            a("end"),
        ]);

        assert_eq!(
            Ok(("start", Variant::Struct { x: 1 }, "end")),
            from_sexp::<(&str, Variant, &str)>(&struct_sexp),
        );

        assert_debug_snapshot!(from_sexp::<Variant>(&l(vec![a("Struct"), a("1")])), @r#"
        Err(
            DeserializationError(
                "expected list",
            ),
        )
        "#);

        assert_debug_snapshot!(from_sexp::<Variant>(&l(vec![a("Struct"), l(vec![a("x"), a("1"), a("bad")])])), @r#"
        Err(
            DeserializationError(
                "Expected two-element list for key-value-pair",
            ),
        )
        "#);
    }
}
