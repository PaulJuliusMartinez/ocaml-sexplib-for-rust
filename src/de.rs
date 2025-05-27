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

fn error<V>(f: &str) -> Result<V> {
    Err(Error::DeserializationError(f.to_string()))
}

fn parse_int_error(err: ParseIntError) -> Error {
    Error::DeserializationError(format!("unable to parse int: {:#?}", err))
}

fn parse_float_error(err: ParseFloatError) -> Error {
    Error::DeserializationError(format!("unable to parse float: {:#?}", err))
}

pub struct Deserializer<'a: 'de, 'de> {
    input_sexp: &'de Sexp<'a>,
    cursor: Vec<(&'de [Sexp<'a>], usize)>,
}

// Someday: This should just be `{ sexps: &'de [Sexp<'a>}, index: usize }` maybe,
// rather than relying on `cursor` always pointing to the correct thing when functions
// are called on this.
pub struct SeqDeserializer<'a: 'de + 'b, 'de: 'b, 'b>(&'b mut Deserializer<'a, 'de>);

impl<'a: 'de, 'de> Deserializer<'a, 'de> {
    pub fn from_sexp(sexp: &'de Sexp<'a>) -> Self {
        Deserializer {
            input_sexp: sexp,
            cursor: vec![(std::array::from_ref(sexp).as_slice(), 0)],
        }
    }

    fn next_atom<'b>(&'b mut self) -> Result<&'b Cow<'a, str>> {
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

    fn start_deserializing_seq<'b>(&'b mut self) -> Result<SeqDeserializer<'a, 'de, 'b>> {
        let (sexps, index) = self.cursor.last().unwrap();
        match sexps.get(*index) {
            None => return error("exhaused current input"),
            Some(Sexp::Atom(_)) => return error("expected list"),
            Some(Sexp::List(list)) => {
                self.cursor.push((list.as_slice(), 0));
            }
        }

        Ok(SeqDeserializer(self))
    }

    fn have_more_elems_to_process(&self) -> bool {
        let (sexps, index) = self.cursor.last().unwrap();
        *index < sexps.len()
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

    fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("Sexp format is not self-describing")
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

    fn deserialize_char<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_char` not implemented yet")
    }

    fn deserialize_str<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_str` not implemented yet")
    }

    fn deserialize_string<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_string` not implemented yet")
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

    fn deserialize_option<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_option` not implemented yet")
    }

    fn deserialize_unit<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_unit` not implemented yet")
    }

    fn deserialize_unit_struct<V>(self, _name: &'static str, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_unit_struct` not implemented yet")
    }

    fn deserialize_newtype_struct<V>(self, _name: &'static str, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_newtype_struct` not implemented yet")
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let seq_access = self.start_deserializing_seq()?;
        let value = visitor.visit_seq(seq_access)?;
        // Someday: Make sure we've processed all of the elements?
        Ok(value)
    }

    fn deserialize_tuple<V>(self, _len: usize, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_tuple` not implemented yet")
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        _visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_tuple_struct` not implemented yet")
    }

    fn deserialize_map<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_map` not implemented yet")
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_struct` not implemented yet")
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_enum` not implemented yet")
    }

    fn deserialize_identifier<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_identifier` not implemented yet")
    }

    fn deserialize_ignored_any<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        error("`deserialize_ignored_any` not implemented yet")
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
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn test_seq() {
        assert_eq!(
            vec![true, false],
            from_sexp::<Vec<bool>>(&l(vec![a("true"), a("false")])).unwrap()
        );

        assert_eq!(
            vec![1u8, 2u8],
            from_sexp::<Vec<u8>>(&l(vec![a("1"), a("2")])).unwrap()
        );
    }
}
