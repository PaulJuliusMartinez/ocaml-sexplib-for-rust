use std::io;
use std::num::{ParseFloatError, ParseIntError};

use serde::de::{
    self, DeserializeSeed, EnumAccess, IntoDeserializer, MapAccess, SeqAccess, VariantAccess,
    Visitor,
};
use serde::Deserialize;

use crate::error::{Error, Result};
use crate::tokenizer::Token;

pub struct Deserializer {
    // Someday: This should be a peekable?
    tokens: Vec<Token>,
}

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

impl Deserializer {
    fn new(mut tokens: Vec<Token>) -> Deserializer {
        tokens.reverse();
        Deserializer { tokens }
    }

    fn next(&mut self) -> Result<Option<Token>> {
        Ok(self.tokens.pop())
    }

    fn peek(&mut self) -> Result<Option<&Token>> {
        Ok(self.tokens.last())
    }

    fn advance(&mut self) {
        self.tokens.pop();
    }

    fn expect_atom(&mut self) -> Result<Vec<u8>> {
        match self.next()? {
            None => error("expected atom; reached end of input"),
            Some(Token::LeftParen) => error("expected atom; got list"),
            Some(Token::RightParen) => error("expected atom; got end of list"),
            Some(Token::Atom(bytes)) => Ok(bytes),
        }
    }

    fn expect_start_of_list(&mut self) -> Result<()> {
        match self.next()? {
            None => error("expected atom; reached end of input"),
            Some(Token::LeftParen) => Ok(()),
            Some(Token::RightParen | Token::Atom(_)) => error("expected list"),
        }
    }

    fn expect_end_of_list(&mut self) -> Result<()> {
        match self.next()? {
            None => error("expected atom; reached end of input"),
            Some(Token::RightParen) => Ok(()),
            Some(Token::LeftParen) => error("expected end of list"),
            Some(Token::Atom(_)) => error("expected end of list"),
        }
    }
}

fn from_tokens<'de, T>(tokens: Vec<Token>) -> Result<T>
where
    T: Deserialize<'de>,
{
    let mut deserializer = Deserializer::new(tokens);
    let t = T::deserialize(&mut deserializer)?;
    // Someday: Check `deserializer` for remaining tokens
    Ok(t)
}

macro_rules! impl_deserialize_int {
    ($deserialize_int:ident, $int_t:ty, $visit_int:ident) => {
        fn $deserialize_int<V>(self, visitor: V) -> Result<V::Value>
        where
            V: Visitor<'de>,
        {
            let atom = self.expect_atom()?;
            match std::str::from_utf8(atom.as_slice()) {
                Err(_) => error("expected int literal; got invalid UTF-8"),
                Ok(s) => {
                    let i = s.parse::<$int_t>().map_err(parse_int_error)?;
                    visitor.$visit_int(i)
                }
            }
        }
    };
}

macro_rules! impl_deserialize_float {
    ($deserialize_float:ident, $float_t:ty, $visit_float:ident) => {
        fn $deserialize_float<V>(self, visitor: V) -> Result<V::Value>
        where
            V: Visitor<'de>,
        {
            let atom = self.expect_atom()?;
            match std::str::from_utf8(atom.as_slice()) {
                Err(_) => error("expected float literal; got invalid UTF-8"),
                Ok(s) => {
                    let i = s.parse::<$float_t>().map_err(parse_float_error)?;
                    visitor.$visit_float(i)
                }
            }
        }
    };
}

impl<'de: 'a, 'a> de::Deserializer<'de> for &'a mut Deserializer {
    type Error = Error;

    fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!();
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let b = match self.expect_atom()?.as_slice() {
            b"true" => true,
            b"false" => false,
            _ => return error("expected `true` or `false`"),
        };
        visitor.visit_bool(b)
    }

    impl_deserialize_int!(deserialize_i8, i8, visit_i8);
    impl_deserialize_int!(deserialize_i16, i16, visit_i16);
    impl_deserialize_int!(deserialize_i32, i32, visit_i32);
    impl_deserialize_int!(deserialize_i64, i64, visit_i64);
    impl_deserialize_int!(deserialize_i128, i128, visit_i128);

    impl_deserialize_int!(deserialize_u8, u8, visit_u8);
    impl_deserialize_int!(deserialize_u16, u16, visit_u16);
    impl_deserialize_int!(deserialize_u32, u32, visit_u32);
    impl_deserialize_int!(deserialize_u64, u64, visit_u64);
    impl_deserialize_int!(deserialize_u128, u128, visit_u128);

    impl_deserialize_float!(deserialize_f32, f32, visit_f32);
    impl_deserialize_float!(deserialize_f64, f64, visit_f64);

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let atom = self.expect_atom()?;
        let mut chars = match std::str::from_utf8(atom.as_slice()) {
            Ok(s) => s.chars(),
            Err(_) => return error("expected valid UTF-8 for char value"),
        };

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
        // Someday: Make `Token` have a `Cow`, so this can pass a borrowed string
        // if possible.
        let atom = self.expect_atom()?;
        match std::str::from_utf8(atom.as_slice()) {
            Ok(s) => visitor.visit_string(s.to_owned()),
            Err(_) => error("atom was not valid UTF-8"),
        }
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    fn deserialize_bytes<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!();
    }

    fn deserialize_byte_buf<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!();
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.expect_start_of_list()?;
        match self.peek()? {
            None => error(" reached end of input"),
            Some(&Token::RightParen) => {
                self.advance();
                visitor.visit_none()
            }
            Some(&Token::LeftParen | &Token::Atom(_)) => {
                let value = visitor.visit_some(&mut *self)?;
                self.expect_end_of_list()?;
                Ok(value)
            }
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.expect_start_of_list()?;
        self.expect_end_of_list()?;
        visitor.visit_unit()
    }

    fn deserialize_unit_struct<V>(self, name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let atom = self.expect_atom()?;
        match std::str::from_utf8(atom.as_slice()) {
            Ok(s) => {
                if s == name {
                    visitor.visit_unit()
                } else {
                    error_string(format!("Expected atom: {:?}, got: {:?}", name, s))
                }
            }
            Err(_) => error("atom was not valid UTF-8"),
        }
    }

    fn deserialize_newtype_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!();
    }

    fn deserialize_tuple<V>(self, _len: usize, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!();
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
        unimplemented!();
    }

    fn deserialize_map<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!();
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
        unimplemented!();
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
        unimplemented!();
    }

    fn deserialize_identifier<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!();
    }

    fn deserialize_ignored_any<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!();
    }
}

impl<'de> SeqAccess<'de> for Deserializer {
    type Error = Error;

    fn next_element_seed<T>(&mut self, _seed: T) -> Result<Option<T::Value>>
    where
        T: DeserializeSeed<'de>,
    {
        unimplemented!();
    }
}

impl<'de> MapAccess<'de> for Deserializer {
    type Error = Error;

    fn next_key_seed<K>(&mut self, _seed: K) -> Result<Option<K::Value>>
    where
        K: DeserializeSeed<'de>,
    {
        unimplemented!();
    }

    fn next_value_seed<V>(&mut self, _seed: V) -> Result<V::Value>
    where
        V: DeserializeSeed<'de>,
    {
        unimplemented!();
    }
}

impl<'de> EnumAccess<'de> for Deserializer {
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V>(self, _seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: DeserializeSeed<'de>,
    {
        unimplemented!();
    }
}

impl<'de> VariantAccess<'de> for Deserializer {
    type Error = Error;

    fn unit_variant(self) -> Result<()> {
        unimplemented!();
    }

    fn newtype_variant_seed<T>(self, _seed: T) -> Result<T::Value>
    where
        T: DeserializeSeed<'de>,
    {
        unimplemented!();
    }

    fn tuple_variant<V>(self, _len: usize, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!();
    }

    fn struct_variant<V>(self, _fields: &'static [&'static str], _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use insta::assert_debug_snapshot;

    fn a(s: &str) -> Token {
        Token::Atom(s.as_bytes().to_vec())
    }

    const LP: Token = Token::LeftParen;
    const RP: Token = Token::RightParen;

    #[allow(clippy::bool_assert_comparison)]
    #[test]
    fn test_primitives() {
        assert_eq!(true, from_tokens(vec![a("true")]).unwrap());
        assert_eq!(false, from_tokens(vec![a("false")]).unwrap());

        assert_eq!(-128i8, from_tokens(vec![a("-128")]).unwrap());
        assert_eq!(-32_738i16, from_tokens(vec![a("-32738")]).unwrap());
        assert_eq!(
            -2_000_000_000i32,
            from_tokens(vec![a("-2000000000")]).unwrap()
        );
        assert_eq!(-1i64, from_tokens(vec![a("-1")]).unwrap());
        assert_eq!(0i128, from_tokens(vec![a("0")]).unwrap());

        assert_eq!(255u8, from_tokens(vec![a("255")]).unwrap());
        assert_eq!(65_535u16, from_tokens(vec![a("65535")]).unwrap());
        assert_eq!(
            2_000_000_000u32,
            from_tokens(vec![a("2000000000")]).unwrap()
        );
        assert_eq!(1u64, from_tokens(vec![a("1")]).unwrap());
        assert_eq!(0u128, from_tokens(vec![a("0")]).unwrap());

        assert_eq!(0.1f32, from_tokens(vec![a("0.1")]).unwrap());
        assert_eq!(-3.2f32, from_tokens(vec![a("-3.2")]).unwrap());
    }

    #[test]
    fn test_char() {
        assert_eq!('a', from_tokens(vec![a("a")]).unwrap());
        assert_eq!('α', from_tokens(vec![a("α")]).unwrap());

        assert_debug_snapshot!(from_tokens::<char>(vec![a("")]), @r#"
        Err(
            DeserializationError(
                "Expected char but got empty string",
            ),
        )
        "#);

        assert_debug_snapshot!(from_tokens::<char>(vec![a("abc")]), @r#"
        Err(
            DeserializationError(
                "Expected single char but got multi-char string",
            ),
        )
        "#);
    }

    #[test]
    fn test_strings() {
        assert_eq!("abc", from_tokens::<&str>(vec![a("abc")]).unwrap());
        assert_eq!("123", from_tokens::<String>(vec![a("123")]).unwrap());
    }

    #[test]
    fn test_option() {
        assert_eq!(None, from_tokens::<Option<i32>>(vec![LP, RP]).unwrap());
        assert_eq!(
            Some(3),
            from_tokens::<Option<i32>>(vec![LP, a("3"), RP]).unwrap()
        );

        assert_debug_snapshot!(from_tokens::<Option<i32>>(vec![a("1")]), @r#"
        Err(
            DeserializationError(
                "expected list",
            ),
        )
        "#);

        assert_debug_snapshot!(from_tokens::<Option<i32>>(vec![LP, a("1"), a("2"), RP]), @r#"
        Err(
            DeserializationError(
                "expected end of list",
            ),
        )
        "#);
    }

    #[allow(clippy::unit_cmp)]
    #[test]
    fn test_unit() {
        assert_eq!((), from_tokens::<()>(vec![LP, RP]).unwrap());

        assert_debug_snapshot!(from_tokens::<()>(vec![a("unit")]), @r#"
        Err(
            DeserializationError(
                "expected list",
            ),
        )
        "#);

        assert_debug_snapshot!(from_tokens::<()>(vec![LP, a("unit"), RP]), @r#"
        Err(
            DeserializationError(
                "expected end of list",
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
            from_tokens::<UnitStruct>(vec![a("UnitStruct")]).unwrap()
        );

        assert_debug_snapshot!(from_tokens::<UnitStruct>(vec![a("unit_struct")]), @r#"
        Err(
            DeserializationError(
                "Expected atom: \"UnitStruct\", got: \"unit_struct\"",
            ),
        )
        "#);

        assert_debug_snapshot!(from_tokens::<UnitStruct>(vec![LP, RP]), @r#"
        Err(
            DeserializationError(
                "expected atom; got list",
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
            from_tokens::<NewtypeStruct>(vec![a("1")]).unwrap()
        );

        assert_debug_snapshot!(from_tokens::<NewtypeStruct>(vec![LP, a("NewtypeStruct"), a("1"), RP]), @r#"
        Err(
            DeserializationError(
                "expected atom; got list",
            ),
        )
        "#);
    }
}
