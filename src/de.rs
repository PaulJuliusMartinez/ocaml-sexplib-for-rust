use std::io;
use std::num::{ParseFloatError, ParseIntError};

use serde::de::{
    self, DeserializeSeed, EnumAccess, IntoDeserializer, MapAccess, SeqAccess, VariantAccess,
    Visitor,
};
use serde::Deserialize;

use crate::error::{Error, Result};
use crate::tokenizer::Token;

pub struct Deserializer<'de> {
    // Someday: This should be a peekable?
    tokens: Vec<Token<'de>>,
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

impl<'de> Deserializer<'de> {
    fn new(mut tokens: Vec<Token<'de>>) -> Deserializer<'de> {
        tokens.reverse();
        Deserializer { tokens }
    }

    fn next(&mut self) -> Result<Option<Token<'de>>> {
        Ok(self.tokens.pop())
    }

    fn peek(&mut self) -> Result<Option<&Token<'de>>> {
        Ok(self.tokens.last())
    }

    fn advance(&mut self) {
        self.tokens.pop();
    }

    fn expect_atom(&mut self) -> Result<&'de [u8]> {
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

fn from_tokens<'de, T>(tokens: Vec<Token<'de>>) -> Result<T>
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
            match std::str::from_utf8(atom) {
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
            match std::str::from_utf8(atom) {
                Err(_) => error("expected float literal; got invalid UTF-8"),
                Ok(s) => {
                    let i = s.parse::<$float_t>().map_err(parse_float_error)?;
                    visitor.$visit_float(i)
                }
            }
        }
    };
}

impl<'de: 'a, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = Error;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.peek()? {
            None => error("reached end of input"),
            Some(Token::RightParen) => error("unexpected end of list"),
            Some(Token::LeftParen) => self.deserialize_seq(visitor),
            Some(Token::Atom(_)) => self.deserialize_str(visitor),
        }
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let b = match self.expect_atom()? {
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
        let mut chars = match std::str::from_utf8(atom) {
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
        match std::str::from_utf8(atom) {
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
            None => error("reached end of input"),
            Some(Token::RightParen) => {
                self.advance();
                visitor.visit_none()
            }
            Some(Token::LeftParen | Token::Atom(_)) => {
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
        match std::str::from_utf8(atom) {
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

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.expect_start_of_list()?;
        visitor.visit_seq(self)
    }

    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let result = self.deserialize_seq(visitor)?;
        self.expect_end_of_list()?;
        Ok(result)
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
        self.expect_start_of_list()?;
        let result = visitor.visit_map(&mut *self);
        if result.is_ok() {
            self.expect_end_of_list()?
        }
        result
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
        match self.peek()? {
            None => error("reached end of input"),
            Some(Token::RightParen) => error("expected variant; got end of list"),
            Some(Token::Atom(atom)) => {
                match std::str::from_utf8(atom) {
                    Ok(s) => {
                        // `IntoDeserializer` is implemented for `&str` and returns a
                        // `StrDeserializer`, which implements a special `EnumAccess`
                        // that only knows how to handle unit variants.
                        let sref: &str = s;
                        let result = visitor.visit_enum(sref.into_deserializer());
                        self.advance();
                        result
                    }
                    Err(_) => error("atom was not valid UTF-8"),
                }
            }
            Some(Token::LeftParen) => {
                self.advance();
                let result = visitor.visit_enum(&mut *self);
                if result.is_ok() {
                    self.expect_end_of_list()?;
                }
                result
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

impl<'de> SeqAccess<'de> for Deserializer<'de> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>>
    where
        T: DeserializeSeed<'de>,
    {
        match self.peek()? {
            None => error("reached end of input"),
            Some(Token::RightParen) => {
                self.advance();
                Ok(None)
            }
            Some(Token::LeftParen | Token::Atom(_)) => {
                let value = seed.deserialize(&mut *self)?;
                Ok(Some(value))
            }
        }
    }
}

impl<'de> MapAccess<'de> for Deserializer<'de> {
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: DeserializeSeed<'de>,
    {
        match self.peek()? {
            None => error("reached end of input"),
            Some(Token::Atom(_)) => error("expect key-value pair, but got atom"),
            Some(Token::RightParen) => Ok(None),
            Some(Token::LeftParen) => {
                self.advance();
                let value = seed.deserialize(&mut *self)?;
                Ok(Some(value))
            }
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: DeserializeSeed<'de>,
    {
        let result = seed.deserialize(&mut *self);
        if result.is_ok() {
            self.expect_end_of_list()?;
        }
        result
    }
}

impl<'de: 'a, 'a> EnumAccess<'de> for &'a mut Deserializer<'de> {
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: DeserializeSeed<'de>,
    {
        let val = seed.deserialize(&mut *self)?;
        Ok((val, self))
    }
}

impl<'de: 'a, 'a> VariantAccess<'de> for &'a mut Deserializer<'de> {
    type Error = Error;

    fn unit_variant(self) -> Result<()> {
        error("`Deserializer::unit_variant` should not be called")
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value>
    where
        T: DeserializeSeed<'de>,
    {
        seed.deserialize(self)
    }

    fn tuple_variant<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_seq(self)
    }

    fn struct_variant<V>(self, _fields: &'static [&'static str], visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_map(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::borrow::Cow;

    use insta::assert_debug_snapshot;

    fn a(s: &str) -> Token {
        Token::Atom(s.as_bytes())
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
        assert_eq!("123", from_tokens::<String>(vec![a("123")]).unwrap());
        assert_eq!("abc", from_tokens::<Cow<str>>(vec![a("abc")]).unwrap());
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

    #[test]
    fn test_seq() {
        assert_eq!(
            vec![true, false],
            from_tokens::<Vec<bool>>(vec![LP, a("true"), a("false"), RP]).unwrap()
        );

        assert_eq!(
            vec![1u8, 2u8],
            from_tokens::<Vec<u8>>(vec![LP, a("1"), a("2"), RP]).unwrap()
        );

        assert_eq!(
            vec![(), (), ()],
            from_tokens::<Vec<()>>(vec![LP, LP, RP, LP, RP, LP, RP, RP]).unwrap()
        );
    }

    #[test]
    fn test_tuple_and_tuple_struct() {
        #[derive(Debug, Deserialize, PartialEq, Eq)]
        struct TupleStruct<'a>(i8, (bool, i8), Cow<'a, str>);

        fn sexp() -> Vec<Token<'static>> {
            vec![LP, a("1"), LP, a("true"), a("2"), RP, a("abc"), RP]
        }

        assert_eq!(
            (1, (true, 2), Cow::Borrowed("abc")),
            from_tokens::<(i8, (bool, i8), Cow<str>)>(sexp()).unwrap(),
        );
        assert_eq!(
            TupleStruct(1, (true, 2), Cow::Borrowed("abc")),
            from_tokens::<TupleStruct>(sexp()).unwrap(),
        );

        assert_debug_snapshot!(from_tokens::<(i8, bool, String)>(vec![LP, a("0"), a("false"), RP]), @r#"
        Err(
            DeserializationError(
                "invalid length 2, expected a tuple of size 3",
            ),
        )
        "#);

        assert_debug_snapshot!(from_tokens::<TupleStruct>(vec![LP, a("0"), a("false"), RP]), @r#"
        Err(
            DeserializationError(
                "expected list",
            ),
        )
        "#);
    }

    #[test]
    fn test_map() {
        use std::collections::BTreeMap;

        let test = vec![
            LP,
            LP,
            LP,
            a("1"),
            a("foo"),
            RP,
            LP,
            a("2"),
            a("two"),
            RP,
            RP,
            a("true"),
            RP,
        ];

        assert_debug_snapshot!(from_tokens::<(BTreeMap<i32, String>, bool)>(test).unwrap(), @r#"
        (
            {
                1: "foo",
                2: "two",
            },
            true,
        )
        "#);

        fn f(tokens: Vec<Token>) -> Result<BTreeMap<i32, i32>> {
            from_tokens::<BTreeMap<i32, i32>>(tokens)
        }

        assert_debug_snapshot!(f(vec![LP, RP]).unwrap(), @r#"{}"#);

        let atom_kvp = vec![LP, a("1"), RP];
        assert_debug_snapshot!(f(atom_kvp).unwrap_err(), @r#"
        DeserializationError(
            "expect key-value pair, but got atom",
        )
        "#);

        let unit_kvp = vec![LP, LP, RP, RP];
        assert_debug_snapshot!(f(unit_kvp).unwrap_err(), @r#"
        DeserializationError(
            "expected atom; got end of list",
        )
        "#);

        let one_element_kvp = vec![LP, LP, a("1"), RP, RP];
        assert_debug_snapshot!(f(one_element_kvp).unwrap_err(), @r#"
        DeserializationError(
            "expected atom; got end of list",
        )
        "#);

        let three_element_kvp = vec![LP, LP, a("1"), a("2"), a("3"), RP, RP];
        assert_debug_snapshot!(f(three_element_kvp).unwrap_err(), @r#"
        DeserializationError(
            "expected end of list",
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

        let tokens = vec![
            LP,
            a("start"),
            LP,
            LP,
            a("x"),
            a("1"),
            RP,
            LP,
            a("y"),
            a("true"),
            RP,
            RP,
            a("end"),
            RP,
        ];

        assert_eq!(
            (
                "start".to_owned(),
                Struct { x: 1, y: true },
                "end".to_owned()
            ),
            from_tokens::<(String, Struct, String)>(tokens).unwrap(),
        );

        let atom_kvp = vec![LP, a("key: value"), RP];
        let unit_kvp = vec![LP, LP, RP, RP];
        let one_element_kvp = vec![LP, LP, a("x"), RP, RP];
        let unknown_one_element_kvp = vec![LP, LP, a("z"), RP, RP];
        let three_element_kvp = vec![LP, LP, a("x"), a("1"), a("true"), RP, RP];

        assert_debug_snapshot!(from_tokens::<Struct>(atom_kvp), @r#"
        Err(
            DeserializationError(
                "expect key-value pair, but got atom",
            ),
        )
        "#);

        assert_debug_snapshot!(from_tokens::<Struct>(unit_kvp), @r#"
        Err(
            DeserializationError(
                "expected atom; got end of list",
            ),
        )
        "#);

        assert_debug_snapshot!(from_tokens::<Struct>(one_element_kvp), @r#"
        Err(
            DeserializationError(
                "expected atom; got end of list",
            ),
        )
        "#);

        assert_debug_snapshot!(from_tokens::<Struct>(unknown_one_element_kvp), @r#"
        Err(
            DeserializationError(
                "unexpected end of list",
            ),
        )
        "#);

        assert_debug_snapshot!(from_tokens::<Struct>(three_element_kvp), @r#"
        Err(
            DeserializationError(
                "expected end of list",
            ),
        )
        "#);

        // Mostly testing serde's internals here.

        // Missing keys
        assert_debug_snapshot!(from_tokens::<Struct>(vec![LP, RP]), @r#"
        Err(
            DeserializationError(
                "missing field `x`",
            ),
        )
        "#);

        // Duplicate key
        assert_debug_snapshot!(from_tokens::<Struct>(vec![LP, LP, a("x"), a("1"), RP, LP, a("x"), a("2"), RP, RP]), @r#"
        Err(
            DeserializationError(
                "duplicate field `x`",
            ),
        )
        "#);

        // Extra_key is ignored
        let tokens = vec![
            LP,
            LP,
            a("x"),
            a("1"),
            RP,
            LP,
            a("y"),
            a("true"),
            RP,
            LP,
            a("z"),
            a("0"),
            RP,
            RP,
        ];
        assert_debug_snapshot!(from_tokens::<Struct>(tokens), @r"
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

        let unit_sexp = vec![LP, a("start"), a("Unit"), a("end"), RP];

        assert_eq!(
            ("start".to_owned(), Variant::Unit, "end".to_owned()),
            from_tokens::<(String, Variant, String)>(unit_sexp).unwrap(),
        );

        assert_debug_snapshot!(from_tokens::<Variant>(vec![a("Newtype")]), @r#"
        Err(
            DeserializationError(
                "invalid type: unit variant, expected newtype variant",
            ),
        )
        "#);

        // Check Newtype

        let newtype_sexp = vec![LP, a("start"), LP, a("Newtype"), a("1"), RP, a("end"), RP];

        assert_eq!(
            ("start".to_owned(), Variant::Newtype(1), "end".to_owned()),
            from_tokens::<(String, Variant, String)>(newtype_sexp).unwrap(),
        );

        assert_debug_snapshot!(from_tokens::<Variant>(vec![LP, a("Newtype"), RP]), @r#"
        Err(
            DeserializationError(
                "expected atom; got end of list",
            ),
        )
        "#);

        assert_debug_snapshot!(from_tokens::<Variant>(vec![LP, a("Newtype"), a("1"), a("2"), RP]), @r#"
        Err(
            DeserializationError(
                "expected end of list",
            ),
        )
        "#);

        // Check Tuple

        let tuple_tokens = vec![
            LP,
            a("start"),
            LP,
            a("Tuple"),
            a("1"),
            a("2"),
            RP,
            a("end"),
            RP,
        ];

        assert_eq!(
            ("start".to_owned(), Variant::Tuple(1, 2), "end".to_owned()),
            from_tokens::<(String, Variant, String)>(tuple_tokens).unwrap(),
        );

        assert_debug_snapshot!(from_tokens::<Variant>(vec![LP, a("Tuple"), a("1"), RP]), @r#"
        Err(
            DeserializationError(
                "invalid length 1, expected tuple variant Variant::Tuple with 2 elements",
            ),
        )
        "#);

        // Check Struct

        let struct_sexp = vec![
            LP,
            a("start"),
            LP,
            a("Struct"),
            LP,
            a("x"),
            a("1"),
            RP,
            RP,
            a("end"),
            RP,
        ];

        assert_eq!(
            (
                "start".to_owned(),
                Variant::Struct { x: 1 },
                "end".to_owned()
            ),
            from_tokens::<(String, Variant, String)>(struct_sexp).unwrap(),
        );

        assert_debug_snapshot!(from_tokens::<Variant>(vec![LP, a("Struct"), a("1"), RP]), @r#"
        Err(
            DeserializationError(
                "expect key-value pair, but got atom",
            ),
        )
        "#);

        assert_debug_snapshot!(from_tokens::<Variant>(vec![LP, a("Struct"), LP, a("x"), a("1"), a("bad"), RP, RP]), @r#"
        Err(
            DeserializationError(
                "expected end of list",
            ),
        )
        "#);
    }
}
