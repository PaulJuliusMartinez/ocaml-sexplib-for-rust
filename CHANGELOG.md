main
===
- Make `atom` and `token_writer` modules public
- Rework `atom` module to expose separate types for atom data vs serialized atom data
- Rename `InputRef` to `Ref` and move it to a top-level crate item
- Remove `RawBytes` and `UnescapedBytes` and move all unescaping logic to `atom` module
- Add function to serialize `AtomData` to a `fmt::Write`
- Add `PlausiblySerializedAtom::normalize_serialization_even_if_invalid`

v0.0.3 (2025-12-13)
===
- Actually escape atoms during serialization

v0.0.2 (2025-11-22)
====
- Rework low-level API to expose `RawTokenTape` trait
- Remove unused `CallNextRawTokenToGetTheRealError`

v0.0.1 (2025-08-18)
===================
- Initial version of crate with support for basic serialization and deserialization
