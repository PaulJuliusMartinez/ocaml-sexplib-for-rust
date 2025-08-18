An implementation of Jane Street's [sexplib](https://github.com/janestreet/sexplib)
S-expression data format, with `serde` support for serialization and deserialization.

Unlike OCaml (de)serialization with [`ppx_sexp_conv`](https://github.com/janestreet/ppx_sexp_conv),
which requires materialization an entire `Sexp.t` in memory, the `serde` implementations
in this crate serialize directly to/from the string representation.

### Todo

- Performance
  - Add benchmarking
  - SIMD tokenization implementation
  - Use [`memchr`](https://github.com/BurntSushi/memchr) where appropriate
  - More efficient number/float (de)serialization
  - Never return `InputRef::Transient` from `RawTokenizer` when using a `SliceInput`
- Correctness
  - Serialization of numbers that contain underscores
  - Add fuzz tests
- API
  - Source input positions during parse errors
  - Add `from_reader`/`many_from_reader`/`iter_from_reader` functions
  - Add `from_{slice,str}_owned` functions that read from in memory data, but don't keep a reference to it.
  - `sexp::Sexp` should store bytes instead of a `str`, and/or there should be separate `sexp::str`
    and `sexp::bytes` modules
  - Support partial unescaping from invalid data, e.g. `echo '"ab\xg"' | sexp print` prints `"ab\\xg"`
- Code/docs
  - Clean up... lots of code and public interfaces?
  - Add doc comments everywhere
  - Add documentation to readme about mapping between Rust/`serde` and OCaml/`ppx_sexp_conv` data
    models and serialization rules
