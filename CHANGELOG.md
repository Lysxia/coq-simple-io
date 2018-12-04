# 0.3

- Changed the type of `unsafe_run` to an abstract `io_unit`, to discourage
  using it in the middle of a function.
- Definitions in `IOMonad` are now namespaced inside an `IO` module.
- Added functions:

    + `unsafe_run'` and `very_unsafe_eval` to `IOMonad`.
    + `int_of_string_opt`, `ostring_eqb` and `char_eqb` to `OcamlPervasives`

- New modules:

    - `Lib` reexporting the core functionality with a single import.
    - `Utils` for extra definitions that don't come straight from OCaml.

# 0.2

- Removed ocaml library. `IO` is now defined in OCaml by extraction simply as
  `('a -> unit) -> unit`.
- Add `delay_io`

# 0.1

Initial release
