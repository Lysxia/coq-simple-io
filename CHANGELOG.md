# 1.3.0

- Fix the extraction of core `IO` constants with type annotations to avoid
  type errors caused by the value restriction.
- Add `IO_Sys`, based on `Sys` from the OCaml stdlib.
- Add `file_descr_eqb` and `select` in `IO_Unix`.
- Fix extraction of `error` and `catch_error` in `IO_Unix`.
- Update `IO.Notations` to agree with *coq-ext-lib* 0.11.1

# 1.2.1

- Blacklisted `List`

# 1.2.0

- Added module `IO_Float`
- Added `OString.escaped`, `OUnix.setsock_timeout`, `OUnix.error`,
  `OUnix.catch_error`, `OUnix.raise_error`
- Fixed extraction of `OBytes.set`
- Changed `IO_Unix.recv` to no longer return the input buffer
- Changed `OBytes.to_string` and `OBytes.from_string` to be `IO` actions
  instead of pure functions

# 1.1.0

- Added `IO_Stdlib`, `IO_Bytes`, `IO_Random`, `IO_Unix`

# 1.0.0

- Big rewrite

- `IO a` is now `('a -> Obj.t) -> Obj.t` (`forall r. (a -> r) -> r`)
- A single main entry point: `SimpleIO.SimpleIO` (plus optional unsafe modules)
- New functions for strings and exceptions

# 0.2

- Removed ocaml library. `IO` is now defined in OCaml by extraction simply as
  `('a -> unit) -> unit`.
- Add `delay_io`

# 0.1

Initial release
