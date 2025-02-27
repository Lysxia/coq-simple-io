# 1.11.0

- Add option `RunIO IOMode Forward` to forward stdin and stdout of the extracted executable to
  the coqc process, allowing IO actions to be run as interactive command-line scripts.
- Fix a file system race: when multiple `RunIO` commands ran concurrently in the same folder,
  they used the same local `__qc_tmp` temporary file, clobbering each other.

# 1.10.0

- Compatibility with Coq 8.20

# 1.9.0

- Add `RunIO Reset`
- Rename `RunIO Builder Basic` to `RunIO Builder Ocamlfind`
- Extend `RunIO Builder` commands with an optional string to pass to the build executable.
  Example: `RunIO Builder Ocamlfind "-I mydir"`.
- Add `IO_Random.init`.

# 1.8.0

- Redesign `RunIO` auxiliary commands for configuring extraction.
    + `RunIO Include "dir".` copies `dir` when compiling package.
    + `RunIO Open "M".` prefixes the extracted OCaml file with `open M`.
    + `RunIO Package "pkg".` adds `pkg` when compiling with `ocamlfind opt` or `ocamlbuild`.
    + `RunIO Builder Basic.` (default) compiles using `ocamlfind opt`.
    + `RunIO Builder Ocamlbuild.` compiles using `ocamlbuild`.
    + `RunIO Builder Dune.` compiles using `dune`. This ignores `RunIO Package`;
      dependencies should be specified in the `dune` file.
    + `RunIO Smart (On|Off).` (`On` by default) enable|disable automatic
      detection of common package dependencies (currently `zarith` for `Big_Int_Z`
      and `coq-core.kernel` for `Uint63`).
- Add `IO_Filename`.
- Use `dune` for building.

# 1.7.0

- Fix definitions of `catch_not_found`, `catch_sys_error`
- Add:
    + `IO_Exceptions.catch_any_exc`
    + in `Stdlib`: `input`, `really_input`, `really_input_string`
    + `IO_Sys.OSys.argv`.

# 1.6.0

- Add `RunIO` command to compile and run executables from a Coq file
- Rename `Pervasives` to `Stdlib` in extracted code (for OCaml >= 4.08)
- Add new definitions from the stdlib:

    + `IO_Stdlib.close_out_noerr`
    + `IO_Stdlib.close_in_noerr`
    + `IO_Stdlib.in_channel_length`
    + `IO_Exceptions.catch_sys_error`
    + `IO_Sys.OSys.command`

# 1.5.0

- Add `IO_MonadFix` with the `MonadFix` instance in its own module.
- Add float arithmeti.
- Add `Bytes.sub`, `Unix.getaddrinfo`, `Sys.time` (and related definitions)

# 1.4.0

- Remove instance `MonadFix_IO` (was causing universe inconsistencies)
- Add in `Unix`:

    + `inet_addr_of_string`, `string_of_inet_addr`
    + `socket_bool_option`, `getsockopt`, setsockopt`
    + `error_message`

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
