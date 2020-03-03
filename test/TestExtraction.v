From SimpleIO Require Import
  SimpleIO
  IO_Bytes
  IO_Random
  IO_Unix
  IO_Float
  IO_Sys
  IO_Unsafe
  IO_UnsafeNat.

(* Make sure these are not inlined constants so the whole module gets extracted. *)
Definition test :=
  ( IO_Stdlib.print_string,
    @IO_Exceptions.catch_eof,
    IO_RawChar.to_ostring,
    IO_String.OString.get_opt,
    IO_Bytes.OBytes.get,
    IO_Random.ORandom.int,
    IO_Unix.OUnix.sleep,
    IO_Float.OFloat.of_int,
    IO_Sys.OSys.getenv,
    IO_Unsafe.unsafe_int_div, (* This module contains only inlined constants... *)
    IO_UnsafeNat.print_nat
  ).

Separate Extraction test
  SimpleIO
  IO_Bytes
  IO_Random
  IO_Unix
  IO_Float
  IO_Sys
  IO_Unsafe
  IO_UnsafeNat.
