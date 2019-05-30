From SimpleIO Require Import
  SimpleIO
  IO_Bytes
  IO_Random
  IO_Unix
  IO_Float
  IO_Unsafe
  IO_UnsafeNat.

Definition test :=
  ( IO_Pervasives.print_string,
    @IO_Exceptions.catch_eof,
    IO_RawChar.int_of_ascii,
    IO_String.OString.length,
    IO_Bytes.OBytes.get,
    IO_Random.ORandom.int,
    IO_Unix.OUnix.error,
    IO_Float.OFloat.of_int,
    IO_Unsafe.unsafe_int_div,
    IO_UnsafeNat.print_nat
  ).

Separate Extraction test
  SimpleIO
  IO_Bytes
  IO_Random
  IO_Unix
  IO_Float
  IO_Unsafe
  IO_UnsafeNat.
