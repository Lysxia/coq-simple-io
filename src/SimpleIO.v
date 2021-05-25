(** * Main module *)

(** This reexports the most common modules for doing IO in Coq. *)

From SimpleIO Require Export
     IO_Monad
     IO_Stdlib
     IO_StdlibAxioms
     IO_Stdlib
     IO_Exceptions
     IO_RawChar
     IO_String.

Declare ML Module "coqsimpleio_plugin".
