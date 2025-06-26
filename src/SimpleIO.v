(** * Main module *)

(** This reexports the most common modules for doing IO in Rocq. *)

From SimpleIO Require Export
     SimpleIO_Plugin
     IO_Monad
     IO_Stdlib
     IO_StdlibAxioms
     IO_Stdlib
     IO_Exceptions
     IO_RawChar
     IO_String.
