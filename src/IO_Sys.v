(** * System interface *)

(** Note: descriptions of the interface are derived from OCaml's documentation:
    https://caml.inria.fr/pub/docs/manual-ocaml/libref/Sys.html *)

(* begin hide *)
From Coq Require Import
     ExtrOcamlIntConv.

From SimpleIO Require Import
     IO_Monad
     IO_Stdlib.
(* end hide *)

Module OSys.

(** Return the value associated to a variable in the process environment.
    Raise [Not_found] if the variable is unbound. *)
Parameter getenv : ocaml_string -> IO ocaml_string.

(** Return the value associated to a variable in the process environment or
    [None] if the variable is unbound. *)
Parameter getenv_opt: ocaml_string -> IO (option ocaml_string).

(** Return the processor time, in seconds, used by the program
    since the beginning of execution. *)
Parameter time : IO float.

(** ** Extraction *)

Extract Constant getenv     => "fun e k -> k (Sys.getenv     e)".
Extract Constant getenv_opt => "fun e k -> k (Sys.getenv_opt e)".
Extract Constant time       => "fun   k -> k (Sys.time      ())".

End OSys.
