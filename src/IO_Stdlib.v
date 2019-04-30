(** * The OCaml Standard library *)
(** Note: description of the interfaces are derived from OCaml's documentation:
    https://github.com/ocaml/ocaml/blob/trunk/stdlib/stdlib.mli *)

(* begin hide *)
From SimpleIO Require Import
     IO_Monad
     IO_Pervasives.
(* end hide *)

(** Return the string representation of a boolean. *)
Parameter ostring_of_bool : bool -> ocaml_string.

(* begin hide *)
Extract Constant ostring_of_bool => "Stdlib.string_of_bool".
(* end hide *)
