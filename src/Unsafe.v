(** Unsafe but convenient primitives.
 *)

Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.

From SimpleIO Require Import OcamlPervasives.

(* Throws an exception if the argument is smaller than 0 or
   greater than 255. *)
Parameter unsafe_char_of_int : int -> char.
Extract Constant unsafe_char_of_int => "Pervasives.char_of_int".

(* Throws an exception if the argument string does not represent
   an integer. *)
Parameter unsafe_int_of_ostring : ocaml_string -> int.
Extract Inlined Constant unsafe_int_of_ostring => "Pervasives.int_of_string".
