(** General purpose utilities. *)

(* begin hide *)
From Coq.extraction Require
     Extraction.

From SimpleIO Require Import
     IO_Monad IO_Pervasives.
(* end hide *)

(** Conversion between [ocaml_string] and [list char]. *)
Parameter list_of_ostring : ocaml_string -> list char.
Parameter ostring_of_list : list char -> ocaml_string.

Axiom to_from_ostring :
  forall s, list_of_ostring (ostring_of_list s) = s.
Axiom from_to_ostring :
  forall s, ostring_of_list (list_of_ostring s) = s.

(** ** Extraction *)

Extract Constant list_of_ostring =>
  "fun s ->
    let rec go n z =
      if n = -1 then z
      else go (n-1) (String.get s n :: z)
    in go (String.length s - 1) []".

Extract Constant ostring_of_list =>
  "fun z -> Bytes.unsafe_to_string (
    let b = Bytes.create (List.length z) in
    let rec go z i =
      match z with
      | c :: z -> Bytes.set b i c; go z (i+1)
      | [] -> b
    in go z 0)".
