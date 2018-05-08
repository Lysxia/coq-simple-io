Require Import Strings.String.
Require Import Strings.Ascii.
Require Extraction.
Require Export ExtrOcamlBasic.
Require Export ExtrOcamlIntConv.

Definition char := ascii.
Definition coq_string := Strings.String.string.

Parameter ocaml_string : Type.

Parameter int_of_char : char -> int.
Parameter char_of_int : int -> char.

Parameter string_of_ocaml : ocaml_string -> coq_string.
Parameter ocaml_of_string : coq_string -> ocaml_string.

(* Coq strings as lists. *)
Extract Inductive ascii => "char" [ "CoqIO_String.mk_ascii" ] "CoqIO_String.ascii_rec".
Extract Inductive string => "char list" [ "[]" "(::)" ].

Extract Constant ocaml_string => "string".

Extract Constant int_of_char => "int_of_char".
Extract Constant char_of_int => "char_of_int".

Extract Constant string_of_ocaml => "CoqIO_String.string_of_ocaml".
Extract Constant ocaml_of_string => "CoqIO_String.ocaml_of_string".
