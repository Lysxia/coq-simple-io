Require Import Strings.String.
Require Import Strings.Ascii.
Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.

(* [ascii] is extracted to [char].
   [string] is extracted to [char list]. *)
Require Import ExtrOcamlString.

(* Types and functions *)

Parameter ocaml_string : Type.

Parameter int_of_char : ascii -> int.
Parameter char_of_int : int -> ascii.

Parameter from_ocaml_string : ocaml_string -> string.
Parameter to_ocaml_string : string -> ocaml_string.

(* Axioms *)

(* The other round-trip is not true because [int]
   is larger than [char]. *)
Axiom char_of_int_of_char : forall c,
  char_of_int (int_of_char c) = c.

Axiom to_from_ocaml_string : forall s,
  from_ocaml_string (to_ocaml_string s) = s.

Axiom from_to_ocaml_string : forall s,
  to_ocaml_string (from_ocaml_string s) = s.

(* Extraction *)

Extract Constant ocaml_string => "string".

Extract Constant int_of_char => "Pervasives.int_of_char".
Extract Constant char_of_int => "Pervasives.char_of_int".

Extract Constant from_ocaml_string =>
  "fun s ->
    let rec go n z =
      if n = -1 then
        z
      else
        go (n-1) (String.get s n :: z)
    in go (String.length s - 1) []".

Extract Constant to_ocaml_string =>
  "fun z -> Bytes.unsafe_to_string (
    let b = Bytes.create (List.length z) in
    let rec go z i =
      match z with
      | c :: z -> Bytes.set b i c; go z (i+1)
      | [] -> b
    in go z 0)".
