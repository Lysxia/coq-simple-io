(**
  This module assumes Coq strings are extracted using [ExtrOcamlString]:
  - [ascii] is extracted to [char];
  - [string] is extracted to [char list].

  Defines mappings between [ocaml_string], [char] (defined in
  [OcamlPervasives]) and Coq's [string], [ascii].
*)

Require Import Strings.String.
Require Import Strings.Ascii.

Require Extraction.
Require Import ExtrOcamlString.
Require Import ExtrOcamlIntConv.

Require Import CoqSimpleIO.OcamlPervasives.

Extraction Blacklist Bytes Pervasives String .

(** * Conversion functions *)

Parameter int_of_ascii : ascii -> int.
Parameter ascii_of_int : int -> ascii.

Parameter from_ostring : ocaml_string -> string.
Parameter to_ostring : string -> ocaml_string.

(** * Axioms *)

Axiom char_is_ascii : char = ascii.

Definition char_of_ascii : ascii -> char :=
  match char_is_ascii in (_ = _ascii) return (_ascii -> char) with
  | eq_refl => fun c => c
  end.

Definition ascii_of_char : char -> ascii :=
  match char_is_ascii in (_ = _ascii) return (char -> _ascii) with
  | eq_refl => fun x => x
  end.

Axiom char_of_int_of_char : forall c, char_of_int (int_of_char c) = c.

(**
  The other roundtrip direction "[int_of_char_of_int]" is not true because
  [int] is larger than [char].
*)

Axiom to_from_ostring : forall s, from_ostring (to_ostring s) = s.

Axiom from_to_ostring : forall s, to_ostring (from_ostring s) = s.

(** * Extraction *)

Extract Inlined Constant int_of_ascii => "Pervasives.int_of_char".
Extract Inlined Constant ascii_of_int => "Pervasives.char_of_int".

Extract Constant from_ostring =>
  "fun s ->
    let rec go n z =
      if n = -1 then
        z
      else
        go (n-1) (String.get s n :: z)
    in go (String.length s - 1) []".

Extract Constant to_ostring =>
  "fun z -> Bytes.unsafe_to_string (
    let b = Bytes.create (List.length z) in
    let rec go z i =
      match z with
      | c :: z -> Bytes.set b i c; go z (i+1)
      | [] -> b
    in go z 0)".
