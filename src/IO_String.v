From Coq Require Import
     Strings.String
     Strings.Ascii
     extraction.ExtrOcamlIntConv.

From SimpleIO Require Import
     IO_Pervasives.

Extraction Blacklist Bytes Pervasives String .

Module OString.

Parameter length : ocaml_string -> int.
Extract Inlined Constant length => "String.length".

(* Equals [None] if out of bounds. *)
Parameter get_opt : ocaml_string -> int -> option char.
Extract Constant get_opt =>
  "fun s i -> try Some (String.get s i)
              with Invalid_argument _ -> None".

(* Concatenates strings with a separator. *)
Parameter concat : ocaml_string -> list ocaml_string -> ocaml_string.
Extract Inlined Constant concat => "String.concat".

Module Unsafe.

(* Throws an exception if out of bounds. *)
Parameter get : ocaml_string -> int -> char.
Extract Inlined Constant get => "String.get".

(* Throws an exception if [n < 0] or [n > Sys.max_string_length]. *)
Parameter make : int -> char -> ocaml_string.
Extract Inlined Constant make => "String.make".

(* Throws an exception if [n < 0] or [n > Sys.max_string_length]. *)
Parameter init : int -> (int -> char) -> ocaml_string.
Extract Inlined Constant init => "String.init".

(* [sub i len s] is the substring of [s] with length [len]
   starting at index [i].
   Throws an exception if out of bounds. *)
Parameter sub : ocaml_string -> int -> int -> ocaml_string.
Extract Inlined Constant sub => "String.sub".

End Unsafe.

End OString.
