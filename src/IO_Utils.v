From Coq.extraction Require
     Extraction.

From SimpleIO Require Import
     IO_Monad IO_Pervasives.

(** * Catch common exceptions *)

Parameter catch_eof : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_eof =>
  "(fun io k ->
     k (try Obj.magic io (fun a -> Some a) with
        | End_of_file -> None))".

Parameter catch_invalid_arg : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_invalid_arg =>
  "(fun io k ->
     k (try Obj.magic io (fun a -> Some a) with
        | Invalid_argument _ -> None))".

Parameter catch_failure : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_failure =>
  "(fun io k ->
     k (try Obj.magic io (fun a -> Some a) with
        | Failure _ -> None))".

Parameter catch_not_found : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_not_found =>
  "(fun io k ->
     k (try Obj.magic io (fun a -> Some a) with
        | Not_found -> None)".

(** * Manipulating strings *)

(** ** Conversion functions *)

Parameter list_of_ostring : ocaml_string -> list char.
Parameter ostring_of_list : list char -> ocaml_string.

(** ** Axioms *)

Axiom char_of_int_of_char :
  forall c, char_of_int_opt (int_of_char c) = Some c.

(** The other roundtrip direction "[int_of_char_of_int]" is not true
    because [int] is larger than [char]. *)

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
