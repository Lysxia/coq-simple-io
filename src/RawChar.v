(**
   [RawChar] reexports [SimpleIO] plus some additional features
   assuming Coq strings are extracted using [ExtrOcamlString]:

   - [ascii] is extracted to [char];
   - [string] is extracted to [char list].

   Though convenient, this is kept separate from [SimpleIO] because
   this uses additional extraction hacks.
 *)

From SimpleIO Require Export SimpleIO.


Require Import Strings.String.
Require Import Strings.Ascii.

Require Extraction.
Require Import ExtrOcamlString.
Require Import ExtrOcamlIntConv.

Require Import SimpleIO.OcamlPervasives.

Extraction Blacklist Bytes Pervasives String .

(** * Conversions *)

Parameter int_of_ascii : ascii -> int.
Parameter ascii_of_int : int -> ascii.

Axiom char_is_ascii : char = ascii.

Definition char_of_ascii : ascii -> char :=
  match char_is_ascii in (_ = _ascii) return (_ascii -> char) with
  | eq_refl => fun c => c
  end.

Definition ascii_of_char : char -> ascii :=
  match char_is_ascii in (_ = _ascii) return (char -> _ascii) with
  | eq_refl => fun x => x
  end.

Extract Inlined Constant int_of_ascii => "Pervasives.int_of_char".
Extract Inlined Constant ascii_of_int => "Pervasives.char_of_int".

Parameter to_ostring : string -> ocaml_string.
Parameter from_ostring : ocaml_string -> string.

Extract Constant to_ostring =>
  "fun z -> Bytes.unsafe_to_string (
    let b = Bytes.create (List.length z) in
    let rec go z i =
      match z with
      | c :: z -> Bytes.set b i c; go z (i+1)
      | [] -> b
    in go z 0)".

Extract Constant from_ostring =>
  "fun s ->
    let rec go n z =
      if n = -1 then z
      else go (n-1) (String.get s n :: z)
    in go (String.length s - 1) []".

(** ** Standard channels *)

(** *** [stdin] *)

Definition print_ascii : ascii -> IO unit :=
  fun a => print_char (char_of_ascii a).

Definition print_string : string -> IO unit :=
  fun s => print_string' (to_ostring s).

Definition print_endline : string -> IO unit :=
  fun s => print_endline' (to_ostring s).

(** *** [stderr] *)

Definition prerr_ascii : ascii -> IO unit :=
  fun a => prerr_char (char_of_ascii a).

Definition prerr_string : string -> IO unit :=
  fun s => prerr_string' (to_ostring s).

Definition prerr_endline : string -> IO unit :=
  fun s => prerr_endline' (to_ostring s).

(** *** [stdin] *)

Definition read_line : IO string :=
  IO.map from_ostring read_line'.

(** ** File handles *)

(** *** Output *)

Definition open_out : string -> IO out_channel :=
  fun s => open_out' (to_ostring s).

Definition output_ascii : out_channel -> ascii -> IO unit :=
  fun h a => output_char h (char_of_ascii a).

Definition output_string : out_channel -> string -> IO unit :=
  fun h s => output_string' h (to_ostring s).

(** *** Input *)

Definition open_in : string -> IO in_channel :=
  fun s => open_in' (to_ostring s).

Definition input_ascii : in_channel -> IO ascii :=
  fun h => IO.map ascii_of_char (input_char h).

Definition input_line : in_channel -> IO string :=
  fun h => IO.map from_ostring (input_line' h).
