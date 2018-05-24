(**
  This module assumes Coq strings are extracted using [ExtrOcamlString]:
  - [ascii] is extracted to [char];
  - [string] is extracted to [char list].

  Convenience wrappers around [OcamlPervasives] using [string], [ascii], [nat].
*)

Require Import Strings.String.
Require Import Strings.Ascii.

Require Extraction.
Require Export ExtrOcamlBasic.
Require Export ExtrOcamlIntConv.

Require Export CoqSimpleIO.IOMonad.
Require Export CoqSimpleIO.OcamlString.
Require Export CoqSimpleIO.OcamlPervasives.

Import IONotations.
Open Scope io_scope.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

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
  map_io from_ostring read_line'.

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
  fun h => map_io ascii_of_char (input_char h).

Definition input_line : in_channel -> IO string :=
  fun h => map_io from_ostring (input_line' h).

(** * Functions using [nat] instead of [int] *)

(** Highly inefficient! *)

Definition print_nat : nat -> IO unit :=
  fun n => print_int (int_of_nat n).

Definition prerr_nat : nat -> IO unit :=
  fun n => prerr_int (int_of_nat n).

Definition read_nat : IO nat :=
  map_io nat_of_int read_int.

Definition read_nat_opt : IO (option nat) :=
  map_io (option_map nat_of_int) read_int_opt.

Definition output_nat : out_channel -> nat -> IO unit :=
  fun h n => output_string' h (ostring_of_int (int_of_nat n)).

Definition output_byte_nat : out_channel -> nat -> IO unit :=
  fun h n => output_byte h (int_of_nat n).

Definition input_byte_nat : in_channel -> IO nat :=
  fun h => map_io nat_of_int (input_byte h).

Definition incr_ref_nat : ref nat -> IO unit :=
  fun r =>
    n <- read_ref r;;
    write_ref r (Nat.succ n).

(** N.B.: 0 decreases to 0. *)
Definition decr_ref_nat : ref nat -> IO unit :=
  fun r =>
    n <- read_ref r;;
    write_ref r (Nat.pred n).

Definition exit_nat {a} : nat -> IO a :=
  fun n => exit (int_of_nat n).
