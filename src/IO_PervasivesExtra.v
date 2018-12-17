(* Wrappers to easily use IO with common Coq types. *)

From Coq.Strings Require Import
     String Ascii.

From Coq.extraction Require Import
     Extraction
     ExtrOcamlBasic
     ExtrOcamlIntConv.

From SimpleIO Require Import
     IO_Monad
     IO_Pervasives
     IO_String.

Import IO.Notations.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

(** * Functions using [nat] instead of [int] *)

(** Highly inefficient! *)

Definition print_nat : nat -> IO unit :=
  fun n => print_int (int_of_nat n).

Definition prerr_nat : nat -> IO unit :=
  fun n => prerr_int (int_of_nat n).

Definition read_nat : IO nat :=
  IO.map nat_of_int read_int.

Definition read_nat_opt : IO (option nat) :=
  IO.map (option_map nat_of_int) read_int_opt.

Definition output_nat : out_channel -> nat -> IO unit :=
  fun h n => output_string' h (ostring_of_int (int_of_nat n)).

Definition output_byte_nat : out_channel -> nat -> IO unit :=
  fun h n => output_byte h (int_of_nat n).

Definition input_byte_nat : in_channel -> IO nat :=
  fun h => IO.map nat_of_int (input_byte h).

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
