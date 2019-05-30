From Coq.Strings Require Import
     Ascii String.

From Coq.extraction Require Import
     ExtrOcamlIntConv.

From SimpleIO Require Import SimpleIO IO_UnsafeNat.
Import IO.Notations.

Local Open Scope string_scope.

Parameter int_constant : int.
Extract Constant int_constant => "3".

Class Eq (a : Type) :=
  eqb : a -> a -> bool.

Class Print (a : Type) :=
  print : a -> IO unit.

Instance Eq_nat : Eq nat := Nat.eqb.
Instance Print_nat : Print nat := print_nat.

Instance Eq_string : Eq string := String.eqb.
Instance Print_string : Print string := print_string.

Definition assert_eq {a} `{Eq a} `{Print a} (expect actual : a) : IO unit :=
  if eqb expect actual then
    IO.ret tt
  else
    (print_string "Expected: ";; print expect;; print_newline;;
     print_string "Actual  : ";; print actual;; print_newline;;
     exit_nat 1).

Definition main : IO unit :=
  print_char (char_of_ascii "a");; print_newline;;
  print_int int_constant;; print_newline;;
  print_string "Hello";;
  print_endline " world!";;
  h <- open_out "/tmp/test_file.txt";;
  output_byte_nat h 65;;
  close_out h;;
  h <- open_in "/tmp/test_file.txt";;
  n <- input_byte_nat h;;
  close_in h;;
  assert_eq 65 n;;
  r <- new_ref 13;;
  incr_ref_nat r;;
  i <- read_ref r;;
  assert_eq 14 i;;
  write_ref r 1;;
  decr_ref_nat r;;
  j <- read_ref r;;
  assert_eq 0 j;;
  exit_nat 0.

Definition run_main : io_unit := IO.unsafe_run main.

(* We extract the whole library to typecheck it. *)
Separate Extraction
  SimpleIO.SimpleIO
  run_main.
