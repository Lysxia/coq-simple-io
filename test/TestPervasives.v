Require Import String.

Require Extraction.
Require Import SimpleIO.CoqPervasives.
Import IONotations.

Open Scope io_scope.
Open Scope string_scope.

Parameter int_constant : int.
Extract Constant int_constant => "3".

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
  print_nat n;; print_newline;;
  close_in h;;
  r <- new_ref 13;;
  incr_ref_nat r;;
  i <- read_ref r;;
  print_nat i;; print_newline;;
  write_ref r 1;;
  decr_ref_nat r;;
  j <- read_ref r;;
  print_nat j;; print_newline;;
  exit_nat 0.

Definition run_main : unit := unsafe_run main.

(* We extract the whole library to typecheck it. *)
Separate Extraction
  SimpleIO.IOMonad
  SimpleIO.OcamlString
  SimpleIO.OcamlPervasives
  SimpleIO.CoqPervasives
  run_main.
