From Coq.Strings Require Import
     Ascii String.
From Coq Require Import List.
Import ListNotations.

From Coq.extraction Require Import
     ExtrOcamlIntConv.

From SimpleIO Require Import SimpleIO IO_UnsafeNat IO_Bytes.
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

Instance Eq_option {a : Type} `{Eq a} : Eq (option a) :=
  fun x y =>
    match x, y with
    | None, None => true
    | Some x, Some y => eqb x y
    | _, _ => false
    end.
Instance Print_option {a : Type} `{Print a} : Print (option a) :=
  fun x =>
    match x with
    | None => print_string "None"
    | Some x => print_string "Some (";; print x;; print_string ")"
    end.

(* Using coercions. [String.eqb] also exists since Coq 8.9 but this
   test needs to be compatible with 8.8. *)
Instance Eq_string : Eq string := ostring_eqb.
Instance Print_string : Print string := print_string.

Instance Eq_ostring : Eq ocaml_string := ostring_eqb.
Instance Print_ostring : Print ocaml_string :=
  fun s => print_string (OString.escaped s).

Instance Eq_char : Eq char := char_eqb.
Instance Print_char : Print char :=
  fun c => print (OString.of_list [c]).

Definition assert_eq {a} `{Eq a} `{Print a} (expect actual : a) : IO unit :=
  if eqb expect actual then
    IO.ret tt
  else
    (print_string "Expected: ";; print expect;; print_newline;;
     print_string "Actual  : ";; print actual;; print_newline;;
     exit_nat 1).

Coercion int_of_nat : nat >-> int.

Definition main : IO unit :=
  (* Pervasives *)

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

  (* String *)

  let s : ocaml_string := "test" in
  assert_eq 4 (nat_of_int (OString.length s));;
  assert_eq (Some ("t"%char : char)) (OString.get_opt s 3);;
  assert_eq None (OString.get_opt s 4);;
  assert_eq ("test,test" : ocaml_string) (OString.concat "," [s;s]);;

  let nl := String "010" "" in
  let s' := OString.escaped (nl ++ nl)%string in
  assert_eq ("\n\n" : ocaml_string) s';;

  (* Bytes *)

  b <- OBytes.of_string "test";;
  s <- OBytes.to_string b;;
  assert_eq "test" (from_ostring s);;

  let n := nat_of_int (OBytes.length b) in
  assert_eq 4 n;;

  OBytes.set b 0 "r"%char;;
  r <- OBytes.get b 0;;
  assert_eq ("r"%char : char) r;;

  b <- OBytes.create (int_of_nat 1);;
  assert_eq 1 (nat_of_int (OBytes.length b));;

  exit_nat 0.

Definition run_main : io_unit := IO.unsafe_run main.

(* We extract the whole library to typecheck it. *)
Separate Extraction
  SimpleIO.SimpleIO
  run_main.
