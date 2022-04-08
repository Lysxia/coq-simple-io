From Coq Require Import Uint63 Extraction String ExtrOCamlInt63.

From SimpleIO Require Import SimpleIO.

Definition print_comparison (c : comparison) : IO unit :=
  match c with
  | Lt => print_endline "Lt"%string
  | Gt => print_endline "Gt"%string
  | Eq => print_endline "Eq"%string
  end.

Definition main : IO unit :=
  print_comparison (Uint63.compare 0 1).

RunIO main.
