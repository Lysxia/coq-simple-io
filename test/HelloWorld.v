From SimpleIO Require Import SimpleIO.
From Stdlib Require Import String.
#[local] Open Scope string_scope.

Definition main : IO unit :=
  print_endline "Hello, world!".

RunIO main.
