From SimpleIO Require Import SimpleIO.
From Stdlib Require Import String.

Definition main : IO unit :=
  print_endline "Hello World!"%string.

RunIO Builder Ocamlbuild.
RunIO main.
