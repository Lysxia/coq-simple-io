From SimpleIO Require Import SimpleIO.
From Coq Require Import String.

Definition main : IO unit :=
  print_endline "Hello World!"%string.

RunIO Builder Ocamlbuild.
RunIO main.
