From Stdlib Require Import
     ExtrOcamlIntConv
     String.
From ExtLib Require Import
     Monad.
From SimpleIO Require Import
     IO_Random
     SimpleIO.
Import
  MonadNotation.
Open Scope monad_scope.
Open Scope string_scope.

Definition coin : IO unit :=
  b <- ORandom.bool tt;;
  print_endline (if b : bool then "head" else "tail").

RunIO (ORandom.init (int_of_nat 42);; coin;; coin;; coin).
