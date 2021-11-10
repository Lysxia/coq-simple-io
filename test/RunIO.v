From Coq Require Import
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

RunIOPackage "cppo".
RunIOPackage "zarith".

RunIO (ORandom.self_init tt;; coin;; coin;; coin).
