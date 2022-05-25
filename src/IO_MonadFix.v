(** * [MonadFix IO] instance *)

(** It was causing a universe inconsistency with VST.
    Until we investigate more we keep this instance in its own module. *)

From ExtLib.Structures Require Import MonadFix.
From SimpleIO Require Import IO_Monad.

Global Instance MonadFix_IO : MonadFix IO := {|
  mfix _ _ := IO.fix_io
|}.
