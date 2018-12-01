From Coq.extraction Require
     Extraction.

From SimpleIO Require Import
     IOMonad.

Parameter catch_eof : forall {a : Type}, IO a -> IO (option a).

Extract Constant catch_eof =>
  "(fun io k ->
     try io (fun a -> k (Some a)) with
     | End_of_file -> k None)".
