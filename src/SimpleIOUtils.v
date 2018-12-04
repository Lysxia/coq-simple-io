From Coq.extraction Require
     Extraction.

From SimpleIO Require Import
     IOMonad.

(** * Catch common exceptions *)

Parameter catch_eof : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_eof =>
  "(fun io k ->
     try io (fun a -> k (Some a)) with
     | End_of_file -> k None)".

Parameter catch_invalid_arg : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_invalid_arg =>
  "(fun io k ->
     try io (fun a -> k (Some a)) with
     | Invalid_argument _ -> k None)".

Parameter catch_failure : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_failure =>
  "(fun io k ->
     try io (fun a -> k (Some a)) with
     | Failure _ -> k None)".

Parameter catch_not_found : forall {a : Type}, IO a -> IO (option a).
Extract Constant catch_not_found =>
  "(fun io k ->
     try io (fun a -> k (Some a)) with
     | Not_found -> k None)".
