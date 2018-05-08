Require Extraction.
Require Export ExtrOcamlBasic.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Parameter ocaml_string : Type.

Parameter IO : Type -> Type.

Parameter ret : forall {a}, a -> IO a.
Parameter bind : forall {a b}, IO a -> (a -> IO b) -> IO b.
Parameter loop : forall {a void}, (a -> IO a) -> (a -> IO void).
Parameter while_loop : forall {a}, (a -> IO (option a)) -> (a -> IO unit).

Parameter unsafe_run : forall {a}, IO a -> unit.

(* Add LoadPath "../ocaml-lib/". *)
(* Declare ML Module "coq_io_lib". *)

Extract Constant IO "'a" => "'a Coq_IO.t".
Extract Constant ret => "Coq_IO.return".
Extract Constant bind => "Coq_IO.bind".
Extract Constant loop => "Coq_IO.loop".
Extract Constant while_loop => "Coq_IO.while_loop".
Extract Constant unsafe_run => "Coq_IO.Impure.run".
