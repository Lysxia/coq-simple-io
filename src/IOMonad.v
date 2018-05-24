(**
  The [IO] monad.
*)

Require Extraction.
Require Export ExtrOcamlBasic.

Extraction Blacklist CoqSimpleIO.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

(** * Main interface *)

Parameter IO : Type -> Type.

(** ** Functions *)

Parameter ret : forall {a}, a -> IO a.
Parameter bind : forall {a b}, IO a -> (a -> IO b) -> IO b.
Parameter fix_io : forall {a b}, ((a -> IO b) -> (a -> IO b)) -> a -> IO b.

Definition map_io {a b} : (a -> b) -> IO a -> IO b :=
  fun f m => bind m (fun a => ret (f a)).

Definition loop : forall {a void}, (a -> IO a) -> (a -> IO void) :=
  fun _ _ f => fix_io (fun k x => bind (f x) k).

Definition while_loop : forall {a}, (a -> IO (option a)) -> (a -> IO unit) :=
  fun _ f => fix_io (fun k x => bind (f x) (fun y' =>
    match y' with
    | None => ret tt
    | Some y => k y
    end)).

(** ** Notations *)

Module IONotations.

Delimit Scope io_scope with io.

Notation "c >>= f" := (bind c f)
(at level 50, left associativity) : io_scope.

Notation "f =<< c" := (bind c f)
(at level 51, right associativity) : io_scope.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
(at level 100, c1 at next level, right associativity) : io_scope.

Notation "e1 ;; e2" := (_ <- e1%io ;; e2%io)%io
(at level 100, right associativity) : io_scope.

End IONotations.

(** ** Run IO! *)

Parameter unsafe_run : forall {a}, IO a -> unit.

(** * Extraction *)

Extract Constant IO "'a" => "'a CoqSimpleIO.t".
Extract Inlined Constant ret => "CoqSimpleIO.return".
Extract Inlined Constant bind => "CoqSimpleIO.bind".
Extract Inlined Constant fix_io => "CoqSimpleIO.fix_io".
Extract Inlined Constant unsafe_run => "CoqSimpleIO.Impure.run".
