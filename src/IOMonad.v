(**
  The [IO] monad.
*)

Require Extraction.
Require Export ExtrOcamlBasic.

Extraction Blacklist SimpleIO.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

(** * Main interface *)

Parameter IO : Type -> Type.

(** ** Functions *)

Parameter ret : forall {a}, a -> IO a.
Parameter bind : forall {a b}, IO a -> (a -> IO b) -> IO b.
(* Fixpoint combinator. *)
Parameter fix_io : forall {a b}, ((a -> IO b) -> (a -> IO b)) -> a -> IO b.
(* Delay eager evaluation. *)
Parameter delay_io : forall {a}, (unit -> IO a) -> IO a.

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

Notation delay io := (delay_io (fun _ => io)).

Open Scope io_scope.

End IONotations.

(** ** Equations *)

Axiom fix_io_equation : forall {a b} f, @fix_io a b f = f (fix_io f).

(** *** Monad laws *)

Axiom bind_ret :
  forall {a b} (x : a) (k : a -> IO b), bind (ret x) k = k x.
Axiom ret_bind : forall {a} (m : IO a), bind m ret = m.
Axiom bind_bind :
  forall {a b c} (m : IO a) (k : a -> IO b) (h : b -> IO c),
    bind (bind m k) h = bind m (fun x => bind (k x) h).
Axiom bind_ext : forall {a b} (m : IO a) (k k' : a -> IO b),
    (forall x, k x = k' x) -> bind m k = bind m k'.

(** ** Run! *)

Parameter io_unit : Type.
Parameter unsafe_run : IO unit -> io_unit.
Parameter unsafe_run' : forall {a}, IO a -> io_unit.

Parameter very_unsafe_eval : forall {a}, IO a -> a.

(** * Extraction *)

(* CPS prevents stack overflows. *)
Extract Constant IO "'a" => "('a -> unit) -> unit".
Extract Constant ret => "fun a k -> k a".
Extract Constant bind => "fun io_a io_b k -> io_a (fun a -> io_b a k)".
Extract Constant fix_io => "fun f -> let rec go k = f go k in go".
Extract Constant delay_io => "fun f k -> f () k".

Extract Inlined Constant io_unit => "unit".
Extract Constant unsafe_run => "fun io -> io (fun _ -> ())".
Extract Constant unsafe_run' => "fun io -> io (fun _ -> ())".
Extract Constant very_unsafe_eval => "fun io ->
  let r = ref None in
  io (fun a -> r := Some a);
  match !r with
  | None -> failwith ""SimpleIO: action did not return properly""
  | Some a -> a
  end".
