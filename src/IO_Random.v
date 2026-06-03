(** * Pseudo-random number generators (PRNG) *)

(** Note: descriptions of the interface are derived from OCaml's documentation:
    https://caml.inria.fr/pub/docs/manual-ocaml/libref/Random.html *)

(* begin hide *)
From Stdlib Require Import
     ExtrOcamlIntConv.
From SimpleIO Require Import
     IO_Monad
     IO_Stdlib.
(* end hide *)

Module ORandom.

(** Initialize using a given seed. The same seed will always yield the same
    sequence of numbers. *)
Parameter init : int -> IO unit.

(** Initialize the generator with a random seed chosen in a system-dependent
    way.  If [/dev/urandom] is available on the host machine, it is used to
    provide a highly random initial seed.  Otherwise, a less random seed is
    computed from system parameters (current time, process IDs). *)
Parameter self_init : unit -> IO unit.

(** [IO_Random.int bound] returns a random integer between 0 (inclusive) and
    [bound] (exclusive). [bound] must be greater than 0 and less than 2{^30}. *)
Parameter int : int -> IO int.

(** [IO_Random.bool tt] returns [true] or [false] with probability 0.5 each. *)
Parameter bool : unit -> IO bool.

(* begin hide *)
Extract Constant init => "fun n k -> k (Random.init n)".
Extract Constant self_init => "fun t k -> k (Random.self_init t)".
Extract Constant int       => "fun i k -> k (Random.int i)".
Extract Constant bool         => "fun t k -> k (Random.bool t)".
(* end hide *)

End ORandom.
