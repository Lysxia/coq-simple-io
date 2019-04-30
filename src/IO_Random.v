(** * Pseudo-random number generators (PRNG) *)

(** Note: description of the interfaces are derived from OCaml's documentation:
    https://github.com/ocaml/ocaml/blob/trunk/stdlib/random.mli *)

(* begin hide *)
From Coq Require Import
     ExtrOcamlIntConv.
From SimpleIO Require Import
     IO_Monad
     IO_Pervasives.
(* end hide *)

Module ORandom.

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
Extract Constant self_init => "fun t k -> k (Random.self_init t)".
Extract Constant int       => "fun i k -> k (Random.int i)".
Extract Constant bool         => "fun t k -> k (Random.bool t)".
(* end hide *)

End ORandom.
