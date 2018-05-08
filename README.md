# Purely functional IO for Coq

An IO monad with user-defined primitive operations.

## Gallina interface

Combinators for IO actions.

```coq
(* Coq module CoqIO.Monad, in src/Monad.v *)

Parameter IO : Type -> Type.

Parameter ret : forall {a}, a -> IO a.
Parameter bind : forall {a b}, IO a -> (a -> IO b) -> IO b.
Parameter fix_io : forall {a b}, ((a -> IO b) -> (a -> IO b)) -> a -> IO b.
```

## OCaml interface

Wrap and run IO actions.

```ocaml
(* OCaml module CoqIO, in ocaml-lib/coqIO.mli *)

type +'a t (* IO type *)

module Impure : sig
  val mk_io : (unit -> 'a) -> 'a t
  val run : 'a t -> unit
end
```

## To do

- Tutorial/introduction
