# Purely functional IO for Coq

An IO monad with user-definable primitive operations.

This library provides tools to implement IO programs directly in Coq, in a
similar style to Haskell.

Facilities for formal verification are not included.
There is no canonical way to describe the effects of the arbitrary foreign
constructs that this library allows, so this library commits to none.

## Installation

### From OPAM

```
opam install coq-simple-io
```

### From this repository as a local package

```
opam pin add -k git coq-simple-io path/to/this/repo
```

## Interface

Combinators for IO actions.

```coq
(* Coq module CoqIO.IOMonad, in src/IOMonad.v *)

Parameter IO : Type -> Type.

Parameter ret : forall {a}, a -> IO a.
Parameter bind : forall {a b}, IO a -> (a -> IO b) -> IO b.
Parameter fix_io : forall {a b}, ((a -> IO b) -> (a -> IO b)) -> a -> IO b.
```

## Defining IO actions

The `IO` type extracts to the following definition in OCaml:

```ocaml
type 'a iO = ('a -> unit) -> unit
```

So an effectful function `f : t -> u -> v` in OCaml can be wrapped
as a Coq function `f : t -> u -> IO v` in the following way:

```coq
Parameter f : t -> u -> IO v.
Extract Constant f => "fun a b k -> k (f a b)".
```

Basically, add an extra parameter `k` and apply it to the OCaml function call.

## Related

- [Ynot](https://github.com/ynot-harvard/ynot)
- [Coq.io](http://coq.io)
