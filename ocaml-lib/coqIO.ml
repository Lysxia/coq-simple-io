(* CPS prevents stack overflows. *)
type 'a t = { apply : 'r. ('a -> 'r) -> 'r } [@@unboxed]

module Impure = struct
  let mk_io_1 f x = { apply = fun k -> k (f x) }
  let mk_io_2 f x y = { apply = fun k -> k (f x y) }

  let mk_io_0 f = mk_io_1 f ()

  let run m = m.apply (fun _ -> ())
end

let return a = { apply = fun k -> k a }

let bind m h = { apply = fun k ->
  m.apply (fun a -> (h a).apply k) }

let fix_io f =
  let rec go y = f go y in
  go
