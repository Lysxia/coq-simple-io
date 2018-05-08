(* CPS prevents stack overflows. *)
type 'a t = { apply : 'r. ('a -> 'r) -> 'r } [@@unboxed]

module Impure = struct
  let mk_io f = { apply = fun k -> k (f ()) }

  let run m = m.apply (fun _ -> ())
end

let return a = { apply = fun k -> k a }

let bind m h = { apply = fun k ->
  m.apply (fun a -> (h a).apply k) }

let fix_io f =
  let rec go y = f go y in
  go
