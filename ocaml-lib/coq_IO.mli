type +'a t

module Impure : sig
  val mk_io : (unit -> 'a) -> 'a t
  val run : 'a t -> unit
end

val return : 'a -> 'a t
val bind : 'a t -> ('a -> 'b t) -> 'b t
val loop : ('a -> 'a t) -> 'a -> 'void t
val while_loop : ('a -> 'a option t) -> 'a -> unit t
