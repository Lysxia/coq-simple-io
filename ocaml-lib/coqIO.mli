type +'a t

module Impure : sig
  val mk_io : (unit -> 'a) -> 'a t
  val run : 'a t -> unit
end

val return : 'a -> 'a t
val bind : 'a t -> ('a -> 'b t) -> 'b t
val fix_io : (('a -> 'b t) -> 'a -> 'b t) -> 'a -> 'b t
