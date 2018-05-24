type +'a t

module Impure : sig
  val mk_io_0 : (unit -> 'a) -> 'a t
  val mk_io_1 : ('b -> 'a) -> 'b -> 'a t
  val mk_io_2 : ('c -> 'b -> 'a) -> 'c -> 'b -> 'a t
  val run : 'a t -> unit
end

val return : 'a -> 'a t
val bind : 'a t -> ('a -> 'b t) -> 'b t
val fix_io : (('a -> 'b t) -> 'a -> 'b t) -> 'a -> 'b t
