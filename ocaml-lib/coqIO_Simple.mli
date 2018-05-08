(* File IO *)

val stdin : in_channel
val stdout : out_channel
val stderr : out_channel

(* stdout *)

val print_char : char -> unit CoqIO.t
val print_bytes : bytes -> unit CoqIO.t
val print_int : int -> unit CoqIO.t
val print_string : string -> unit CoqIO.t
val print_endline : string -> unit CoqIO.t
val print_newline : unit CoqIO.t

(* stderr *)

val prerr_char : char -> unit CoqIO.t
val prerr_bytes : bytes -> unit CoqIO.t
val prerr_int : int -> unit CoqIO.t
val prerr_string : string -> unit CoqIO.t
val prerr_endline : string -> unit CoqIO.t
val prerr_newline : unit CoqIO.t

(* stdin *)

val read_line : string CoqIO.t
val read_int : int CoqIO.t
val read_int_opt : int option CoqIO.t

(* File handles *)

(* Output *)

val open_out : string -> out_channel CoqIO.t
val flush : out_channel -> unit CoqIO.t
val flush_all : unit CoqIO.t

val output_char : out_channel -> char -> unit CoqIO.t
val output_string : out_channel -> string -> unit CoqIO.t
val output_bytes : out_channel -> bytes -> unit CoqIO.t
val output_byte : out_channel -> int -> unit CoqIO.t

val close_out : out_channel -> unit CoqIO.t

(* Input *)

val open_in : string -> in_channel CoqIO.t

val input_char : in_channel -> char CoqIO.t
val input_line : in_channel -> string CoqIO.t
val input_byte : in_channel -> int CoqIO.t

val close_in : in_channel -> unit CoqIO.t

(* References *)

type 'a ref = 'a Pervasives.ref

val new_ref : 'a -> 'a ref CoqIO.t
val read_ref : 'a ref -> 'a CoqIO.t
val write_ref : 'a ref -> 'a -> unit CoqIO.t
val incr_ref : int ref -> unit CoqIO.t
val decr_ref : int ref -> unit CoqIO.t

(* Termination *)

val exit : int -> 'a CoqIO.t
