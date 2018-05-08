open CoqIO

(* Internal shorthand *)
let wrap_io f x = Impure.mk_io (fun () -> f x)

(* File IO *)

let stdin = Pervasives.stdin
let stdout = Pervasives.stdout
let stderr = Pervasives.stderr

(* stdout *)

let print_char = wrap_io Pervasives.print_char
let print_string = wrap_io Pervasives.print_string
let print_bytes = wrap_io Pervasives.print_bytes
let print_int = wrap_io Pervasives.print_int
let print_endline = wrap_io Pervasives.print_endline
let print_newline = Impure.mk_io Pervasives.print_newline

(* stderr *)

let prerr_char = wrap_io Pervasives.prerr_char
let prerr_string = wrap_io Pervasives.prerr_string
let prerr_bytes = wrap_io Pervasives.prerr_bytes
let prerr_int = wrap_io Pervasives.prerr_int
let prerr_endline = wrap_io Pervasives.prerr_endline
let prerr_newline = Impure.mk_io Pervasives.prerr_newline

(* stdin *)

let read_line = Impure.mk_io Pervasives.read_line
let read_int = Impure.mk_io Pervasives.read_int
let read_int_opt = Impure.mk_io Pervasives.read_int_opt

(* File handles *)

(* Output *)

let open_out = wrap_io Pervasives.open_out
let flush = wrap_io Pervasives.flush
let flush_all = Impure.mk_io Pervasives.flush_all

let output_char h = wrap_io (Pervasives.output_char h)
let output_string h = wrap_io (Pervasives.output_string h)
let output_bytes h = wrap_io (Pervasives.output_bytes h)
let output_byte h = wrap_io (Pervasives.output_byte h)

let close_out = wrap_io Pervasives.close_out

(* Input *)

let open_in = wrap_io Pervasives.open_in

let input_char = wrap_io Pervasives.input_char
let input_line = wrap_io Pervasives.input_line
let input_byte = wrap_io Pervasives.input_byte

let close_in = wrap_io Pervasives.close_in

(* References *)

type 'a ref = 'a Pervasives.ref

let new_ref x = wrap_io Pervasives.ref x
let read_ref r = wrap_io Pervasives.(!) r
let write_ref r = wrap_io (Pervasives.(:=) r)
let incr_ref = wrap_io Pervasives.incr
let decr_ref = wrap_io Pervasives.decr

(* Termination *)

let exit = wrap_io Pervasives.exit
