(**
  Extraction of Ocaml's [Pervasives] module.

  This depends on [ExtrOcamlBasic] and [ExtrOcamlIntConv] that define extraction
  for a few basic types ([option], [list], [int]).
  Other types that do not have a natural counterpart in Coq are left abstract.
  In particular, this module does not assume any particular representation of
  Coq's [string] and [ascii] (as opposed to the [RawChar] module).
*)

Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.

Require Import SimpleIO.IOMonad.

Extraction Blacklist Pervasives.

(** * Types *)

Parameter ocaml_string : Type.
Parameter char : Type.

Parameter bytes : Type.
Parameter in_channel : Type.
Parameter out_channel : Type.
Parameter ref : Type -> Type.

(** * Misc *)

Parameter ostring_eqb : ocaml_string -> ocaml_string -> bool.
Parameter char_eqb : char -> char -> bool.

Parameter int_of_char : char -> int.

(* Equals [None] if the argument is greater than 255. *)
Parameter char_of_int_opt : int -> option char.

(* Throws an [Invalid_argument] exception if the argument is
   greater than 255. *)
Parameter char_of_int_io : int -> IO char.

Parameter ostring_of_int : int -> ocaml_string.
Parameter int_of_ostring_opt : ocaml_string -> option int.

(* Notes:
   - [int_of_ostring] would throw exceptions.
   - Comparisons between mutable structures should happen in IO.
 *)

(** * Standard channels *)

Parameter stdin : in_channel.
Parameter stdout : out_channel.
Parameter stderr : out_channel.

(** ** [stdout] *)

Parameter print_char : char -> IO unit.
Parameter print_bytes : bytes -> IO unit.
Parameter print_int : int -> IO unit.
Parameter print_string' : ocaml_string -> IO unit.
Parameter print_endline' : ocaml_string -> IO unit.
Parameter print_newline : IO unit.

(** ** [stderr] *)

Parameter prerr_char : char -> IO unit.
Parameter prerr_bytes : bytes -> IO unit.
Parameter prerr_int : int -> IO unit.
Parameter prerr_string' : ocaml_string -> IO unit.
Parameter prerr_endline' : ocaml_string -> IO unit.
Parameter prerr_newline : IO unit.

(** ** [stdin] *)

Parameter read_line' : IO ocaml_string.
Parameter read_int : IO int.
Parameter read_int_opt : IO (option int).

(** * File handles *)

(** ** Output *)

Parameter open_out' : ocaml_string -> IO out_channel.
Parameter flush : out_channel -> IO unit.
Parameter flush_all : IO unit.

Parameter output_char : out_channel -> char -> IO unit.
Parameter output_string' : out_channel -> ocaml_string -> IO unit.
Parameter output_bytes : out_channel -> bytes -> IO unit.
Parameter output_substring : out_channel -> ocaml_string -> int -> int -> IO unit.
Parameter output_byte : out_channel -> int -> IO unit.

Parameter close_out : out_channel -> IO unit.

(** ** Input *)

Parameter open_in' : ocaml_string -> IO in_channel.

Parameter input_char : in_channel -> IO char.
Parameter input_line' : in_channel -> IO ocaml_string.
Parameter input_byte : in_channel -> IO int.

Parameter close_in : in_channel -> IO unit.

(** * Mutable references *)

Parameter new_ref : forall {a}, a -> IO (ref a).
Parameter read_ref : forall {a}, ref a -> IO a.
Parameter write_ref : forall {a}, ref a -> a -> IO unit.
Parameter incr_ref : ref int -> IO unit.
Parameter decr_ref : ref int -> IO unit.

(** * Program termination *)

Parameter exit : forall {a}, int -> IO a.

(** * Extraction *)

(** ** Types *)

Extract Inlined Constant ocaml_string => "string".
Extract Inlined Constant char => "char".

Extract Inlined Constant bytes => "bytes".
Extract Inlined Constant in_channel => "Pervasives.in_channel".
Extract Inlined Constant out_channel => "Pervasives.out_channel".
Extract Constant ref "'a" => "'a Pervasives.ref".

(** ** Misc *)

Extract Inlined Constant ostring_eqb => "Pervasives.(=)".
Extract Inlined Constant char_eqb => "Pervasives.(=)".

Extract Inlined Constant int_of_char => "Pervasives.int_of_char".

Extract Constant char_of_int_opt =>
  "fun n ->
     try Some (Pervasives.char_of_int n)
     with Invalid_argument _ -> None".

Extract Constant char_of_int_io => "fun n k -> k (Pervasives.char_of_int n)".

Extract Inlined Constant ostring_of_int => "Pervasives.string_of_int".
Extract Inlined Constant int_of_ostring_opt => "Pervasives.int_of_string_opt".

(** ** Standard channels *)

Extract Inlined Constant stdin  => "Pervasives.stdin".
Extract Inlined Constant stdout => "Pervasives.stdout".
Extract Inlined Constant stderr => "Pervasives.stderr".

(** *** [stdout] *)

Extract Constant print_char     => "fun c k -> k (Pervasives.print_char    c)".
Extract Constant print_bytes    => "fun b k -> k (Pervasives.print_bytes   b)".
Extract Constant print_int      => "fun n k -> k (Pervasives.print_int     n)".
Extract Constant print_string'  => "fun s k -> k (Pervasives.print_string  s)".
Extract Constant print_endline' => "fun s k -> k (Pervasives.print_endline s)".
Extract Constant print_newline  => "fun   k -> k (Pervasives.print_newline ())".

(** *** [stderr] *)

Extract Constant prerr_char     => "fun c  k -> k (Pervasives.prerr_char    c)".
Extract Constant prerr_bytes    => "fun bs k -> k (Pervasives.prerr_bytes   bs)".
Extract Constant prerr_int      => "fun n  k -> k (Pervasives.prerr_int     n)".
Extract Constant prerr_string'  => "fun s  k -> k (Pervasives.prerr_string  s)".
Extract Constant prerr_endline' => "fun s  k -> k (Pervasives.prerr_endline s)".
Extract Constant prerr_newline  => "fun    k -> k (Pervasives.prerr_newline ())".

(** *** [stdin] *)

Extract Constant read_line'   => "fun k -> k (Pervasives.read_line ())".
Extract Constant read_int     => "fun k -> k (Pervasives.read_int  ())".
Extract Constant read_int_opt => "fun k -> k (Pervasives.read_int_opt ())".

(** ** File handles *)

(** *** Output *)

Extract Constant open_out' => "fun s k -> k (Pervasives.open_out s)".
Extract Constant flush     => "fun h k -> k (Pervasives.flush h)".
Extract Constant flush_all => "fun   k -> k (Pervasives.flush_all ())".

Extract Constant output_char    => "fun h c k -> k (Pervasives.output_char h c)".
Extract Constant output_string' => "fun h s k -> k (Pervasives.output_string h s)".
Extract Constant output_bytes   => "fun h b k -> k (Pervasives.output_bytes h b)".
Extract Constant output_byte    => "fun h b k -> k (Pervasives.output_byte h b)".
Extract Constant output_substring =>
  "fun h s i n k -> k (Pervasives.output_substring h s i n)".

Extract Constant close_out => "fun h k -> k (close_out h)".

(** *** Input *)

Extract Constant open_in' => "fun s k -> k (Pervasives.open_in s)".

Extract Constant input_char  => "fun h k -> k (Pervasives.input_char h)".
Extract Constant input_line' => "fun h k -> k (Pervasives.input_line h)".
Extract Constant input_byte  => "fun h k -> k (Pervasives.input_byte h)".

Extract Constant close_in => "fun h k -> k (Pervasives.close_in h)".

(** ** Mutable references *)

Extract Constant new_ref   =>
  "fun x k -> k (Pervasives.ref x)".
Extract Constant read_ref  =>
  "fun r k -> k (Pervasives.(!) r)".
Extract Constant write_ref =>
  "fun r x k -> k (Pervasives.(:=) r x)".
Extract Constant incr_ref  => "fun r k -> k (Pervasives.incr r)".
Extract Constant decr_ref  => "fun r k -> k (Pervasives.decr r)".

(** ** Program termination *)

Extract Constant exit => "fun n k -> k (Pervasives.exit n)".
