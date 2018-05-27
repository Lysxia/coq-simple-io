(**
  Extraction of Ocaml's [Pervasives] module.

  This depends on [ExtrOcamlBasic] and [ExtrOcamlIntConv] that define extraction
  for a few basic types ([option], [list], [int]).
  Other types that do not have a natural counterpart in Coq are left abstract.
  In particular, this module does not assume any particular representation of
  Coq's [string] and [ascii] (as opposed to [SimpleIO.OcamlString] and
  [SimpleIO.CoqPervasives]).
*)

Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.

Require Import SimpleIO.IOMonad.

Extraction Blacklist CoqSimpleIO Pervasives.

(** * Types *)

Parameter ocaml_string : Type.
Parameter char : Type.

Parameter bytes : Type.
Parameter in_channel : Type.
Parameter out_channel : Type.
Parameter ref : Type -> Type.

(** * Misc *)

Parameter int_of_char : char -> int.
Parameter char_of_int : int -> char.
Parameter ostring_of_int : int -> ocaml_string.

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

Extract Inlined Constant int_of_char => "Pervasives.int_of_char".
Extract Inlined Constant char_of_int => "Pervasives.char_of_int".
Extract Inlined Constant ostring_of_int => "Pervasives.string_of_int".

(** ** Standard channels *)

Extract Inlined Constant stdin  => "Pervasives.stdin".
Extract Inlined Constant stdout => "Pervasives.stdout".
Extract Inlined Constant stderr => "Pervasives.stderr".

(** *** [stdout] *)

Extract Constant print_char     => "CoqSimpleIO.Impure.mk_io_1 Pervasives.print_char".
Extract Constant print_bytes    => "CoqSimpleIO.Impure.mk_io_1 Pervasives.print_bytes".
Extract Constant print_int      => "CoqSimpleIO.Impure.mk_io_1 Pervasives.print_int".
Extract Constant print_string'  => "CoqSimpleIO.Impure.mk_io_1 Pervasives.print_string".
Extract Constant print_endline' => "CoqSimpleIO.Impure.mk_io_1 Pervasives.print_endline".
Extract Constant print_newline  => "CoqSimpleIO.Impure.mk_io_0 Pervasives.print_newline".

(** *** [stderr] *)

Extract Constant prerr_char     => "CoqSimpleIO.Impure.mk_io_1 Pervasives.prerr_char".
Extract Constant prerr_bytes    => "CoqSimpleIO.Impure.mk_io_1 Pervasives.prerr_bytes".
Extract Constant prerr_int      => "CoqSimpleIO.Impure.mk_io_1 Pervasives.prerr_int".
Extract Constant prerr_string'  => "CoqSimpleIO.Impure.mk_io_1 Pervasives.prerr_string".
Extract Constant prerr_endline' => "CoqSimpleIO.Impure.mk_io_1 Pervasives.prerr_endline".
Extract Constant prerr_newline  => "CoqSimpleIO.Impure.mk_io_0 Pervasives.prerr_newline".

(** *** [stdin] *)

Extract Constant read_line'   => "CoqSimpleIO.Impure.mk_io_0 Pervasives.read_line".
Extract Constant read_int     => "CoqSimpleIO.Impure.mk_io_0 Pervasives.read_int".
Extract Constant read_int_opt => "CoqSimpleIO.Impure.mk_io_0 Pervasives.read_int_opt".

(** ** File handles *)

(** *** Output *)

Extract Constant open_out' => "CoqSimpleIO.Impure.mk_io_1 Pervasives.open_out".
Extract Constant flush     => "CoqSimpleIO.Impure.mk_io_1 Pervasives.flush".
Extract Constant flush_all => "CoqSimpleIO.Impure.mk_io_0 Pervasives.flush_all".

Extract Constant output_char    => "CoqSimpleIO.Impure.mk_io_2 Pervasives.output_char".
Extract Constant output_string' => "CoqSimpleIO.Impure.mk_io_2 Pervasives.output_string".
Extract Constant output_bytes   => "CoqSimpleIO.Impure.mk_io_2 Pervasives.output_bytes".
Extract Constant output_byte    => "CoqSimpleIO.Impure.mk_io_2 Pervasives.output_byte".
Extract Constant output_substring =>
  "fun h s -> CoqSimpleIO.Impure.mk_io_2 (Pervasives.output_substring h s)".

Extract Constant close_out => "CoqSimpleIO.Impure.mk_io_1 close_out".

(** *** Input *)

Extract Constant open_in' => "CoqSimpleIO.Impure.mk_io_1 Pervasives.open_in".

Extract Constant input_char  => "CoqSimpleIO.Impure.mk_io_1 Pervasives.input_char".
Extract Constant input_line' => "CoqSimpleIO.Impure.mk_io_1 Pervasives.input_line".
Extract Constant input_byte  => "CoqSimpleIO.Impure.mk_io_1 Pervasives.input_byte".

Extract Constant close_in => "CoqSimpleIO.Impure.mk_io_1 Pervasives.close_in".

(** ** Mutable references *)

(* Polymorphic definitions must be eta-expanded because of the value
   restriction. *)
Extract Constant new_ref   =>
  "fun x -> CoqSimpleIO.Impure.mk_io_1 Pervasives.ref x".
Extract Constant read_ref  =>
  "fun x -> CoqSimpleIO.Impure.mk_io_1 Pervasives.(!) x".
Extract Constant write_ref =>
  "fun x -> CoqSimpleIO.Impure.mk_io_2 Pervasives.(:=) x".
Extract Constant incr_ref  => "CoqSimpleIO.Impure.mk_io_1 Pervasives.incr".
Extract Constant decr_ref  => "CoqSimpleIO.Impure.mk_io_1 Pervasives.decr".

(** ** Program termination *)

Extract Constant exit => "CoqSimpleIO.Impure.mk_io_1 Pervasives.exit".
