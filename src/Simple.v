Require Strings.Ascii.
Require Extraction.
Require Export ExtrOcamlIntConv.
Require Export CoqIO.Monad.
Require Export CoqIO.String.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Definition string := ocaml_string.

Parameter bytes : Type.
Parameter in_channel : Type.
Parameter out_channel : Type.
Parameter ref : Type -> Type.

Parameter stdin : in_channel.
Parameter stdout : out_channel.
Parameter stderr : out_channel.

(* stdout *)

Parameter print_char : char -> IO unit.
Parameter print_bytes : bytes -> IO unit.
Parameter print_int : int -> IO unit.
Parameter print_string : string -> IO unit.
Parameter print_endline : string -> IO unit.
Parameter print_newline : IO unit.

(* stderr *)

Parameter prerr_char : char -> IO unit.
Parameter prerr_bytes : bytes -> IO unit.
Parameter prerr_int : int -> IO unit.
Parameter prerr_string : string -> IO unit.
Parameter prerr_endline : string -> IO unit.
Parameter prerr_newline : IO unit.

(* stdin *)

Parameter read_line : IO string.
Parameter read_int : IO int.
Parameter read_int_opt : IO int.

(* File handles *)

(* Output *)

Parameter open_out : string -> IO out_channel.
Parameter flush : out_channel -> IO unit.
Parameter flush_all : IO unit.

Parameter output_char : out_channel -> char -> IO unit.
Parameter output_string : out_channel -> string -> IO unit.
Parameter output_bytes : out_channel -> bytes -> IO unit.
Parameter output_byte : out_channel -> int -> IO unit.

Parameter close_out : out_channel -> IO unit.

(* Input *)

Parameter open_in : string -> IO in_channel.

Parameter input_char : in_channel -> IO char.
Parameter input_line : in_channel -> IO string.
Parameter input_byte : in_channel -> IO int.

Parameter close_in : in_channel -> IO unit.

(* References *)

Parameter new_ref : forall {a}, a -> IO (ref a).
Parameter read_ref : forall {a}, ref a -> IO a.
Parameter write_ref : forall {a}, ref a -> a -> IO unit.
Parameter incr_ref : ref int -> IO unit.
Parameter decr_ref : ref int -> IO unit.

(* Termination *)

Parameter exit : forall {a}, int -> IO a.

(**)

Extract Constant bytes => "bytes".
Extract Constant in_channel => "in_channel".
Extract Constant out_channel => "out_channel".
Extract Constant ref "'a" => "'a ref".

Extract Constant stdin => "CoqIO_Simple.stdin".
Extract Constant stdout => "CoqIO_Simple.stdout".
Extract Constant stderr => "CoqIO_Simple.stderr".

(* stdout *)

Extract Constant print_char => "CoqIO_Simple.print_char".
Extract Constant print_bytes => "CoqIO_Simple.print_bytes".
Extract Constant print_int => "CoqIO_Simple.print_int".
Extract Constant print_string => "CoqIO_Simple.print_string".
Extract Constant print_endline => "CoqIO_Simple.print_endline".
Extract Constant print_newline => "CoqIO_Simple.print_newline".

(* stderr *)

Extract Constant prerr_char => "CoqIO_Simple.prerr_char".
Extract Constant prerr_bytes => "CoqIO_Simple.prerr_bytes".
Extract Constant prerr_int => "CoqIO_Simple.prerr_int".
Extract Constant prerr_string => "CoqIO_Simple.prerr_string".
Extract Constant prerr_endline => "CoqIO_Simple.prerr_endline".
Extract Constant prerr_newline => "CoqIO_Simple.prerr_newline".

(* stdin *)

Extract Constant read_line => "CoqIO_Simple.read_line".
Extract Constant read_int => "CoqIO_Simple.read_int".
Extract Constant read_int_opt => "CoqIO_Simple.read_int_opt".

(* File handles *)

(* Output *)

Extract Constant open_out => "CoqIO_Simple.open_out".
Extract Constant flush => "CoqIO_Simple.flush".
Extract Constant flush_all => "CoqIO_Simple.flush_all".

Extract Constant output_char => "CoqIO_Simple.output_char".
Extract Constant output_string => "CoqIO_Simple.output_string".
Extract Constant output_bytes => "CoqIO_Simple.output_bytes".
Extract Constant output_byte => "CoqIO_Simple.output_byte".

Extract Constant close_out => "CoqIO_Simple.close_out".

(* Input *)

Extract Constant open_in => "CoqIO_Simple.open_in".

Extract Constant input_char => "CoqIO_Simple.input_char".
Extract Constant input_line => "CoqIO_Simple.input_line".
Extract Constant input_byte => "CoqIO_Simple.input_byte".

Extract Constant close_in => "CoqIO_Simple.close_in".

(* References *)

Extract Constant new_ref => "CoqIO_Simple.new_ref".
Extract Constant read_ref => "CoqIO_Simple.read_ref".
Extract Constant write_ref => "CoqIO_Simple.write_ref".
Extract Constant incr_ref => "CoqIO_Simple.incr_ref".
Extract Constant decr_ref => "CoqIO_Simple.decr_ref".

(* Termination *)

Extract Constant exit => "CoqIO_Simple.exit".
