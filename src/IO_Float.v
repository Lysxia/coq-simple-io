From Coq Require Import ExtrOcamlIntConv.
From SimpleIO Require Import
     IO_Pervasives
     IO_Stdlib.

Module OFloat.

(** Floating-point arithmetic *)

(** Convert an integer to floating-point. *)
Parameter of_int : int -> float.

(** Multiply by [10e-6]. *)
Parameter micro : float -> float.

Module Unsafe.

(** Truncate the given floating-point number to an integer.
    The result is unspecified if the argument is [nan] or falls outside the
    range of representable integers. *)
Parameter to_int : float -> int.

(** Convert the given string to a float.  The string is read in decimal
    (by default) or in hexadecimal (marked by [0x] or [0X]).
    The format of decimal floating-point numbers is
    [ [-] dd.ddd (e|E) [+|-] dd ], where [d] stands for a decimal digit.
    The format of hexadecimal floating-point numbers is
    [ [-] 0(x|X) hh.hhh (p|P) [+|-] dd ], where [h] stands for an
    hexadecimal digit and [d] for a decimal digit.
    In both cases, at least one of the integer and fractional parts must be
    given; the exponent part is optional.
    The [_] (underscore) character can appear anywhere in the string
    and is ignored.
    Depending on the execution platforms, other representations of
    floating-point numbers can be accepted, but should not be relied upon.
    Raise [Failure "float_of_string"] if the given string is not a valid
    representation of a float. *)
Parameter of_string : ocaml_string -> float.

(* begin hide *)
Extract Constant to_int    => "Float.to_int".
Extract Constant of_string => "Float.of_string".
(* end hide *)

End Unsafe.

(** Same as [of_string], but returns [None] instead of raising. *)
Parameter of_string_opt : ocaml_string -> option float.

(** Return the string representation of a floating-point number. *)
Parameter to_string     : float -> ocaml_string.

(* begin hide *)
Extract Constant of_int        => "Float.of_int".
Extract Constant of_string_opt => "Float.of_string_opt".
Extract Constant to_string     => "Float.to_string".
Extract Constant micro         => "fun x -> x * 10e-6".
(* end hide *)

End OFloat.
