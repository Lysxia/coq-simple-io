From Coq Require Import
     extraction.ExtrOcamlIntConv.

From SimpleIO Require Import
  SimpleIO
  IO_Sys.
Import IO.Notations.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

(* This test returns the number of arguments on the command line *)

Definition f : IO unit :=
  args <- OSys.argv ;;
  print_int (int_of_nat (length args)).

Definition y0 : io_unit := IO.unsafe_run f.

Separate Extraction y0.
