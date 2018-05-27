Require Extraction.
Require Import SimpleIO.CoqPervasives.
Import IONotations.

Open Scope string_scope.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Parameter print_bool : bool -> IO unit.
Extract Constant print_bool =>
  "CoqSimpleIO.Impure.mk_io_1 (fun b ->
    Pervasives.print_endline (Pervasives.string_of_bool b))".

Parameter int_constant : int.
Extract Constant int_constant => "3".

Definition f : IO unit := while_loop (fun b =>
  match b with
  | true =>
      print_bool false;;
      print_endline "Hello";;
      ret None
  | false =>
      print_bool true ;;
      print_int int_constant;;
      print_newline;;
      ret (Some true)
  end) false.

Definition y : unit := unsafe_run f.

Separate Extraction y.
