Require Extraction.
Require Import CoqIO.Simple.
Import IONotations.

Open Scope io_scope.
Open Scope string_scope.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Parameter print_bool : bool -> IO unit.
Extract Constant print_bool => "Misc.print_bool".

Parameter int_constant : int.
Extract Constant int_constant => "Misc.int_constant".

Definition f : IO unit := while_loop (fun b =>
  match b with
  | true =>
      print_bool false;;
      print_endline (to_ocaml_string "Hello");;
      ret None
  | false =>
      print_bool true ;;
      print_int int_constant;;
      print_newline;;
      ret (Some true)
  end) false.

Definition y : unit := unsafe_run f.

Separate Extraction y.
