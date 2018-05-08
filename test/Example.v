Require Extraction.
Require Import CoqIO.Monad.
Import IONotations.
Open Scope io_scope.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Parameter print_bool : bool -> IO unit.
Extract Constant print_bool => "Misc.print_bool".

Definition f : IO unit := while_loop (fun b =>
  match b with
  | true =>
      print_bool false;;
      ret None
  | false =>
      print_bool true ;;
      ret (Some true)
  end) false.

Definition y : unit := unsafe_run f.

Separate Extraction y.
