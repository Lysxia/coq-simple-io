Require Extraction.
Require Import CoqIO.Monad.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Parameter print_bool : bool -> IO unit.
Extract Constant print_bool => "Misc.print_bool".

Definition f : IO unit := while_loop (fun b =>
  match b with
  | true =>
      bind (print_bool false) (fun _ => ret None)
  | false => bind (print_bool true) (fun _ => ret (Some true))
  end) false.

Definition y : unit := unsafe_run f.

Separate Extraction y.
