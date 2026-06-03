From Stdlib Require Import
     Strings.String
     extraction.ExtrOcamlIntConv.

From SimpleIO Require Import SimpleIO IO_Sys.
Import IO.Notations.

Open Scope string_scope.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Definition print_bool (b : bool) : IO unit :=
  print_string (ostring_of_bool b).

Parameter int_constant : int.
Extract Constant int_constant => "3".

Definition f : IO unit := IO.while_loop (fun b =>
  match b with
  | true =>
      print_bool false;;
      print_newline;;
      print_endline "Hello";;
      IO.ret None
  | false =>
      print_bool true ;;
      print_newline;;
      print_int int_constant;;
      print_newline;;
      IO.ret (Some true)
  end) false.

Definition g : IO unit :=
  _ <- OSys.command "echo ""echo test""" ;;
  IO.ret tt.

Definition y := f ;; g.

Definition y0 : io_unit := IO.unsafe_run y.

Separate Extraction y0.
