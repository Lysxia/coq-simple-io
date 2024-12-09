From SimpleIO Require Import SimpleIO.
Import IO.Notations.

RunIO IOMode Forward.

Definition cat : IO unit :=
  _ <- catch_eof
    (IO.fix_io (fun f _ =>
      input <- read_line ;;
      print_endline input ;;
      f tt :> IO unit) tt) ;;
  IO.ret tt.

RunIO cat.
