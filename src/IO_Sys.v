(** * System interface *)

(** Note: descriptions of the interface are derived from OCaml's documentation:
    https://caml.inria.fr/pub/docs/manual-ocaml/libref/Sys.html *)

(* begin hide *)
From Coq Require Import
     ExtrOcamlIntConv.

From SimpleIO Require Import
     IO_Monad
     IO_Stdlib.
(* end hide *)

Module OSys.

(** Execute the given shell command and return its exit code.
  The argument of [Sys.command] is generally the name of a
  command followed by zero, one or several arguments, separated
  by whitespace.  The given argument is interpreted by a
  shell: either the Windows shell [cmd.exe] for the Win32 ports of
  OCaml, or the POSIX shell [sh] for other ports.  It can contain
  shell builtin commands such as [echo], and also special characters
  such as file redirections [>] and [<], which will be honored by the
  shell.
  Conversely, whitespace or special shell characters occurring in
  command names or in their arguments must be quoted or escaped
  so that the shell does not interpret them.  The quoting rules vary
  between the POSIX shell and the Windows shell.
  The [Filename.quote_command] performs the appropriate quoting
  given a command name, a list of arguments, and optional file redirections.
*)
Parameter command: ocaml_string -> IO int.

(** Return the value associated to a variable in the process environment.
    Raise [Not_found] if the variable is unbound. *)
Parameter getenv : ocaml_string -> IO ocaml_string.

(** Return the value associated to a variable in the process environment or
    [None] if the variable is unbound. *)
Parameter getenv_opt: ocaml_string -> IO (option ocaml_string).

(** Return the processor time, in seconds, used by the program
    since the beginning of execution. *)
Parameter time : IO float.

(** ** Extraction *)

Extract Constant command    => "fun c k -> k (Sys.command    c)".
Extract Constant getenv     => "fun e k -> k (Sys.getenv     e)".
Extract Constant getenv_opt => "fun e k -> k (Sys.getenv_opt e)".
Extract Constant time       => "fun   k -> k (Sys.time      ())".

End OSys.
