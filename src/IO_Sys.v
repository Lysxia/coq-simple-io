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

(** Change the current working directory of the process. *)
Parameter chdir : ocaml_string -> IO unit.

(** Create a directory with the given permissions.
    @since 4.12.0
*)
Parameter mkdir : ocaml_string -> int -> IO unit.

(** Remove an empty directory.
    @since 4.12.0
*)
Parameter rmdir : ocaml_string -> IO unit.

(** Return the current working directory of the process. *)
Parameter getcwd : IO ocaml_string.

(** Return the names of all files present in the given directory.
   Names denoting the current directory and the parent directory
   (["."] and [".."] in Unix) are not returned.  Each string in the
   result is a file name rather than a complete path.  There is no
   guarantee that the name strings in the resulting array will appear
   in any specific order; they are not, in particular, guaranteed to
   appear in alphabetical order. *)
Parameter readdir : ocaml_string -> IO (list ocaml_string).

Parameter argv : IO (list ocaml_string).

(** ** Extraction *)

Extract Constant command    => "fun c k -> k (Sys.command    c)".
Extract Constant getenv     => "fun e k -> k (Sys.getenv     e)".
Extract Constant getenv_opt => "fun e k -> k (Sys.getenv_opt e)".
Extract Constant time       => "fun   k -> k (Sys.time      ())".
Extract Constant chdir      => "fun d k -> k (Sys.chdir      d)".
Extract Constant mkdir    => "fun d m k -> k (Sys.mkdir    d m)".
Extract Constant rmdir      => "fun d k -> k (Sys.rmdir      d)".
Extract Constant getcwd     => "fun   k -> k (Sys.getcwd    ())".
Extract Constant readdir    => "fun d k -> k (Array.to_list (Sys.readdir d))".
Extract Constant argv       => "fun   k -> k (Array.to_list (Sys.argv))".

End OSys.
