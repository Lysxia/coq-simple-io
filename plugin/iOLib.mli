open Constrexpr

type filename = string
type builder = Ocamlfind of string | Ocamlbuild of string | Dune of filename * string

val set_builder : builder -> unit

(* Handle extra ocaml directory to be copied *)
val add_extra_dir : string -> unit
val add_extra_pkg : string -> unit
val add_module_to_open : string -> unit

(* Automatically insert common dependencies (zarith, coq-simple-io.extraction).
   [true] by default. *)
val smart_mode : bool ref

(** Option for handling standard input and output *)
type io_mode
  = Repl
  (** Default mode compatible with interactive Coq sessions *)
  | Forward
  (** Forward stdin,stdout,stderr to the child processes running the extracted
      programs. This option lets you run [RunIO] scripts from the command line. *)

(** See [type io_mode] above. *)
val io_mode : io_mode ref

val reset : unit -> unit

val apply_constr : constr_expr -> constr_expr list -> constr_expr_r
val mk_ref : string -> constr_expr
val define_and_run : plugin_name:string -> opaque_access:Compat.indirect_accessor ->
  Environ.env -> Evd.evar_map -> Evd.econstr -> unit
val run : plugin_name:string -> opaque_access:Compat.indirect_accessor -> name:string -> constr_expr -> unit
