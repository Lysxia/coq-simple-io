open Constrexpr

type builder = Ocamlfind | Ocamlbuild | Dune of string

val set_builder : builder -> unit

(* Handle extra ocaml directory to be copied *)
val add_extra_dir : string -> unit
val add_extra_pkg : string -> unit
val add_module_to_open : string -> unit

(* Automatically insert common dependencies (zarith, coq-simple-io.extraction).
   [true] by default. *)
val smart_mode : bool ref

val apply_constr : constr_expr -> constr_expr list -> constr_expr_r
val mk_ref : string -> constr_expr
val string_of_constr_expr : constr_expr -> string
val define_and_run : plugin_name:string -> Environ.env -> Evd.evar_map -> Evd.econstr -> unit
val run : plugin_name:string -> constr_expr -> unit
