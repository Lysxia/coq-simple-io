(** This code was originally from from QuickChick, under the MIT license. *)

open Pp
open Names
open Declare
open Libnames
open Util
open Constrintern
open Constrexpr

include Compat

(** * Global settings *)

type filename = string
type builder = Ocamlfind of string | Ocamlbuild of string | Dune of filename * string

let builder : builder ref =
  Summary.ref ~name:"runio_builder" (Ocamlfind "")
let set_builder b = builder := b

(* Handle extra ocaml directory to be copied *)
let extra_dir : string list ref = Summary.ref ~name:"runio_ocaml_dir" []
let add_extra_dir s = extra_dir := s :: !extra_dir

let extra_pkg : string list ref = Summary.ref ~name:"runio_ocaml_pkg" []
let add_extra_pkg s = extra_pkg := s :: !extra_pkg

let modules_to_open : string list ref = Summary.ref ~name:"runio_modules_to_open" []
let add_module_to_open s = modules_to_open := s :: !modules_to_open

(* Automatically insert common dependencies (zarith, coq-core.kernel).
   [true] by default. *)
let smart_mode : bool ref =
  Summary.ref ~name:"runio_smart_mode" true

type io_mode
  = Repl
  (** Default mode compatible with interactive Coq sessions *)
  | Forward
  (** Forward stdin,stdout,stderr to the child processes running the extracted
      programs. This option lets you run [RunIO] scripts from the command line. *)

let io_mode = Summary.ref ~name:"runio_io_mode" Repl

let reset () =
  builder := Ocamlfind "";
  extra_dir := [];
  extra_pkg := [];
  modules_to_open := [];
  smart_mode := true;
  io_mode := Repl

(** * General helper functions *)

let (</>) = Filename.concat

(* Rewrite a file line by line *)
let sed_file file f =
  let src = open_in file in
  let tmpfile = file ^ ".tmp" in
  let tmp = open_out tmpfile in
  let rec go () =
    match input_line src with
    | line -> output_string tmp (f line); output_char tmp '\n'; go ()
    | exception End_of_file ->
        close_in src;
        close_out tmp;
        Sys.rename tmpfile file
  in go ()

let read_all chan =
  let buf = Buffer.create 1024 in
  let rec go () =
    match Buffer.add_channel buf chan 1024 with
    | () -> go ()
    | exception End_of_file -> Buffer.contents buf
  in go ()

let read_file file =
  let h = open_in file in
  let s = read_all h in
  close_in h;
  s

let fresh_name n =
    let base = Id.of_string n in

    (* [is_visible_name id] returns [true] if [id] is already used on
       the Coq side. *)
    let is_visible_name id =
      try
        ignore (Nametab.locate (Libnames.qualid_of_ident id));
        true
      with Not_found -> false
    in
    (* Safe fresh name generation. *)
    Namegen.next_ident_away_from base is_visible_name

(* [mkdir -p]: recursively make the parent directories if they do not exist. *)
let rec mkdir_ dname =
  let cmd () = Unix.mkdir dname 0o755 in
  try cmd () with
  | Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  | Unix.Unix_error (Unix.ENOENT, _, _) ->
    (* If the parent directory doesn't exist, try making it first. *)
    mkdir_ (Filename.dirname dname);
    cmd ()

(* [${TMP}/${PLUGIN_NAME}/${TIME}_${SALT}/main.ml],
   where [${TIME}] is the current time in format [HHMMSS]
   and [${SALT}] is a random string for uniqueness. *)
let mk_tmp_dir ~plugin_name : string =
  let tmp = Filename.get_temp_dir_name () </> plugin_name in
  mkdir_ tmp;
  mk_temp_dir tmp

(** * Extract, fix, compile, run *)

let coq_kernel = if Coq_config.version < "8.14" then "coq.kernel" else "coq-core.kernel"

let get_packages mlf =
  if !smart_mode then
    let (p_out, _, p_err) as process = Unix.open_process_full ("ocamldep -modules " ^ mlf) (Unix.environment ()) in
    let errmsg () = Feedback.msg_info (str "Unexpected error in coq-simple-io: ocamldep failed") in
    let pkgs = ref !extra_pkg in
    let opts = ref [] in
    let () =
      match input_line p_out with
      | e ->
        let modules = List.tl (String.split_on_char ' ' e) in
        modules |> List.iter (fun m ->
          let try_add ~pkg md =
            if m = md && not (List.mem pkg !pkgs) then
              pkgs := pkg :: !pkgs in
          try_add ~pkg:coq_kernel "Uint63";
          if m = "Uint63" then opts := "-rectypes" :: !opts;
          try_add ~pkg:"zarith" "Big_int_Z")
      | exception End_of_file -> errmsg () in
    let () =
      let stat = Unix.close_process_full process in
      match stat with
      | Unix.WEXITED 0 -> ()
      | _ -> errmsg ()
        (* probably an unparseable file, which will fail compilation *)
    in
    !opts, !pkgs
  else [], !extra_pkg

(* Extract the term and its dependencies *)
let extract ~opaque_access ~file ident =
  let warnings = CWarnings.get_flags () in
  let mute_extraction = (if warnings = "" then "" else warnings ^ ",") ^ "-extraction-opaque-accessed" in
  CWarnings.set_flags mute_extraction;
  Flags.silently (Compat.apply_accessor Extraction_plugin.Extract_env.full_extraction ~opaque_access (Some file)) [qualid_of_ident ident];
  CWarnings.set_flags warnings

(* Add any modules that have been marked "open" *)
let open_modules ~dir ms mlf =
  let prefix = String.concat "" List.(concat @@ map (fun m -> ["open "; m; ";;"]) ms) in
  let open_cmd = Printf.sprintf "awk -v n=1 -v s=\"%s\" 'NR == n {print s} {print}' %s > %s/__qc_tmp && mv %s/__qc_tmp %s" prefix mlf dir dir mlf in
  if Sys.command open_cmd <> 0 then
    CErrors.user_err (str "awk command failed on " ++ str mlf ++ fnl ())

let tmp_int_re = Str.regexp "type int =[ ]*int"

(* Before compiling, fix stupid cyclic dependencies like "type int = int".
   Introduced by "Definition int := int." possibly inside a module, so just
   removing it might break other definitions that depend on it.
   TODO: Generalize (.) \g1\b or something *)
let redefine_int mlf =
  sed_file mlf (fun line ->
    if Str.string_match tmp_int_re line 0 then
      "type tmptmptmp = int;; type int = tmptmptmp"
    else line)

(* Extraction sometimes produces ML code that does not implement its interface.
   We circumvent this problem by erasing the interface.  However, sometimes the
   inferred types are too abstract. So we touch the .mli to close the weak types. *)
let remove_mli mlif =
  Sys.remove mlif;
  ignore (Sys.command ("touch " ^ mlif))

let fixup ~dir mlif mlf =
  open_modules ~dir !modules_to_open mlf;
  redefine_int mlf;
  remove_mli mlif

(* Copy over the contents of the ocaml directory *)
let copy_dirs dir ds =
  List.iter (fun s -> ignore (Sys.command (Printf.sprintf "cp -r %s %s" s dir))) ds

let compile ~dir mlif mlf =
  let run_command cmd =
    if Sys.command cmd <> 0 then
      let build_log = read_file (dir ^ "/build.log") in
      let build_err = read_file (dir ^ "/build.err") in
      let msg = str "Could not compile test program: " ++ str mlf ++ fnl () in
      let msg = if build_log = "" then msg else
        msg ++ fnl () ++ str "Build stdout:" ++ fnl () ++ str build_log ++ fnl () in
      let msg = if build_err = "" then msg else
        msg ++ fnl () ++ str "Build stderr:" ++ fnl () ++ str build_err ++ fnl () in
      CErrors.user_err msg in
  let fileprefix = Filename.chop_extension mlf in
  match !builder with
  | Ocamlfind opts ->
      let execn = fileprefix ^ ".native" in
      let pkg_opts, packages = get_packages mlf in
      let packages =
        match packages with
        | [] -> ""
        | x -> "-package " ^ (String.concat "," x)
      in
      let pkg_opts =
        match pkg_opts with
        | [] -> ""
        | pkg_opts -> String.concat " " pkg_opts
      in
      run_command (Printf.sprintf
        "cd %s && ocamlfind opt -linkpkg -w -3 %s %s %s -o %s %s %s > build.log 2> build.err"
        dir pkg_opts packages opts execn mlif mlf);
      execn
  | Ocamlbuild opts ->
      let execn = Filename.basename (fileprefix ^ ".native") in
      let pkg_opts, packages = get_packages mlf in
      let packages =
        match packages with
        | [] -> ""
        | x -> "-pkgs " ^ (String.concat "," x)
      in
      let pkg_opts =
        match pkg_opts with
        | [] -> ""
        | x -> "-cflags " ^ String.concat "," x
      in
      run_command (Printf.sprintf
        "cd %s && ocamlbuild -use-ocamlfind -cflags -w,-3 %s %s %s %s > build.log 2> build.err"
        dir pkg_opts packages opts execn);
      dir </> "_build" </> execn
  | Dune (dune, opts) ->
      let execn = Filename.basename fileprefix in
      (* Modify the dune file to add the executable name and put it in the output dir *)
      let awk_cmd = Printf.sprintf
        "awk -v n=2 -v s=\"   (name %s)\" 'NR == n {print s} {print}' %s > %s"
        execn dune (dir ^ "/" ^ dune) in
      ignore (Sys.command awk_cmd);
      (* The command is just dune build *)
      run_command (Printf.sprintf
        "cd %s && dune build %s.exe --root=. --display=quiet %s > build.log 2> build.err"
        dir execn opts);
      dir </> "_build/default" </> execn ^ ".exe"

let run_exec_repl execn =
  let (p_out, _, p_err) as process = Unix.open_process_full execn (Unix.environment ()) in
  let rec process_otl_aux () =
    let e = input_line p_out in
    Feedback.msg_info (Pp.str e);
    process_otl_aux() in
  try process_otl_aux ()
  with End_of_file ->
       let err_msg = read_all p_err in
       let err descr = CErrors.user_err (str (execn ^ ": " ^ descr) ++ fnl () ++ fnl () ++ str err_msg ++ fnl ()) in
       let stat = Unix.close_process_full process in
       begin match stat with
       | Unix.WEXITED 0 -> ()
       | Unix.WEXITED i -> err (Printf.sprintf "Exited with status %d" i)
       | Unix.WSIGNALED i -> err (Printf.sprintf "Killed (%d)" i)
       | Unix.WSTOPPED i -> err (Printf.sprintf "Stopped (%d)" i)
       end

let run_exec_forward execn =
  let pid = Unix.create_process execn [|execn|] Unix.stdin Unix.stdout Unix.stderr in
  let _, status = Unix.waitpid [] pid in
  let err descr = CErrors.user_err (str (execn ^ ": " ^ descr) ++ fnl ()) in
  begin match status with
  | Unix.WEXITED 0 -> ()
  | Unix.WEXITED i -> err (Printf.sprintf "Exited with status %d" i)
  | Unix.WSIGNALED i -> err (Printf.sprintf "Killed (%d)" i)
  | Unix.WSTOPPED i -> err (Printf.sprintf "Stopped (%d)" i)
  end

let run_exec execn =
  match !io_mode with
  | Repl -> run_exec_repl execn
  | Forward -> run_exec_forward execn

let compile_and_run ~dir mlif mlf =
  compile ~dir mlif mlf |> run_exec

let extract_and_run ~plugin_name ~opaque_access ident =
  let dir            = mk_tmp_dir ~plugin_name in
  let mlf   : string = dir </> "extracted_main.ml" in
  let mlif  : string = Filename.chop_extension mlf ^ ".mli" in
  extract ~opaque_access ~file:mlf ident;
  fixup ~dir mlif mlf;
  copy_dirs dir !extra_dir;
  compile_and_run ~dir mlif mlf
;;

let mk_ref s = CAst.make @@ CRef (qualid_of_string s, None)

(** [define env evd c] introduces a fresh constant name for the term [c]. *)
let define env evd c =
  let (evd,_) = Typing.type_of env evd c in
  let univs = Evd.univ_entry ~poly:true evd in
  let fn = fresh_name "quickchick" in
  (* TODO: Maxime - which of the new internal flags should be used here? The names aren't as clear :) *)
  let _ : Constant.t = declare_constant ~name:fn ~kind:Decls.(IsDefinition Definition)
      (DefinitionEntry (definition_entry ~univs (EConstr.to_constr evd c))) in
  fn

let define_and_run ~plugin_name ~opaque_access env evd term =
  let term = define env evd term in
  extract_and_run ~plugin_name ~opaque_access term

let chatty () =
  match !io_mode with
  | Repl -> true
  | Forward -> false

let run ~plugin_name ~opaque_access ~name term =
  if chatty () then Feedback.msg_info (Pp.str ("Running " ^ name ^ " ..."));
  let env = Global.env () in
  let evd = Evd.from_env env in
  let (term,_) = interp_constr env evd term in
  define_and_run ~plugin_name ~opaque_access env evd term
  (* TODO: clean leftover files *)

let string_of_constr_expr c =
  let env = Global.env () in
  let evd = Evd.from_env env in
  Pp.string_of_ppcmds (Ppconstr.pr_constr_expr env evd c)
