open CoqIO
let print_bool b = Impure.mk_io (fun () ->
  if b then print_endline "true" else print_endline "false")
let int_constant = 3
