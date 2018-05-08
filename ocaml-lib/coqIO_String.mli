val mk_ascii : bool * bool * bool * bool * bool * bool * bool * bool -> char
val ascii_rec :
  (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a) ->
    char -> 'a
val string_of_ocaml : string -> char list
val ocaml_of_string : char list -> string
