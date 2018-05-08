(* [mk_ascii] and [ascii_rec] from Coq's extraction plugin code
   [coq/plugins/extraction/ExtrOcamlString.v]. *)

let mk_ascii (b0,b1,b2,b3,b4,b5,b6,b7) =
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7)

let ascii_rec f c =
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7)

let string_of_ocaml s =
  let rec go n z =
    if n = -1 then
      z
    else
      go (n-1) (String.get s n :: z)
  in go (String.length s - 1) []

let ocaml_of_string z =
  Bytes.unsafe_to_string (
    let b = Bytes.create (List.length z) in
    let rec go z i =
      match z with
      | c :: z -> Bytes.set b i c; go z (i+1)
      | [] -> b
    in go z 0)
