(lang dune 3.21)
(using rocq 0.11)
(using menhir 2.0)
(name rocq-simple-io)
(version dev)

(generate_opam_files true)

(source (github Lysxia/rocq-simple-io))
(license MIT)
(authors "Li-yao Xia" "Yishuai Li")
(maintainers "lysxia@gmail.com")

(package
 (name rocq-simple-io)
 (synopsis "IO monad for Rocq")
 (description
"This library provides tools to implement IO programs directly in Rocq, in a
similar style to Haskell. Facilities for formal verification are not
included.

IO is defined as a parameter with a purely functional interface in
Rocq, to be extracted to OCaml. Some wrappers for the basic types and
functions in the OCaml Pervasives module are provided, and users are free to
define their own APIs on top of this IO type.")
 (depends
   (ocaml (>= 4.08.0))
   ocamlfind
   (rocq-prover (< 9.3))
   (coq-ext-lib (>= 0.10.0))
   (ocamlbuild (and :with-test (>= 0.9.0)))
   (cppo (and :build (>= 1.6.8))))
)
