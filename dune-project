(lang dune 2.8)
(using coq 0.3)
(using menhir 2.0)
(name coq-simple-io)
(version dev)

(generate_opam_files true)

(source (github Lysxia/coq-simple-io))
(license MIT)
(authors "Li-yao Xia" "Yishuai Li")
(maintainers "lysxia@gmail.com")

(package
 (name coq-simple-io)
 (synopsis "IO monad for Coq")
 (description
"This library provides tools to implement IO programs directly in Coq, in a
similar style to Haskell. Facilities for formal verification are not
included.

IO is defined as a parameter with a purely functional interface in
Coq, to be extracted to OCaml. Some wrappers for the basic types and
functions in the OCaml Pervasives module are provided, and users are free to
define their own APIs on top of this IO type.")
 (depends
   (ocaml (>= 4.08.0))
   ocamlfind
   (coq (>= 8.11~))
   (coq-ext-lib (>= 0.10.0))
   (ocamlbuild (and :with-test (>= 0.9.0)))
   (cppo (and :build (>= 1.6.8))))
)
