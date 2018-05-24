NAME=coq-simple-io
OCAMLBUILD = ocamlbuild
INCLUDE = -I ocaml-lib
TARGETS = coqSimpleIO.cma coqSimpleIO.cmxa coqSimpleIO.a
OCAML_LIB = ocaml-lib
INSTALL_TARGETS = $(addprefix _build/, $(TARGETS))
INSTALL_TARGETS += _build/$(OCAML_LIB)/*.cmi
INSTALL_TARGETS += _build/$(OCAML_LIB)/*.cmo
INSTALL_TARGETS += _build/$(OCAML_LIB)/*.o
INSTALL_TARGETS += _build/$(OCAML_LIB)/*.mli
INSTALL_TARGETS += _build/$(OCAML_LIB)/*.cmx

MAKEFILE_COQ = Makefile.coq
MAKE_COQ = $(MAKE) -f $(MAKEFILE_COQ)

.PHONY: all build install clean example depgraph

build: $(MAKEFILE_COQ)
	$(MAKE_COQ)
	$(OCAMLBUILD) $(INCLUDE) $(TARGETS)

install: build
	$(MAKE_COQ) install
	ocamlfind install $(NAME) META $(INSTALL_TARGETS)

uninstall: $(MAKEFILE_COQ)
	$(MAKE_COQ) uninstall
	ocamlfind remove $(NAME)

$(MAKEFILE_COQ): _CoqProject
	coq_makefile -f $< -o $@

# With local source files
example: build
	mkdir -p build/out/
	cd build; \
	  coqc -Q ../src/ CoqSimpleIO ../test/Example.v
	ocamlbuild -no-hygiene -I ocaml-lib build/Example.native
	mv Example.native build/out/
	./build/out/Example.native

# With installed library (check proper installation)
test: build
	mkdir -p build/out
	cd build; \
	  coqc ../test/Example.v
	ocamlbuild -use-ocamlfind -pkg coq-simple-io -no-hygiene build/Example.native
	mv Example.native build/out/
	./build/out/Example.native

example-pervasives: build
	mkdir -p build/out
	cd build; \
	  coqc -Q ../src/ CoqSimpleIO ../test/TestPervasives.v
	ocamlbuild -I ocaml-lib -no-hygiene build/TestPervasives.native
	mv TestPervasives.native build/out/
	./build/out/TestPervasives.native

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	$(RM) -f Makefile.coq* *.cmxs
	$(RM) -rf _build/ build/
	$(RM) {./,*/,*/*/}{*.{v.d,vo,glob},.*.aux}
	$(RM) $(DEPS_DOT) $(DEPS_OUT)

COQDEP=coqdep
DEPS_DOT=deps.dot
DEPS_OUT=deps.jpg

depgraph:
	$(COQDEP) -dumpgraph $(DEPS_DOT) -Q src/ CoqSimpleIO src > /dev/null 2>&1
	sed 's%\("\([^"]*\)/\([^"/]*\)"\[label="\)%\1\2/\n%' -i deps.dot
	dot $(DEPS_DOT) -Tjpg -o$(DEPS_OUT)
