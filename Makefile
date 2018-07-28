NAME=coq-simple-io
OCAMLBUILD = ocamlbuild

MAKEFILE_COQ = Makefile.coq
MAKE_COQ = $(MAKE) -f $(MAKEFILE_COQ)

.PHONY: all build install clean example depgraph

build: $(MAKEFILE_COQ)
	$(MAKE_COQ)

install: build
	$(MAKE_COQ) install

uninstall: $(MAKEFILE_COQ)
	$(MAKE_COQ) uninstall

$(MAKEFILE_COQ): _CoqProject
	coq_makefile -f $< -o $@

# With local source files
example: build
	mkdir -p build/out/
	cd build; \
	  coqc -Q ../src/ SimpleIO ../test/Example.v
	ocamlbuild build/Example.native
	mv Example.native build/out/
	./build/out/Example.native

# With installed library (check proper installation)
test: build
	mkdir -p build/out
	cd build; \
	  coqc ../test/Example.v
	ocamlbuild build/Example.native
	mv Example.native build/out/
	./build/out/Example.native

example-pervasives: build
	mkdir -p build/out
	cd build; \
	  coqc -Q ../src/ SimpleIO ../test/TestPervasives.v
	ocamlbuild build/TestPervasives.native
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
