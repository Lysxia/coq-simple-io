.PHONY: all build install clean

build: Makefile.coq
	$(MAKE) -f $<

install: build
	echo "TODO"

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

example: build
	mkdir -p build/out/
	cd build; \
	  coqc -Q ../src/ CoqIO ../test/Example.v
	ocamlbuild -no-hygiene -I ocaml-lib -I test build/Example.native
	mv Example.native build/out/
	./build/out/Example.native

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	$(RM) -f Makefile.coq* *.cmxs
	$(RM) -rf _build/ build/
	$(RM) {./,*/,*/*/}{*.{v.d,vo,glob},.*.aux}

COQDEP=coqdep
DEPS_DOT=deps.dot
DEPS_OUT=deps.jpg

depgraph:
	$(COQDEP) -dumpgraph $(DEPS_DOT) -Q src/ CoqIO src > /dev/null 2>&1
	sed 's%\("\([^"]*\)/\([^"/]*\)"\[label="\)%\1\2/\n%' -i deps.dot
	dot $(DEPS_DOT) -Tjpg -o$(DEPS_OUT)
