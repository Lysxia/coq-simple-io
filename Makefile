NAME=coq-simple-io
OCAMLBUILD = ocamlbuild

MAKEFILE_COQ = Makefile.coq
MAKE_COQ = $(MAKE) -f $(MAKEFILE_COQ)

.PHONY: all build install clean example depgraph doc html html-raw compat

build: $(MAKEFILE_COQ) compat
	$(MAKE_COQ)

doc: html

install: build
	$(MAKE_COQ) install

uninstall: $(MAKEFILE_COQ)
	$(MAKE_COQ) uninstall

$(MAKEFILE_COQ): _CoqProject
	coq_makefile -f $< -o $@

COMPATFILES:=plugin/coqsimpleio.mlg \
  src/IO_Stdlib.v \
  src/IO_RawChar.v \
  src/IO_String.v \
  src/IO_Float.v \
  src/IO_Unsafe.v

compat: $(COMPATFILES)

COQ_VERSION:=$(word 1, $(shell coqc -print-version))
OCAML_VERSION:=$(shell ocamlc -version)

%: %.cppo
	$(V)cppo -V COQ:$(COQ_VERSION) -V OCAML:$(OCAML_VERSION) -n -o $@ $^

# With local source files
test: build
	sh test.sh Example
	sh test.sh TestPervasives
	sh test.sh TestExtraction
	sh test.sh RunIO -n

# With installed library (check proper installation)
install-test: build
	sh test.sh Example -i ""

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) Makefile.coq* *.cmxs
	$(RM) -r _build/ build/
	$(RM) $(DEPS_DOT) $(DEPS_OUT)
	$(RM) test/*.ml{i,}
	$(RM) $(COMPATFILES)

COQDEP=coqdep
DEPS_DOT=deps.dot
DEPS_OUT=deps.jpg

depgraph:
	$(COQDEP) -dumpgraph $(DEPS_DOT) -Q src/ SimpleIO src > /dev/null 2>&1
	sed 's%\("\([^"]*\)/\([^"/]*\)"\[label="\)%\1\2/\n%' -i deps.dot
	dot $(DEPS_DOT) -Tjpg -o$(DEPS_OUT)

## coqdoc -------------------------------------------------
COQDOCFLAGS:= \
  -t "Simple IO" \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments

ifdef COQDOCJS_DIR
COQDOCFLAGS+=--with-header $(COQDOCJS_DIR)/extra/header.html --with-footer $(COQDOCJS_DIR)/extra/footer.html

html: html-raw
	cp $(COQDOCJS_DIR)/extra/resources/* doc
else
html: html-raw
	@echo "`tput bold``tput setaf 3`WARNING: coqdocjs not set.`tput sgr0` This will produce ugly docs. Set the COQDOCJS_DIR variable when invoking make."
endif

export COQDOCFLAGS

html-raw: Makefile.coq
	rm -rf html
	$(MAKE_COQ) html
	cp -r html/. doc/

## -------------------------------------------------------
