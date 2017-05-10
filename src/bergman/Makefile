SOURCES = ../stdlib.ml interface.ml bergman.ml
RESULT = bergman
INCDIRS = ../../ocaml-alg/src +../js_of_ocaml
LIBS = alg js_of_ocaml
ANNOTATE = true
USE_CAMLP4 = true

all: alg dc
	js_of_ocaml $(RESULT)

test: all test.ml
	$(OCAMLC) -g -pp "camlp4o" test.ml -o test
	OCAMLRUNPARAM=b ./test

alg:
	@$(MAKE) -C ../../ocaml-alg/src dcl INCDIRS=

website:
	cp index.html bergman.js bergman.css ../../docs/bergman

# upload: all
	# scp index.html bergman.js bergman.css lix:.webdir/bergman

include OCamlMakefile

.PHONY: alg
