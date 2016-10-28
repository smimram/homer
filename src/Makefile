MONOID = monoid/freeMonoid.ml monoid/langMonoid.ml monoid/anick.ml \
         monoid/generate.ml monoid/builtin.ml
PARITY = parity/simpleSet.ml parity/parity.ml parity/generateParity.ml \
         parity/langParity.ml parity/cube.ml parity/associahedron.ml \
         parity/permutohedron.ml parity/testParity.ml
YVES = $(wildcard monoid/yves/*.ml)
SAM = $(wildcard monoid/sam/*.ml)

# Files
FILES := stdlib simpleMap equiv poset graph freeGroup lang matrix timeout \
         $(MONOID:.ml=) $(SAM:.ml=) $(YVES:.ml=) $(PARITY:.ml=) rewr
BINS := rewr
LIBS := unix
INCDIRS := -I monoid -I parity

# OCaml
OPT = .opt
OCAMLC = ocamlc$(OPT) $(INCDIRS)
OCAMLOPT = ocamlopt$(OPT) -g $(INCDIRS)
OCAMLDEP = ocamldep$(OPT) $(INCDIRS)
OCAMLLEX = ocamllex$(OPT)
OCAMLYACC = ocamlyacc$(OPT)
OCAMLDOC = ocamldoc$(OPT) $(INCDIRS)

# Definition of all used files
SYSTEM := $(shell uname)
ifeq ($(SYSTEM),Linux)
  EXE :=
else
  EXE := .exe
endif
EXEs := $(BINS:%=%$(EXE))
MLs := $(FILES:%=%.ml)
MLIs := $(FILES:%=%.mli)
CMXs := $(FILES:%=%.cmx)
CMOs := $(FILES:%=%.cmo)
CMAs := $(LIBS:%=%.cma)
CMXAs := $(LIBS:%=%.cmxa)

# Computation of generated files
MLYs := $(wildcard *.mly, $(addsuffix .mly, $(FILES) $(BINS)))
MLLs := $(wildcard *.mll, $(addsuffix .mll, $(FILES) $(BINS)))
GEN_MLs := $(addsuffix .ml, $(basename $(MLYs) $(MLLs)))
GEN_MLIs := $(addsuffix .mli, $(basename $(MLYs)))
GENs := $(EXEs) $(GEN_MLs) $(GEN_MLIs)

# Verbose
SHOW := @echo
HIDE := @

# Actions
.SUFFIXES: .mli .ml .cmi .cmx .mll .mly

test: all
	-export OCAMLRUNPARAM=b
	./rewr$(EXE) -b test.rewr

all exe: depend $(EXEs)

clean:
	rm -f *.cmi *.cmx *.cmo *.o *.jo *.obj *~ $(GENs) rewr.js *.annot

force:
	rm -f $(GEN_MLs) $(GEN_MLIs)
	make all

ci:
	svn ci -m "Worked on rewr."

dist:
	cd ..; $(MAKE) dist

doc:
	-mkdir doc
	$(OCAMLDOC) -html -d doc -sort $(MLs)

# WEB VERSION

rewr_js.cmo: rewr_js.ml $(SOURCES)
	$(OCAMLC) -annot -I `ocamlfind query js_of_ocaml` -pp "camlp4o -I `ocamlfind query js_of_ocaml` pa_js.cmo" -c rewr_js.ml

js: $(CMOs) rewr_js.cmo
	$(OCAMLC) -I `ocamlfind query js_of_ocaml` js_of_ocaml.cma $(CMAs) $(filter-out rewr.cmo,$(CMOs)) rewr_js.cmo -o rewr$(EXE)
	js_of_ocaml rewr$(EXE)

web: js
	scp rewr.html lix:.webdir/rewr/index.html
	scp rewr.js rewr.css lix:.webdir/rewr/

# GENERIC RULES

.depend depend: $(MLs)
	$(OCAMLDEP) -slash $(MLIs) $(MLs) > .depend

%$(EXE): $(CMXs) %.cmx
	$(SHOW) OCAMLOPT $(CMXAs) -o $@
	$(HIDE) $(OCAMLOPT) $(CMXAs) -o $@ $^

.mli.cmi:
	$(OCAMLOPT) -c $<

.ml.cmx:
	$(OCAMLOPT) -annot -c $<

%.cmo: %.ml
	$(OCAMLC) -annot -c $<

.mll.ml:
	$(OCAMLLEX) -q $<

.mly.ml:
	$(OCAMLYACC) -q $<

-include .depend

.PHONY: doc
