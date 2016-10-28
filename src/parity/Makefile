SOURCES = ../stdlib.ml ../simpleMap.ml ../equiv.ml ../poset.ml ../graph.ml simpleSet.mli simpleSet.ml parity.ml generateParity.ml main.ml
RESULT = parity
ANNOTATE = true
DOC_FILES = $(SOURCES)
LIBS = unix

all: dnc
	OCAMLRUNPARAM=b ./parity

disks: all
	./parity 1 1 > disk11.txt
	./parity 1 2 > disk12.txt
	./parity 1 3 > disk13.txt
	./parity 2 2 > disk22.txt
	./parity 2 3 > disk23.txt
	./parity 3 3 > disk33.txt
	rm -f /tmp/disks.zip
	zip /tmp/disks.zip disk*.txt

dist:
	rm -f parity.tar.gz
	tar zcvf parity.tar.gz OCamlMakefile Makefile $(SOURCES)

ci:
	git ci . -m "Parity."
	git push

include OCamlMakefile
