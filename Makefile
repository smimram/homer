all:
	$(MAKE) -C ocaml-alg $@
	$(MAKE) -C src $@

dist:
	tar zcvf rewr.tar.gz src/Makefile $(wildcard src/*.ml src/*.rewr src/*.js src/*.html src/*.css)
