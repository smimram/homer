all:

update: rewr bergman alg

rewr:
	$(MAKE) -C ../src website

bergman:
	$(MAKE) -C ../src/bergman website

alg:
	$(MAKE) -C ../ocaml-alg/src htdoc
	mkdir -p ocamldoc/alg
	cp ../ocaml-alg/src/doc/alg/html/* ocamldoc/alg/
	-git add ocamldoc/alg/*.html

ci: update
	git ci . -m "Update website."
	git push

.PHONY: rewr bergman ocamldoc
