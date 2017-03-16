all:

update: rewr bergman ocamldoc

rewr:
	$(MAKE) -C ../src website

bergman:
	$(MAKE) -C ../src/bergman website

ocamldoc:
	$(MAKE) -C ../src/alg htdoc
	mkdir -p ocamldoc/alg
	cp ../src/alg/doc/alg/html/* ocamldoc/alg/
	-git add ocamldoc/alg/*.html

ci: update
	git ci . -m "Update website."
	git push

.PHONY: rewr bergman ocamldoc
