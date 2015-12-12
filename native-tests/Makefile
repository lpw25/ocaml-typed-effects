EXE=test1.native test2.native test3.native test4.native test5.native \
		test6.native test7.native test8.native test9.native
DEBUG=false
DEBUG_FLAG=

ifeq ($(DEBUG),true)
	OCAMLOPT=ocamlopt -g -runtime-variant d -S
else
	OCAMLOPT=ocamlopt
endif

all: $(EXE)

test6.native: test6.ml test6.mli test6.c
	$(OCAMLOPT) -ccopt -c -o test6_c.o test6.c
	$(OCAMLOPT) -c test6.mli
	$(OCAMLOPT) -o test6.native test6_c.o test6.ml -linkall

test7.native: test7.ml test7.mli test7.c
	$(OCAMLOPT) -ccopt -c -o test7_c.o test7.c
	$(OCAMLOPT) -c test7.mli
	$(OCAMLOPT) -o test7.native test7_c.o test7.ml -linkall

test8.native: test8.ml test8.mli test8.c
	$(OCAMLOPT) -ccopt -c -o test8_c.o test8.c
	$(OCAMLOPT) -c test8.mli
	$(OCAMLOPT) -o test8.native test8_c.o test8.ml -linkall

test9.native: test9.ml test9.mli test9.c
	$(OCAMLOPT) -ccopt -c -o test9_c.o test9.c
	$(OCAMLOPT) -c test9.mli
	$(OCAMLOPT) -o test9.native test9_c.o test9.ml -linkall

%.native: %.ml
	$(OCAMLOPT) -o $@ $<

.PHONY: clean test expected

clean:
	rm -f *.cmi *.cmx *.s *~ *.o op $(EXE) seen.out

test: all
	ls $(EXE) | xargs -I {} bash -c `pwd`/{} &> seen.out; diff expected.out seen.out

expected.out: all
	ls $(EXE) | xargs -I {} bash -c `pwd`/{} &> expected.out
