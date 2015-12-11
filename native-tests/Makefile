EXE=test1.native test2.native test3.native test4.native test5.native \
		test6.native test7.native
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

%.native: %.ml
	$(OCAMLOPT) -o $@ $<

.PHONY: clean

clean:
	rm -f *.cmi *.cmx *.s *~ *.o op $(EXE)
