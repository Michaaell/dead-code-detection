include Makefile.config

LIBS=-I +compiler-libs ocamlcommon.cma -I $(OCAMLBUILDDIR)tools pprintast.cmo untypeast.cmo str.cma


SOURCES=printer.ml utils.ml opcheck.ml letrec.ml deps.ml side_effect.ml clean.ml main.ml
OBJS=$(SOURCES:.ml=.cmo)
EXEC=dead_code

all: main

main: $(OBJS)
	$(OCAMLC) $(LIBS) -o $(EXEC) $(OBJS)

%.cmo:%.ml 
	$(OCAMLC) -bin-annot $(LIBS) -c $<

%.cmi:%.mli 
	$(OCAMLC) $(LIBS) -c $<

depend: $(SOURCES)
	ocamldep *.ml *.mli > .depend

clean:
	rm -f *.cm* $(EXEC)