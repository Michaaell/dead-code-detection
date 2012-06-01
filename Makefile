include Makefile.config

INCLUDES=-I $(TYPEREX_DIR)/typerex-config -I $(TYPEREX_DIR)/ocplib-lang -I $(TYPEREX_DIR)/ocplib-system -I $(TYPEREX_DIR)/ocaml-config \
	-I $(TYPEREX_DIR)/ocaml-utils -I $(TYPEREX_DIR)/ocaml-parsing -I $(TYPEREX_DIR)/ocaml-typing -I $(TYPEREX_DIR)/ocaml-compiler
LIBS=unix.cma str.cma $(TYPEREX_DIR)/typerex-config/typerex-config.cma $(TYPEREX_DIR)/ocplib-lang/ocplib-lang.cma $(TYPEREX_DIR)/ocplib-system/ocplib-system.cma $(TYPEREX_DIR)/ocaml-config/ocaml-config.cma $(TYPEREX_DIR)/ocaml-utils/ocaml-utils.cma $(TYPEREX_DIR)/ocaml-parsing/ocaml-parsing.cma \
	$(TYPEREX_DIR)/ocaml-typing/ocaml-typing.cma $(TYPEREX_DIR)/ocaml-compiler/ocaml-compiler.cma 

SOURCES=printer.ml utils.ml read.ml clean.ml deps.ml side_effect.ml main.ml
OBJS=$(SOURCES:.ml=.cmo)
EXEC=reader

all: main

main: $(OBJS)
	$(OCAMLC) $(LIBS) -o $(EXEC) $(OBJS)

%.cmo:%.ml 
	$(OCAMLC) $(INCLUDES) $(LIBS) -c $<

%.cmi:%.mli 
	$(OCAMLC) $(INCLUDES) $(LIBS) -c $<

depend: $(SOURCES)
	ocamldep *.ml *.mli > .depend

clean:
	rm -f *.cm* $(EXEC)