TOPFILE = rc
OCAMLC = ocamlfind c
OCAMLOPT = ocamlfind opt
OCAMLDEP = ocamlfind dep
SOURCES = Language.ml SM.ml X86.ml Driver.ml
<<<<<<< HEAD
LIBS = GT.cma unix.cma re.cma emacs/re_emacs.cma str/re_str.cma
# LIBS = GT.cma unix.cma re.cma re_emacs.cma re_str.cma
CAMLP5 = -pp "camlp5o -I `ocamlfind -query GT.syntax` -I `ocamlfind -query ostap.syntax` pa_ostap.cmo pa_gt.cmo -L `ocamlfind -query GT.syntax`"
=======
CAMLP5 = -syntax camlp5o -package ostap.syntax,GT.syntax.all
>>>>>>> dcf275fda6eb350b2ff39f58182dfcda201cbef1
PXFLAGS = $(CAMLP5)
BFLAGS = -rectypes
OFLAGS = $(BFLAGS)

all: .depend $(TOPFILE).opt

.depend: $(SOURCES)
	$(OCAMLDEP) $(PXFLAGS) *.ml > .depend

$(TOPFILE).opt: $(SOURCES:.ml=.cmx)
	$(OCAMLOPT) -o $(TOPFILE).opt $(OFLAGS) $(LIBS:.cma=.cmxa) -linkpkg -package ostap $(SOURCES:.ml=.cmx)

$(TOPFILE).byte: $(SOURCES:.ml=.cmo)
	$(OCAMLC) -o $(TOPFILE).byte $(BFLAGS) $(LIBS) -linkpkg -package ostap $(SOURCES:.ml=.cmo) 

clean:
	rm -Rf *.cmi *.cmo *.cmx *.annot *.o *.opt *.byte *~ .depend

-include .depend
# generic rules

###############
%.cmi: %.mli
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

# Note: cmi <- mli should go first
%.cmi: %.ml
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

%.cmo: %.ml
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

%.o: %.ml
	$(OCAMLOPT) -c $(OFLAGS) $(STATIC) $(PXFLAGS) $<

%.cmx: %.ml
	$(OCAMLOPT) -c $(OFLAGS) $(STATIC) $(PXFLAGS) $<
