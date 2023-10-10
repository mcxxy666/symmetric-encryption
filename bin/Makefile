SOURCE = utilities.ml datatype.ml parser.mli parser.ml lexer.ml stype.ml einf.ml poly.ml solve.ml reduce.ml  pprint.ml main.ml

GLPK = /home/koba/program/ocaml-glpk-0.1.5/src

parser.mli parser.ml:parser.mly
	ocamlyacc parser.mly
lexer.ml:lexer.mll
	ocamllex lexer.mll

spicabyte: $(SOURCE)
	(ocamlc -o spica -I $(GLPK) glpk.cma $(SOURCE); rm *.cmi *.cmx *.o; cd ..)

spica: $(SOURCE)
	(ocamlopt -o spica -I $(GLPK) glpk.cmxa $(SOURCE); rm *.cmi *.cmx *.o; cd ..)

.SUFFIXES:
	.ml .cmo .mli .cmi

.ml.cmo:
	ocamlc $(SOURCE)

top: $(SOURCE)
	(ocamlmktop glpk.cma $(SOURCE); cd ..)

clean: 
	rm *.cmi *.cmx *.o *.cmo *.exe parser.ml lexer.ml parser.mli lexer.mli



