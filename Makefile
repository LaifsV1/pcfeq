MAIN=pcfeq

compile:
	ocamlbuild -I src/parser -I src/up-to-techniques -I src -use-ocamlfind -tag thread -package z3 -use-menhir src/pcfeq.native

clean:
	ocamlbuild -clean
	rm -f parser.{ml,mli} lexer.ml

show-branches:
	git log --oneline --decorate --graph --all
