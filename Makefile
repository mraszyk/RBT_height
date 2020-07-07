all: main.native

main.native: main.ml RBT_height.ml
	ocamlbuild -package zarith main.native
