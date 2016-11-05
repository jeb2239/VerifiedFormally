OCAMLBUILD = corebuild
CFLAGS = -safe-string
BUILDFLAGS = -use-ocamlfind -pkgs cil -cflags $(CFLAGS)

vcc: *.ml *.mli
	$(OCAMLBUILD) $(BUILDFLAGS) vcc.native

.PHONY: clean
clean:
	$(OCAMLBUILD) -clean
