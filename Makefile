OCAMLBUILD = corebuild
CFLAGS = -safe-string
BUILDFLAGS = -use-ocamlfind -I src/ -pkgs cil -cflags $(CFLAGS)

.PHONY: vcc
vcc:
	$(OCAMLBUILD) $(BUILDFLAGS) vcc.native

.PHONY: clean
clean:
	$(OCAMLBUILD) -clean
