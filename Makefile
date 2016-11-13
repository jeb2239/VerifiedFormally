OCAMLBUILD = corebuild
CFLAGS = -safe-string
BUILDFLAGS = -use-ocamlfind -I src/ -pkgs cil -pkgs why3 -cflags $(CFLAGS)

.PHONY: vcc
vcc:
	$(OCAMLBUILD) $(BUILDFLAGS) vcc.native

.PHONY: clean
clean:
	$(OCAMLBUILD) -clean
