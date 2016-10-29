# Make sure ocamlbuild can find opam-managed packages: first run
# "$ eval `opam config env`"

# Easiest way to build: using ocamlbuild, which in turn uses ocamlfind

# See http://caml.inria.fr/pub/docs/manual-ocaml/comp.html for suppressed errors
# 44 & 45 In particular suppressed -- no errors, constantly filled up warning reports



#no core at the moment will add
vcc:
	corebuild -use-ocamlfind -pkgs cil \
		-cflags -w,+a-4-44-45 -I src/ vcc.native

# "$ make clean" removes all generated files & test output files
.PHONY : clean
clean :
	corebuild -clean
	rm -rf *.diff stop scanner.ml parser.ml parser.mli
	rm -rf *.cmx *.cmi *.cmo *.cmx *.o *.ll *.out *.log *.diff *.output
