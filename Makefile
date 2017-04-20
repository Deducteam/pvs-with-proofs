.PHONY: all patch-300

all: logic.dko patch-300

patch-300:
	cp pvs-with-proofs.lisp $$PVS_LIBRARY_PATH/pvs-patches/patch-300.lisp

%.dko: %.dk
	dkcheck -e $<
	cp logic.dko ints/
	cp logic.dko induction/
