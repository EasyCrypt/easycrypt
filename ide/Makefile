# -*- Makefile -*-

# --------------------------------------------------------------------
OPAM ?= 4.01.0
DEST ?= binaries

# --------------------------------------------------------------------
.PHONY: all

all:
	rm -rf $(DEST)/*
	cp -r etc/. $(DEST)
	make -C .. DESTDIR=ide/$(DEST) PREFIX=/ install
	cp \
	  ../_tools/ocaml-$(OPAM)/opam/system/bin/z3 \
	  ../_tools/ocaml-$(OPAM)/opam/system/bin/alt-ergo \
	  ../_tools/ocaml-$(OPAM)/opam/system/bin/eprover \
	  ../_tools/ocaml-$(OPAM)/opam/system/lib/why3/lib/why3/why3-cpulimit \
	  $(DEST)/bin/
	cp -r ../_tools/ocaml-$(OPAM)/opam/system/lib/why3/lib/.   $(DEST)/lib/
	cp -r ../_tools/ocaml-$(OPAM)/opam/system/lib/why3/share/. $(DEST)/share/
	for bin in alt-ergo; do \
    cp $$(ldd $(DEST)/bin/alt-ergo \
      | egrep 'lib(gmp)\.so' \
      | sed 's/=>//' \
      | awk '{print $$2}') \
	    $(DEST)/lib; \
	done
	./setup.py bdist
