# -*- Makefile -*-

# --------------------------------------------------------------------
OPAM ?= 4.01.0
DEST ?= binaries

# --------------------------------------------------------------------
.PHONY: linux mac

linux:
	rm -rf dist/ build/ $(DEST)/*
	cp -r etc/. $(DEST)
	make -C .. DESTDIR=ide/$(DEST) PREFIX=/ install
	cp \
	  ../_tools/ocaml-$(OPAM)/opam/system/bin/z3 \
	  ../_tools/ocaml-$(OPAM)/opam/system/bin/alt-ergo \
	  ../_tools/ocaml-$(OPAM)/opam/system/bin/eprover \
	  ../_tools/ocaml-$(OPAM)/opam/system/lib/why3/lib/why3/why3-cpulimit \
	  $(DEST)/bin
	cp -r ../_tools/ocaml-$(OPAM)/opam/system/lib/why3/lib/.   $(DEST)/lib/
	cp -r ../_tools/ocaml-$(OPAM)/opam/system/lib/why3/share/. $(DEST)/share/
	./setup.py bdist_dumb

# --------------------------------------------------------------------
mac:
	rm -rf dist/ build/ $(DEST)/*
	cp -r etc/. $(DEST)
	make -C .. DESTDIR=ide/$(DEST) PREFIX=/ install
	cp -r ../_tools/ocaml-$(OPAM)/opam/system/lib/why3/lib/.   $(DEST)/lib/
	cp -r ../_tools/ocaml-$(OPAM)/opam/system/lib/why3/share/. $(DEST)/share/
	./setup.py bdist_dmg
