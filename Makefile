# -*- Makefile -*-

# --------------------------------------------------------------------
CONFIG           = _tags myocamlbuild.ml
OCAMLBUILD_BIN   = ocamlbuild
OCAMLBUILD_EXTRA = -classic-display -menhir "menhir --explain"

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_EXTRA += -cflag "-dtypes" -tag debug -classic-display
endif
OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_EXTRA)

# --------------------------------------------------------------------
.PHONY: all build byte native check clean tags

all: build

build: byte

byte: tags
	$(OCAMLBUILD) src/ec.byte

native: tags
	$(OCAMLBUILD) src/ec.native

check: byte
	./scripts/runtest.py     \
	  --bin=./ec.byte        \
	  --ok-dir=tests/success \
	  --ko-dir=tests/fail    \
          --ok-dir=theories

clean:
	$(OCAMLBUILD) -clean
	set -e; for i in $(CONFIG); do [ \! -h "$$i" ] || rm -f "$$i"; done

tags:
	set -e; for i in $(CONFIG); do [ -e "$$i" ] || ln -s config/"$$i" $$i; done
