# -*- Makefile -*-

# --------------------------------------------------------------------
CONFIG           = _tags myocamlbuild.ml
OCAMLBUILD_BIN   = ocamlbuild
OCAMLBUILD_EXTRA = -no-hygiene -classic-display

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_EXTRA += -cflag "-dtypes" -tag debug -classic-display
endif
OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_EXTRA)

# --------------------------------------------------------------------
.PHONY: all build clean tags tests

all: build

build: tags
	$(OCAMLBUILD) src/ec.native

clean:
	$(OCAMLBUILD) -clean
	set -e; for i in $(CONFIG); do [ \! -h "$$i" ] || rm -f "$$i"; done

tags:
	set -e; for i in $(CONFIG); do [ -e "$$i" ] || ln -s config/"$$i" $$i; done
