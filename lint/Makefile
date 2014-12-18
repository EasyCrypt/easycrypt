# -*- Makefile -*-

# --------------------------------------------------------------------
OCAMLBUILD_BIN   = ocamlbuild -use-ocamlfind
OCAMLBUILD_EXTRA = -classic-display

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_EXTRA += -classic-display
endif
OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_EXTRA)

# --------------------------------------------------------------------
.PHONY: all clean

all:
	$(OCAMLBUILD) ppx_lint.native

clean:
	$(OCAMLBUILD) -clean
	rm -f ppx_lint.native* ppx_lint.byte*
