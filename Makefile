# -*- Makefile -*-

# --------------------------------------------------------------------
CONFIG           = _tags myocamlbuild.ml
OCAMLBUILD_BIN   = ocamlbuild
OCAMLBUILD_EXTRA = -classic-display

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_EXTRA += -classic-display
endif
OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_EXTRA)

CHECK = \
	./scripts/runtest.py             \
	  --bin=./ec.byte                \
	  --ok-dir=theories              \
	  --ok-dir=tests/typing/success  \
	  --ko-dir=tests/typing/fail     \
	  --ok-dir=tests/modules/success \
	  --ko-dir=tests/modules/fail

XUNITOUT ?= xunit.xml
VERSION  ?= $(shell date '+%F')
DISTDIR   = easycrypt-$(VERSION)

# --------------------------------------------------------------------
.PHONY: all build byte native check check-xunit clean tags dist
.PHONY: %.ml

all: build

build: byte

byte: tags
	$(OCAMLBUILD) src/ec.byte

native: tags
	$(OCAMLBUILD) src/ec.native

check: byte
	$(CHECK)

check-xunit:
	$(CHECK) --xunit="$(XUNITOUT)"

clean:
	$(OCAMLBUILD) -clean
	set -e; for i in $(CONFIG); do [ \! -h "$$i" ] || rm -f "$$i"; done

tags:
	set -e; for i in $(CONFIG); do [ -e "$$i" ] || ln -s config/"$$i" $$i; done

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 tar -cjf $(DISTDIR).tar.bz2 --owner=0 --group=0 $(DISTDIR)
	rm -rf $(DISTDIR)

# --------------------------------------------------------------------
%.ml:
	$(OCAMLBUILD) src/$*.cmo
