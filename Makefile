# -*- Makefile -*-

# --------------------------------------------------------------------
CONFIG           = _tags myocamlbuild.ml
OCAMLBUILD_BIN   = ocamlbuild -use-ocamlfind
OCAMLBUILD_EXTRA = -classic-display

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_EXTRA += -classic-display
endif
OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_EXTRA)

DESTDIR  ?=
PREFIX   ?= /usr/local
VERSION  ?= $(shell date '+%F')
DISTDIR   = easycrypt-$(VERSION)
THEORIES  = $(wildcard theories/*.ec)

# --------------------------------------------------------------------
INSTALL   ?= scripts/install-sh
XUNITOUT  ?= xunit.xml
CHECKARGS ?=

CHECK = \
	./scripts/runtest.py             \
	  --bin=./ec.native              \
	  --bin-args="$(CHECKARGS)"      \
	  --ok-dir=theories              \
	  --ok-dir=tests/typing/success  \
	  --ko-dir=tests/typing/fail     \
	  --ok-dir=tests/modules/success \
	  --ko-dir=tests/modules/fail

CHECKLIBS = \
	./scripts/runtest.py        \
	  --bin=./ec.native         \
	  --bin-args="$(CHECKARGS)" \
	  --ok-dir=theories

# --------------------------------------------------------------------
.PHONY: all build byte native check check-xunit tags
.PHONY: clean install uninstall dist distcheck
.PHONY: %.ml

all: build

build: native

byte: tags
	$(OCAMLBUILD) src/ec.byte

native: tags
	$(OCAMLBUILD) src/ec.native

install: ec.native
	$(INSTALL) -m 0755 -d $(DESTDIR)$(PREFIX)/bin
	$(INSTALL) -m 0755 -T ec.native $(DESTDIR)$(PREFIX)/bin/easycrypt
	$(INSTALL) -m 0755 -d $(DESTDIR)$(PREFIX)/lib/easycrypt/theories
	$(INSTALL) -m 0644 -t $(DESTDIR)$(PREFIX)/lib/easycrypt/theories $(THEORIES)

uninstall:
	rm -f $(DESTDIR)$(PREFIX)/bin/easycrypt
	rm -f $(patsubst %,$(DESTDIR)$(PREFIX)/lib/easycrypt/%,$(THEORIES))
	-@rmdir $(DESTDIR)$(PREFIX)/lib/easycrypt/theories
	-@rmdir $(DESTDIR)$(PREFIX)/lib/easycrypt

check: ec.native
	$(CHECK)

checklibs: ec.native
	$(CHECKLIBS)

check-xunit: ec.native
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

distcheck: dist
	tar -xof $(DISTDIR).tar.bz2
	set -x; \
	     $(MAKE) -C $(DISTDIR) \
	  && $(MAKE) -C $(DISTDIR) dist \
	  && mkdir $(DISTDIR)/dist1 $(DISTDIR)/dist2 \
	  && ( cd $(DISTDIR)/dist1 && tar -xof ../$(DISTDIR).tar.bz2 ) \
	  && ( cd $(DISTDIR)/dist2 && tar -xof ../../$(DISTDIR).tar.bz2 ) \
	  && diff -rq $(DISTDIR)/dist1 $(DISTDIR)/dist2 \
	  || exit 1
	rm -rf $(DISTDIR)
	@echo "$(DISTDIR) is ready for distribution" | \
	  sed -e 1h -e 1s/./=/g -e 1p -e 1x -e '$$p' -e '$$x'

# --------------------------------------------------------------------
%.ml:
	$(OCAMLBUILD) src/$*.cmo

# --------------------------------------------------------------------
%.inferred.mli:
	$(OCAMLBUILD) src/$@ && cat _build/src/$@
