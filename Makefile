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
DISTDIR  := easycrypt-$(VERSION)
THEORIES := $(wildcard theories/*.ec)
PRELUDE  := $(wildcard theories/prelude/*.ec)
INSTALL  := scripts/install-sh

# --------------------------------------------------------------------
XUNITOUT ?= xunit.xml
ECARGS   ?=
CHECK     = scripts/runtest.py config/tests.config

# --------------------------------------------------------------------
.PHONY: all build byte native tests check check-xunit examples tags
.PHONY: clean install uninstall dist distcheck why3
.PHONY: pg toolchain update-toolchain %.ml %.mli %.inferred.mli

all: build

build: native

define do-build
	$(OCAMLBUILD) "$(1)"
endef

byte: tags
	$(call do-build,src/ec.byte)

native: tags
	$(call do-build,src/ec.native)

install: ec.native
	$(INSTALL) -m 0755 -d $(DESTDIR)$(PREFIX)/bin
	$(INSTALL) -m 0755 -T ec.native $(DESTDIR)$(PREFIX)/bin/easycrypt
	$(INSTALL) -m 0755 -d $(DESTDIR)$(PREFIX)/lib/easycrypt/theories
	$(INSTALL) -m 0644 -t $(DESTDIR)$(PREFIX)/lib/easycrypt/theories $(THEORIES)
	$(INSTALL) -m 0755 -d $(DESTDIR)$(PREFIX)/lib/easycrypt/theories/prelude
	$(INSTALL) -m 0644 -t $(DESTDIR)$(PREFIX)/lib/easycrypt/theories/prelude $(PRELUDE)

uninstall:
	rm -f $(DESTDIR)$(PREFIX)/bin/easycrypt
	rm -f $(patsubst %,$(DESTDIR)$(PREFIX)/lib/easycrypt/%,$(PRELUDE))
	rm -f $(patsubst %,$(DESTDIR)$(PREFIX)/lib/easycrypt/%,$(THEORIES))
	-@rmdir $(DESTDIR)$(PREFIX)/lib/easycrypt/theories/prelude
	-@rmdir $(DESTDIR)$(PREFIX)/lib/easycrypt/theories
	-@rmdir $(DESTDIR)$(PREFIX)/lib/easycrypt

tests: check

examples:
	$(CHECK) examples

check: ec.native
	$(CHECK) prelude theories unit

check-xunit: ec.native
	$(CHECK) --xunit="$(XUNITOUT)" prelude theories unit

checklibs: ec.native
	$(CHECK) --xunit=libresults.xml prelude theories

clean:
	$(OCAMLBUILD) -clean
	set -e; for i in $(CONFIG); do [ \! -h "$$i" ] || rm -f "$$i"; done

tags:
	set -e; for i in $(CONFIG); do [ -e "$$i" ] || ln -s config/"$$i" $$i; done

# --------------------------------------------------------------------
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
	$(call do-build,src/$*.cmo)

# --------------------------------------------------------------------
%.mli:
	$(call do-build,src/$*.cmi)

# --------------------------------------------------------------------
%.inferred.mli:
	$(call do-build,src/$@) && cat _build/src/$@

# --------------------------------------------------------------------
pg:
	$(MAKE) -C proofgeneral run-local

# --------------------------------------------------------------------
TOOLCHAIN_URL := http://ci.easycrypt.info/scripts/ec-build-toolchain

toolchain:
	bash ./scripts/ec-build-toolchain

update-toolchain:
	$$(./scripts/activate-toolchain.sh) \
	  && opam update  -y \
	  && opam remove  -y ec-toolchain \
	  && opam install -y ec-toolchain
