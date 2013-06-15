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
INSTALL  := scripts/install-sh

# --------------------------------------------------------------------
XUNITOUT     ?= xunit.xml
ECARGS       ?=
CHECKARGS    := $(ECARGS) -I theories
CHECKLIBARGS := $(CHECKARGS) -p Eprover -p Alt-Ergo -p Z3

OKTESTS = \
	  --ok-dir=tests/theories/success \
	  --ok-dir=tests/typing/success   \
	  --ok-dir=tests/modules/success  \
	  --ok-dir=tests/third-party      \
	  --ok-dir=tests/unclassified     \
	  --ok-dir=tests/tactics/success  \
	  --ok-dir=tests/phl/success      \
	  --ok-dir=tests/prhl/success     

KOTESTS = \
	  --ko-dir=tests/typing/fail      \
	  --ko-dir=tests/modules/fail     \
	  --ko-dir=tests/theories/fail    \
	  --ko-dir=tests/tactics/fail     \
	  --ko-dir=tests/phl/fail         \
	  --ko-dir=tests/prhl/fail       

THTESTS = --ok-dir=theories

CHECK = \
	./scripts/runtest.py              \
	  --bin=./ec.native               \
	  --bin-args="$(CHECKARGS)"       

CHECKLIBS = \
	./scripts/runtest.py           \
	  --bin=./ec.native            \
	  --bin-args="$(CHECKLIBARGS)" \
	  --ok-dir=theories/prelude    \
	  --extra-args="-boot"         \
	  --ok-dir=theories            \
	  --xunit=libresults.xml

# --------------------------------------------------------------------
.PHONY: all build byte native check check-xunit tags
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

uninstall:
	rm -f $(DESTDIR)$(PREFIX)/bin/easycrypt
	rm -f $(patsubst %,$(DESTDIR)$(PREFIX)/lib/easycrypt/%,$(THEORIES))
	-@rmdir $(DESTDIR)$(PREFIX)/lib/easycrypt/theories
	-@rmdir $(DESTDIR)$(PREFIX)/lib/easycrypt

tests: ec.native
	$(CHECK) $(OKTESTS) $(KOTESTS)

check: ec.native
	$(CHECK) $(THTESTS) $(OKTESTS) $(KOTESTS)

checklibs: ec.native
	$(CHECKLIBS)

check-xunit: ec.native
	$(CHECK) $(THTESTS) $(OKTESTS) $(KOTESTS) --xunit="$(XUNITOUT)"

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
