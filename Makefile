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
REALIZED := $(wildcard theories/realizations/*.ec)
PRELUDE  := $(wildcard theories/prelude/*.ec)
INSTALL  := scripts/install-sh

# --------------------------------------------------------------------
XUNITOUT ?= xunit.xml
ECARGS   ?=
CHECK     = scripts/runtest.py --bin-args="$(ECARGS)" config/tests.config

# --------------------------------------------------------------------
.PHONY: all build byte native tests check check-xunit examples tags
.PHONY: clean install uninstall uninstall-purge dist distcheck why3
.PHONY: callprover pg toolchain update-toolchain provers update
.PHONY: %.ml %.mli %.inferred.mli

all: build

build: callprover native

define do-build
	$(OCAMLBUILD) "$(1)"
endef

byte: tags
	$(call do-build,src/ec.byte)

native: tags
	$(call do-build,src/ec.native)

callprover:
	$(MAKE) -C system

define check-for-staled-files
	if [ -d "$(DESTDIR)$(PREFIX)/lib/easycrypt/" ]; then   \
	  cd "$(DESTDIR)$(PREFIX)/lib/easycrypt/" &&           \
	    find theories -type f -name '*.ec' 2>/dev/null |   \
	    sed 's/^/!! FOUND STALED FILE: /';                 \
	fi
endef

define install-theories
	$(INSTALL) -m 0755 -d $(DESTDIR)$(PREFIX)/lib/easycrypt/theories/$(1)
	$(INSTALL) -m 0644 -t $(DESTDIR)$(PREFIX)/lib/easycrypt/theories/$(1) $(2)
endef

install: ec.native uninstall
	-@$(call check-for-staled-files)
	$(INSTALL) -m 0755 -d $(DESTDIR)$(PREFIX)/bin
	$(INSTALL) -m 0755 -T ec.native $(DESTDIR)$(PREFIX)/bin/easycrypt
	$(call install-theories,,$(THEORIES))
	$(call install-theories,prelude,$(PRELUDE))
	$(call install-theories,realizations,$(REALIZED))

define rmdir
	-	@if [ -d "$(1)" ]; then rmdir "$(1)"; fi
endef

define uninstall-theories
	rm -f $(patsubst %,$(DESTDIR)$(PREFIX)/lib/easycrypt/%,$(2))
	$(call rmdir,$(DESTDIR)$(PREFIX)/lib/easycrypt/theories/$(1))
endef

uninstall:
	rm -f $(DESTDIR)$(PREFIX)/bin/easycrypt
	$(call uninstall-theories,realizations,$(REALIZED))
	$(call uninstall-theories,prelude,$(PRELUDE))
	$(call uninstall-theories,,$(THEORIES))
	$(call rmdir,$(DESTDIR)$(PREFIX)/lib/easycrypt)

uninstall-purge:
	rm  -f $(DESTDIR)$(PREFIX)/bin/easycrypt
	rm -rf $(DESTDIR)$(PREFIX)/lib/easycrypt

tests: check

examples:
	$(CHECK) examples

fullcheck: ec.native
	$(CHECK) prelude theories realized examples unit

check: ec.native
	$(CHECK) prelude theories realized unit

check-xunit: ec.native
	$(CHECK) --xunit="$(XUNITOUT)" prelude theories realized unit

checklibs: ec.native
	$(CHECK) --xunit=libresults.xml prelude theories realized

clean:
	$(OCAMLBUILD) -clean
	rm -f ec.native ec.byte
	$(MAKE) -C system clean
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
	if [ -d _tools ]; then $$(./scripts/activate-toolchain.sh); fi; \
	  $(MAKE) -C proofgeneral run-local

# --------------------------------------------------------------------
TOOLCHAIN_URL := http://ci.easycrypt.info/scripts/ec-build-toolchain

toolchain:
	export OPAMVERBOSE=1; bash ./scripts/ec-build-toolchain

update-toolchain:
	export OPAMVERBOSE=1; $$(./scripts/activate-toolchain.sh) \
	  && opam update  -y \
	  && opam remove  -y ec-toolchain \
	  && opam install -y ec-toolchain

provers:
	export OPAMVERBOSE=1; $$(./scripts/activate-toolchain.sh) \
	  && opam update  -y \
	  && opam remove  -y ec-provers \
	  && opam install -y ec-provers \
	  && rm -f _tools/why3.local.conf \
	  && why3config --detect -C _tools/why3.local.conf

update:
	git pull
	make clean && make
