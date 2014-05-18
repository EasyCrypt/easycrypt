# -*- Makefile -*-

# --------------------------------------------------------------------
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
CORE     := $(wildcard theories/core/*.ec)
INSTALL  := scripts/install-sh

# --------------------------------------------------------------------
BINDIR := $(PREFIX)/bin
LIBDIR := $(PREFIX)/lib/easycrypt
SYSDIR := $(LIBDIR)/system

# --------------------------------------------------------------------
XUNITOUT ?= xunit.xml
ECARGS   ?=
CHECK     = scripts/runtest.py --bin-args="$(ECARGS)" config/tests.config

# --------------------------------------------------------------------
.PHONY: all build byte native tests check check-xunit examples
.PHONY: clean install uninstall uninstall-purge dist distcheck
.PHONY: callprover pg toolchain update-toolchain provers update
.PHONY: webui webui-start webui-stop webui-env
.PHONY: %.ml %.mli %.inferred.mli

all: build

build: callprover native

define do-build
	$(OCAMLBUILD) "$(1)"
endef

byte:
	$(call do-build,src/ec.byte)

native:
	$(call do-build,src/ec.native)

callprover:
	$(MAKE) -C system

define check-for-staled-files
	if [ -d "$(DESTDIR)$(PREFIX)/lib/easycrypt/" ]; then   \
	  cd "$(DESTDIR)$(LIBDIR)/" &&           \
	    find theories -type f -name '*.ec' 2>/dev/null |   \
	    sed 's/^/!! FOUND STALED FILE: /';                 \
	fi
endef

define install-theories
	$(INSTALL) -m 0755 -d $(DESTDIR)$(LIBDIR)/theories/$(1)
	$(INSTALL) -m 0644 -t $(DESTDIR)$(LIBDIR)/theories/$(1) $(2)
endef

install: ec.native uninstall
	-@$(call check-for-staled-files)
	$(INSTALL) -m 0755 -d $(DESTDIR)$(BINDIR)
	$(INSTALL) -m 0755 -T ec.native $(DESTDIR)$(BINDIR)/easycrypt
	$(INSTALL) -m 0755 -d $(DESTDIR)$(SYSDIR)
	$(INSTALL) -m 0755 -T system/callprover $(DESTDIR)$(SYSDIR)/callprover
	$(call install-theories,,$(THEORIES))
	$(call install-theories,core,$(CORE))
	$(call install-theories,prelude,$(PRELUDE))
	$(call install-theories,realizations,$(REALIZED))

define rmdir
	-@if [ -d "$(1)" ]; then rmdir "$(1)"; fi
endef

define uninstall-theories
	rm -f $(patsubst %,$(DESTDIR)$(LIBDIR)/%,$(2))
	$(call rmdir,$(DESTDIR)$(LIBDIR)/theories/$(1))
endef

uninstall:
	rm -f $(DESTDIR)$(BINDIR)/easycrypt
	rm -f $(DESTDIR)$(SYSDIR)/callprover
	$(call rmdir,$(DESTDIR)$(SYSDIR))
	$(call uninstall-theories,realizations,$(REALIZED))
	$(call uninstall-theories,prelude,$(PRELUDE))
	$(call uninstall-theories,core,$(CORE))
	$(call uninstall-theories,,$(THEORIES))
	$(call rmdir,$(DESTDIR)$(LIBDIR))

uninstall-purge:
	rm  -f $(DESTDIR)$(BINDIR)/easycrypt
	rm -rf $(DESTDIR)$(LIBDIR)

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
webui:
	@python -mwebbrowser 'http://localhost:6543'

webui-start: native
	bash ./scripts/ec-run-webui start

webui-stop:
	bash ./scripts/ec-run-webui stop

# --------------------------------------------------------------------
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

webui-env:
	bash ./scripts/ec-build-webui-env

update:
	git pull
	make clean && make
