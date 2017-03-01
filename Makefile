# -*- Makefile -*-

# --------------------------------------------------------------------
OCAMLBUILD_JOBS  ?= 1
OCAMLBUILD_BIN   ?= ocamlbuild
OCAMLBUILD_EXTRA ?= 
OCAMLBUILD_OPTS  := -use-ocamlfind -j $(OCAMLBUILD_JOBS)


# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_OPTS += -classic-display
endif
ifeq ($(LINT),1)
 OCAMLBUILD_OPTS += -tag lint
endif
OCAMLBUILD_OPTS += $(OCAMLBUILD_EXTRA)

OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_OPTS)

DESTDIR    ?=
PREFIX     ?= /usr/local
VERSION    ?= $(shell date '+%F')
DISTDIR    := easycrypt-$(VERSION)
INSTALL    := scripts/install/install-sh
PWD        := $(shell pwd)
COMMIT     := $(shell scripts/install/get-commit)
FVERSION   := src/ecVersion.ml

include Makefile.system

# --------------------------------------------------------------------
BINDIR := $(PREFIX)/bin
LIBDIR := $(PREFIX)/lib/easycrypt
SHRDIR := $(PREFIX)/share/easycrypt
SYSDIR := $(LIBDIR)/system

# --------------------------------------------------------------------
XUNITOUT  ?= xunit.xml
ECARGS    ?=
ECTOUT    ?= 5
ECJOBS    ?= 1
ECEXTRA   ?= --pretty
ECPROVERS ?= Alt-Ergo Z3 Eprover
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/testing/runtest
CHECK     += --bin-args="$(ECARGS)" --bin-args="$(ECPROVERS:%=-p %)"
CHECK     += --timeout="$(ECTOUT)" --jobs="$(ECJOBS)"
CHECK     += $(ECEXTRA) config/tests.config
CHECKCATS ?= prelude stdlib

# --------------------------------------------------------------------
.PHONY: all build byte native tests check weak-check check-xunit examples
.PHONY: clean install uninstall uninstall-purge dist distcheck
.PHONY: callprover license
.PHONY: %.ml %.mli %.inferred.mli

all: build
	@true

build: callprover native

define do-core-build
	$(OCAMLBUILD) "$(1)"
endef

define do-build
	rm -f "$(1)$(EXE)"
	sed 's/COMMIT/$(COMMIT)/g' < $(FVERSION).in > $(FVERSION)
  $(call do-core-build,src/$(1))
	if [ ! -z "$(EXE)" ]; then \
	  cp "_build/src/$(1)" "$(1)$(EXE)"; \
	fi
endef

byte:
	$(call do-build,ec.byte)

native:
	$(call do-build,ec.native)

callprover:
	$(MAKE) -C system

define check-for-staled-files
	if [ -d "$(DESTDIR)$(PREFIX)/lib/easycrypt/" ]; then   \
	  cd "$(DESTDIR)$(LIBDIR)/" &&           \
	    find theories -type f -name '*.ec*' 2>/dev/null |   \
	    sed 's/^/!! FOUND STALED FILE: /';                 \
	fi
endef

install: ec.native uninstall
	-@$(call check-for-staled-files)
	$(INSTALL) -m 0755 -d $(DESTDIR)$(BINDIR)
	$(INSTALL) -m 0755 -T ec.native $(DESTDIR)$(BINDIR)/easycrypt$(EXE)
	$(INSTALL) -m 0755 -d $(DESTDIR)$(SYSDIR)
	$(INSTALL) -m 0755 -T system/callprover$(EXE) $(DESTDIR)$(SYSDIR)/callprover$(EXE)
	for i in $$(find theories -type d); do \
	  $(INSTALL) -m 0755 -d $(DESTDIR)$(LIBDIR)/$$i ';'; \
	  $(INSTALL) -m 0644 -t $(DESTDIR)$(LIBDIR)/$$i $$i/*.ec*; \
	done

define rmdir
	-@if [ -d "$(1)" ]; then rmdir "$(1)"; fi
endef

uninstall:
	rm -f $(DESTDIR)$(BINDIR)/easycrypt
	rm -f $(DESTDIR)$(SYSDIR)/callprover
	$(call rmdir,$(DESTDIR)$(SYSDIR))
	for i in $$(find theories -depth -type d); do \
	  for j in $$i/*.ec*; do rm -f $(DESTDIR)$(LIBDIR)/$$j; done; \
	  rmdir $(DESTDIR)$(LIBDIR)/$$i 2>/dev/null || true; \
	done
	rm -f $(DESTDIR)$(SHRDIR)/emacs/*.el
	$(call rmdir,$(DESTDIR)$(SHRDIR)/emacs)
	$(call rmdir,$(DESTDIR)$(SHRDIR))

uninstall-purge:
	rm  -f $(DESTDIR)$(BINDIR)/easycrypt
	rm -rf $(DESTDIR)$(LIBDIR)
	rm -rf $(DESTDIR)$(SHRDIR)

tests: check

examples:
	$(CHECK) examples

check: ec.native
	$(CHECK) $(CHECKCATS)

weak-check: ec.native
	$(CHECK) --bin-args="-pragmas Proofs:weak" $(CHECKCATS) '!unit'

check-xunit: ec.native
	$(CHECK) --xunit="$(XUNITOUT)" $(CHECKCATS)

license:
	scripts/srctx/license COPYRIGHT.yaml \
	  $(shell find src -name '*.ml' -o -name '*.ml[a-z]') \
	  $(shell find theories -name '*.ec' -o -name '*.ec[a-z]') \
	  $(shell find proofgeneral/easycrypt -name '*.el')

clean:
	$(OCAMLBUILD) -clean
	rm -f ec.native ec.byte
	rm -f ec.native.exe ec.byte.exe
	$(MAKE) -C system clean

# --------------------------------------------------------------------
dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/install/distribution $(DISTDIR) MANIFEST
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
%.inferred.mli:
	@$(call do-core-build,src/$@) && cat _build/src/$@

# --------------------------------------------------------------------
%.ml:
	$(call do-core-build,src/$*.cmo)

# --------------------------------------------------------------------
%.mli:
	$(call do-core-build,src/$*.cmi)
