# -*- Makefile -*-

# --------------------------------------------------------------------
DUNE       ?= dune
DESTDIR    ?=
PREFIX     ?= /usr/local
VERSION    ?= $(shell date '+%F')
DISTDIR    := easycrypt-$(VERSION)
INSTALL    := scripts/install/install-sh
PWD        := $(shell pwd)

# --------------------------------------------------------------------
BINDIR := $(PREFIX)/bin
LIBDIR := $(PREFIX)/lib/easycrypt
SHRDIR := $(PREFIX)/share/easycrypt

# --------------------------------------------------------------------
ECARGS    ?=
ECTOUT    ?= 10
ECJOBS    ?= 1
ECEXTRA   ?= --report=report.log
ECPROVERS ?= Alt-Ergo Z3 CVC4
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/testing/runtest
CHECK     += --bin-args="$(ECARGS)" --bin-args="$(ECPROVERS:%=-p %)"
CHECK     += --timeout="$(ECTOUT)" --jobs="$(ECJOBS)"
CHECK     += $(ECEXTRA) config/tests.config
CHECKCATS ?= prelude stdlib

# --------------------------------------------------------------------
.PHONY: default build byte native tests check weak-check examples
.PHONY: clean install uninstall uninstall-purge license

default: build
	@true

build:
	rm -f ec.native && $(DUNE) build && ln -sf src/ec.exe ec.native

define check-for-staled-files
	if [ -d "$(DESTDIR)$(PREFIX)/lib/easycrypt/" ]; then   \
	  cd "$(DESTDIR)$(LIBDIR)/" &&           \
	    find theories -type f -name '*.ec*' 2>/dev/null |   \
	    sed 's/^/!! FOUND STALED FILE: /';                 \
	fi
endef

install: build uninstall
	-@$(call check-for-staled-files)
	$(INSTALL) -m 0755 -d $(DESTDIR)$(BINDIR)
	$(INSTALL) -m 0755 -T src/ec.exe $(DESTDIR)$(BINDIR)/easycrypt
	$(INSTALL) -m 0755 -T scripts/testing/runtest $(DESTDIR)$(BINDIR)/ec-runtest
	for i in $$(find theories -type d -mindepth 1); do \
	  $(INSTALL) -m 0755 -d $(DESTDIR)$(LIBDIR)/$$i ';'; \
	  $(INSTALL) -m 0644 -t $(DESTDIR)$(LIBDIR)/$$i $$i/*.ec*; \
	done

define rmdir
	-@if [ -d "$(1)" ]; then rmdir "$(1)"; fi
endef

uninstall:
	rm -f $(DESTDIR)$(BINDIR)/easycrypt
	rm -f $(DESTDIR)$(BINDIR)/ec-runtest
	for i in $$(find theories -depth -type d); do \
	  for j in $$i/*.ec*; do rm -f $(DESTDIR)$(LIBDIR)/$$j; done; \
	  rmdir $(DESTDIR)$(LIBDIR)/$$i 2>/dev/null || true; \
	done
	$(call rmdir,$(DESTDIR)$(SHRDIR)/emacs)
	$(call rmdir,$(DESTDIR)$(SHRDIR))

uninstall-purge:
	rm  -f $(DESTDIR)$(BINDIR)/easycrypt
	rm -rf $(DESTDIR)$(LIBDIR)
	rm -rf $(DESTDIR)$(SHRDIR)

tests: check

examples: build
	$(CHECK) examples mee-cbc

check: build
	$(CHECK) $(CHECKCATS)

weak-check: build
	$(CHECK) --bin-args="-pragmas Proofs:weak" $(CHECKCATS) '!unit'

license:
	scripts/srctx/license COPYRIGHT.yaml \
	  $(shell find src -name '*.ml' -o -name '*.ml[a-z]') \
	  $(shell find theories -name '*.ec' -o -name '*.ec[a-z]') \
	  $(shell find proofgeneral/easycrypt -name '*.el')

clean:
	rm -f ec.native && dune clean
	find theories examples -name '*.eco' -exec rm '{}' ';'

clean_eco:
	find theories examples -name '*.eco' -exec rm '{}' ';'
