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
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/testing/runtest
CHECK     += --bin-args="$(ECARGS)" --timeout="$(ECTOUT)" --jobs="$(ECJOBS)"
CHECK     += config/tests.config
CHECKCATS ?= prelude core theories encryption newth realized

# --------------------------------------------------------------------
.PHONY: all build byte native tests check weak-check check-xunit examples
.PHONY: clean install uninstall uninstall-purge dist distcheck
.PHONY: callprover pg toolchain update-toolchain provers license
.PHONY: %.ml %.mli %.inferred.mli

all: build
	@true

build: callprover native

define do-build
	rm -f "$(1)$(EXE)"
	$(OCAMLBUILD) "src/$(1)"
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
	$(INSTALL) -m 0755 -d $(DESTDIR)$(SHRDIR)
	$(INSTALL) -m 0755 -d $(DESTDIR)$(SHRDIR)/emacs
	$(INSTALL) -m 0644 -t $(DESTDIR)$(SHRDIR)/emacs proofgeneral/easycrypt/*.el

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
	  src/*.ml src/*/*.ml* theories/*.ec theories/*/*.ec

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
	@if [ "$$EC_TOOLCHAIN_ACTIVATED" = "" -a -d _tools ]; then \
	  EC_SRC_ROOT="$(PWD)/scripts" \
	    . ./scripts/activate-toolchain.sh 2>/dev/null; \
	  if [ "$$EC_TOOLCHAIN_ACTIVATED" = "" ]; then \
	    echo "Toolchain activation failed" >&2; \
	  fi; \
	fi; $(MAKE) -C proofgeneral run-local

# --------------------------------------------------------------------
toolchain:
	export OPAMVERBOSE=1; bash ./scripts/toolchain/ec-build-toolchain

update-toolchain:
	@[ "$$EC_TOOLCHAIN_ACTIVATED" != "" ] || { \
	  echo "Activate the EasyCrypt toolchain first" >&2; false; \
	}
	export OPAMVERBOSE=1; \
             opam update  -y \
	  && opam remove  -y ec-toolchain \
	  && opam install -y ec-toolchain

provers:
	@[ "$$EC_TOOLCHAIN_ACTIVATED" != "" ] || { \
	  echo "Activate the EasyCrypt toolchain first" >&2; false; \
	}
	export OPAMVERBOSE=1; \
	     opam update  -y \
	  && opam remove  -y ec-provers \
	  && opam install -y ec-provers \
	  && rm -f _tools/why3.local.conf \
	  && why3 config --detect -C _tools/why3.local.conf
