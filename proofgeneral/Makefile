# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all install install-soft uninstall local run-local

PGROOT ?= /usr/share/emacs/site-lisp/ProofGeneral
EMACS  ?= $(shell ./scripts/find-emacs)

# --------------------------------------------------------------------
all:
	@echo "Type '$(MAKE) install' for installing ec-mode"

keywords: easycrypt/easycrypt-keywords.el

easycrypt/easycrypt-keywords.el: ../src/ecLexer.mll
	../scripts/keywords.py -m emacs < $< > $@

install: $(PGROOT)
	@if [ -d $(PGROOT)/easycrypt ]; then \
	  echo "This PG version has already been patched" >&2; \
	  exit 1; \
	fi
	( cd $(PGROOT)/generic && patch -p0 -t ) < proof-site.patch
	../scripts/install-sh -m 0755 -d $(PGROOT)/easycrypt
	../scripts/install-sh -m 0644 -t $(PGROOT)/easycrypt easycrypt/*.el

install-soft: $(PGROOT)
	@if [ -d $(PGROOT)/easycrypt ]; then \
	  echo "This PG version has already been patched" >&2; \
	  exit 1; \
	fi
	( cd $(PGROOT)/generic && patch -p0 -t ) < proof-site.patch
	../scripts/install-sh -m 0755 -d $(PGROOT)/easycrypt
	for i in easycrypt/*.el; do ln -s $(CURDIR)/$$i $(PGROOT)/easycrypt; done

uninstall: $(PGROOT)/easycrypt
	( cd $(PGROOT)/generic && patch -p0 -tR ) < proof-site.patch
	rm -rf $(PGROOT)/easycrypt

# --------------------------------------------------------------------
PGVER := 4.2
PGURL := http://proofgeneral.inf.ed.ac.uk/releases/ProofGeneral-$(PGVER).tgz

local:
	rm -rf _local && mkdir _local
	cd _local; \
	     curl -O $(PGURL) \
	  && tar -xof ProofGeneral-$(PGVER).tgz \
	  && if [ -e $(CURDIR)/pg-$(PGVER).patch ]; then \
           (    cd $(CURDIR)/_local/ProofGeneral-$(PGVER) \
             && patch -t -p1 < $(CURDIR)/pg-$(PGVER).patch;  ); \
         fi \
	  || exit 1
	$(MAKE) PGROOT=$(CURDIR)/_local/ProofGeneral-$(PGVER) install-soft
	$(MAKE) EMACS=$(EMACS) -C $(CURDIR)/_local/ProofGeneral-$(PGVER) clean
	$(MAKE) EMACS=$(EMACS) -C $(CURDIR)/_local/ProofGeneral-$(PGVER)
	sed -e s/@VERSION@/$(PGVER)/g config/emacs.rc.in > \
	  $(CURDIR)/_local/emacs.rc

run-local:
	$(EMACS) \
	  --execute '(load-file "_local/emacs.rc")' \
	  --execute '(load-file "$(CURDIR)/emacs.local.rc")' \
	  --execute '(cd "$(CURDIR)/..")' \
	  --no-init-file
