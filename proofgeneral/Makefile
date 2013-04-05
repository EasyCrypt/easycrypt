# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all install uninstall local run-local

PGROOT ?= /usr/share/emacs/site-lisp/ProofGeneral

all:
	@echo "Type '$(MAKE) install' for installing ec-mode"

install: $(PGROOT)
	@if [ -d $(PGROOT)/easycrypt ]; then \
	  echo "This PG version has already been patched" >&2; \
	  exit 1; \
	fi
	( cd $(PGROOT)/generic && patch -p0 -t ) < proof-site.patch
	../scripts/install-sh -m 0755 -d $(PGROOT)/easycrypt
	../scripts/install-sh -m 0644 -t $(PGROOT)/easycrypt easycrypt/*.el

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
	  || exit 1
	$(MAKE) PGROOT=$(CURDIR)/_local/ProofGeneral-$(PGVER) install
	$(MAKE) -C $(CURDIR)/_local/ProofGeneral-$(PGVER) clean
	$(MAKE) -C $(CURDIR)/_local/ProofGeneral-$(PGVER)
	sed -e s/@VERSION@/$(PGVER)/g config/emacs.rc.in > \
	  $(CURDIR)/_local/emacs.rc

run-local:
	emacs -q \
	  --execute '(load-file "_local/emacs.rc")' \
	  --execute '(cd "$(CURDIR)/..")' \
	  --execute '(setq easycrypt-prog-name "$(CURDIR)/../ec.native -emacs")'
