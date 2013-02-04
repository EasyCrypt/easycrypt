# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all install uninstall

PGROOT ?= /usr/share/emacs/site-lisp/ProofGeneral

all:
	@echo "Type '$(MAKE) install' for installing ec-mode"

install: $(PGROOT)
	@if [ -d $(PGROOT)/easycrypt ]; then \
	  echo "This PG version has already been patched" >&2; \
	  exit 1; \
	fi
	( cd $(PGROOT)/generic && patch -p0 -t ) < proof-site.patch
	install -d $(PGROOT)/easycrypt
	install -t $(PGROOT)/easycrypt easycrypt/*.el

uninstall: $(PGROOT)/easycrypt
	( cd $(PGROOT)/generic && patch -p0 -tR ) < proof-site.patch
	rm -rf $(PGROOT)/easycrypt
