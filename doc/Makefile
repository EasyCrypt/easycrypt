# -*- Makefile -*-

# ------------------------------------------------------------------------
SPHINXBUILD ?= sphinx-build
SPHINXOPTS  ?=
SOURCEDIR    = .
BUILDDIR     = _build
NPM         ?= npm

# ------------------------------------------------------------------------
.PHONY:

default:
	@echo "make [ecproof-deps | ecproof-bundle| sphinx-html]" >&2

# ------------------------------------------------------------------------
.PHONY: sphinx-help sphinx-deps __force__

sphinx-help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(SPHINXOPTS)

sphinx-deps:
	pip install -r requirements.txt

sphinx-%: __force__
	@$(SPHINXBUILD) -M $* "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(SPHINXOPTS)

# ------------------------------------------------------------------------
.PHONY: ecproof-deps ecproof-bundle

ECPROOFDIR = extensions/ecproofs/proofnav

ecproof-deps:
	$(NPM) --prefix="$(ECPROOFDIR)" install

ecproof-bundle:
	$(NPM) --prefix="$(ECPROOFDIR)" run build

# ------------------------------------------------------------------------
clean:
	rm -rf _build
	rm -rf "$(ECPROOFDIR)"/dist

mrproper: clean
	rm -rf "$(ECPROOFDIR)"/node_modules
