# -*- Makefile -*-

# --------------------------------------------------------------------
DUNE      ?= dune
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

# --------------------------------------------------------------------
.PHONY: default build byte native tests check examples
.PHONY: clean install uninstall

default: build
	@true

build:
	rm -f ec.native && $(DUNE) build && ln -sf src/ec.exe ec.native

install: build
	dune install

uninstall:
	dune uninstall

check: stdlib examples

stdlib: build
	$(CHECK) prelude stdlib

examples: build
	$(CHECK) examples mee-cbc

check: stdlib examples
	@true

clean:
	rm -f ec.native && dune clean
	find theories examples -name '*.eco' -exec rm '{}' ';'

clean_eco:
	find theories examples -name '*.eco' -exec rm '{}' ';'
