# -*- Makefile -*-

# --------------------------------------------------------------------
DUNE      ?= dune
ECARGS    ?=
ECTOUT    ?= 10
ECJOBS    ?= 0
ECEXTRA   ?= --report=report.log
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/testing/runtest
CHECK     += --bin=./ec.native
CHECK     += --jobs="$(ECJOBS)"
CHECK     += --bin-args=-timeout --bin-args="$(ECTOUT)"
CHECK     += $(foreach arg,$(ECARGS),--bin-args="$(arg)")
CHECK     += $(ECEXTRA) config/tests.config
NIX       ?= nix --extra-experimental-features "nix-command flakes"
PROFILE   ?= dev

# --------------------------------------------------------------------
UNAME_P = $(shell uname -p)
UNAME_S = $(shell uname -s)

# --------------------------------------------------------------------
.PHONY: default build byte native tests check examples
.PHONY: nix-build nix-build-with-provers nix-develop
.PHONY: clean install uninstall

default: build
	@true

build:
	rm -f src/ec.exe ec.native
	$(DUNE) build --profile=$(PROFILE)
	ln -sf src/ec.exe ec.native
ifeq ($(UNAME_P)-$(UNAME_S),arm-Darwin)
	-codesign -f -s - src/ec.exe
endif

install: build
	$(DUNE) install

uninstall:
	$(DUNE) uninstall

unit: build
	$(CHECK) unit

stdlib: build
	$(CHECK) prelude stdlib

examples: build
	$(CHECK) examples mee-cbc

check: unit stdlib examples
	@true

nix-build:
	$(NIX) build

nix-build-with-provers:
	$(NIX) build .#with_provers

nix-develop:
	$(NIX) develop

clean:
	rm -f ec.native && $(DUNE) clean
	find theories examples -name '*.eco' -exec rm '{}' ';'

clean_eco:
	find theories examples -name '*.eco' -exec rm '{}' ';'
