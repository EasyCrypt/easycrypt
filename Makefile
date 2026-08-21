# -*- Makefile -*-

# --------------------------------------------------------------------
DUNE      ?= dune
ECARGS    ?=
ECJOBS    ?= 0
ECEXTRA   ?= --report=report.log
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/testing/runtest
CHECK     += --bin=./ec.native
CHECK     += --jobs="$(ECJOBS)"
CHECK     += $(foreach arg,$(ECARGS),--bin-args="$(arg)")
CHECK     += $(ECEXTRA) config/tests.config
LLMCHECK  := scripts/testing/llm-golden
LLMCHECK  += --bin=./ec.native
MCPCHECK  := scripts/testing/mcp-golden
MCPCHECK  += --bin=./ec.native
MCPPARITY := scripts/testing/mcp-parity
MCPPARITY += --bin=./ec.native
NIX       ?= nix --extra-experimental-features "nix-command flakes"
PROFILE   ?= dev

# --------------------------------------------------------------------
UNAME_P = $(shell uname -p)
UNAME_S = $(shell uname -s)

# --------------------------------------------------------------------
.PHONY: default build byte native tests check examples
.PHONY: test-llm test-mcp
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

test-llm: build
	$(LLMCHECK)

test-mcp: build
	$(MCPCHECK)
	$(MCPPARITY)

check: unit stdlib examples test-llm test-mcp
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
