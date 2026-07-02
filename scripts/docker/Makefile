#! -*- Makefile -*-

# --------------------------------------------------------------------
VARIANT ?= build
TAG     ?= main
VERSION ?= $(TAG)
BARGS   += --build-arg EC_VERSION=$(VERSION)

# --------------------------------------------------------------------
.PHONY: default build publish

default: build

build:
	docker build --target $(VARIANT) \
	  --platform linux/amd64 \
	  $(BARGS) \
	  -t ghcr.io/easycrypt/ec-$(VARIANT)-box:$(TAG) \
	  .

publish:
	docker push ghcr.io/easycrypt/ec-$(VARIANT)-box:$(TAG)
