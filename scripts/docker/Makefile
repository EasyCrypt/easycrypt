#! -*- Makefile -*-

# --------------------------------------------------------------------
VARIANT ?= build
TAG     ?= main

# --------------------------------------------------------------------
.PHONY: default build publish

default: build

build:
	docker build -f Dockerfile.$(VARIANT) \
	  --platform linux/amd64 \
	  -t ghcr.io/easycrypt/ec-$(VARIANT)-box:$(TAG) \
	  .

publish:
	docker push ghcr.io/easycrypt/ec-$(VARIANT)-box:$(TAG)
