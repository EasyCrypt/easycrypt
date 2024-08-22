#! -*- Makefile -*-

# --------------------------------------------------------------------
VARIANT ?= build

# --------------------------------------------------------------------
.PHONY: default build publish

default: build

build:
	docker build -f Dockerfile.$(VARIANT) \
	  --platform linux/amd64 \
	  -t ghcr.io/easycrypt/ec-$(VARIANT)-box \
	  .

publish:
	docker push ghcr.io/easycrypt/ec-$(VARIANT)-box
