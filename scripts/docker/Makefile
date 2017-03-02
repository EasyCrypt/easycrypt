# -*- Makefile -*-

# --------------------------------------------------------------------
# docker.com account name
DNAME ?= strubpy
BBOX  := build-box doc-box test-box aprhl-test-box

# --------------------------------------------------------------------
.PHONY: all __force__

default:
	@echo "Available images: $(BBOX)"

all:
	for i in $(BBOX); do $(MAKE) $$i-build; done

%-build: __force__
	cd $* && docker build -t $(DNAME)/ec-$* .

%-publish: __force__
	cd $* && docker push $(DNAME)/ec-$*:latest
