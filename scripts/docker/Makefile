# -*- Makefile -*-

# --------------------------------------------------------------------
# docker.com account name
DNAME ?= ghcr.io/easycrypt
BBOX  := build-box test-box

# --------------------------------------------------------------------
.PHONY: all __force__

default:
	@echo "Available images: $(BBOX)"

all:
	for i in $(BBOX); do $(MAKE) $$i-build; done

%-test-box-build:
	[ -d $*-test-box ] || mkdir $*-test-box
	sed -e 's/BRANCH/$*/g' < templates/Dockerfile > $*-test-box/Dockerfile
	cd $*-test-box && docker build -t $(DNAME)/ec-$*-test-box .

%-build: __force__
	cd $* && docker build --platform linux/amd64 -t $(DNAME)/ec-$* .

%-publish: __force__
	cd $* && docker push $(DNAME)/ec-$*:latest
