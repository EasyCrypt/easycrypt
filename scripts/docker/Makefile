# -*- Makefile -*-

# --------------------------------------------------------------------
# docker.com account name
DNAME ?= easycryptpa
BBOX  := build-box doc-box test-box aprhl-test-box

# --------------------------------------------------------------------
.PHONY: all __force__

default:
	@echo "Available images: $(BBOX)"

all:
	for i in $(BBOX); do $(MAKE) $$i-build; done

%-test-box-build:
	[ -d $*-test-box ] || mkdir $*-test-box
	cp templates/sudo-ci $*-test-box/
	sed -e 's/BRANCH/$*/g' < templates/Dockerfile > $*-test-box/Dockerfile
	cd $*-test-box && docker build -t $(DNAME)/ec-$*-test-box .

%-build: __force__
	cd $* && docker build -t $(DNAME)/ec-$* .

%-publish: __force__
	cd $* && docker push $(DNAME)/ec-$*:latest
