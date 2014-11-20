# -*- Makefile -*-

# --------------------------------------------------------------------
OPAM ?= 4.01.0
DEST ?= easycrypt
TAG  ?= $(shell date +"%Y-%m-%d")

# --------------------------------------------------------------------
.PHONY: default base posix linux-32 linux-64 macos win32 publish
.PHONY: export export-linux-32 export-linux-64 export-macos
.PHONY: build-linux-32 build-linux-64 build-macos

# --------------------------------------------------------------------
default:
	@echo "make [linux-32|linux-64|macos]"

# --------------------------------------------------------------------
base:
	rm -rf $(DEST) && mkdir $(DEST)
	rsync -avt package/ $(DEST)/
	make -C ../.. DESTDIR=ide/emacs-based/$(DEST) PREFIX=/ install

# --------------------------------------------------------------------
posix: base
	rsync -avt ../../_tools/ocaml-$(OPAM)/opam/system/lib/why3/lib/   $(DEST)/lib/
	rsync -avt ../../_tools/ocaml-$(OPAM)/opam/system/lib/why3/share/ $(DEST)/share/
	mv $(DEST)/lib/why3/why3-cpulimit $(DEST)/bin/

# --------------------------------------------------------------------
linux-32: posix
	rsync -avt provers/linux-x86/ $(DEST)/
	tar --owner=0 --group=0 -czf easycrypt-$(TAG)-x86.tar.gz easycrypt

# --------------------------------------------------------------------
linux-64: posix
	rsync -avt provers/linux-x64/ $(DEST)/
	tar --owner=0 --group=0 -czf easycrypt-$(TAG)-x64.tar.gz easycrypt

# --------------------------------------------------------------------
macos: posix
	rsync -avt extra/macos/ $(DEST)/share/
	rsync -avt provers/macos/ $(DEST)/
	/usr/local/bin/gtar --owner=0 --group=0 -czf easycrypt-$(TAG)-macos.tar.gz easycrypt

# --------------------------------------------------------------------
win32: base
	rsync -avt /opt/wodi32/lib/why3   $(DEST)/lib/
	rsync -avt /opt/wodi32/share/why3 $(DEST)/share/
	mv $(DEST)/lib/why3/why3-cpulimit.exe $(DEST)/bin/
	cp $(DEST)/etc/why3-win32.conf $(DEST)/etc/why3.conf
	rsync -avt extra/win32/ $(DEST)/share/
	rsync -avt provers/win32/ $(DEST)/
	zip -r easycrypt-$(TAG)-win32.zip easycrypt/

# --------------------------------------------------------------------
export:
	if [ ! -z "${ECHOST}" ]; then \
	  rsync -avtRa --rsh=ssh --delete \
	    extra provers package/share/easycrypt/pg/ProofGeneral \
	    ${ECHOST}; \
	fi

# --------------------------------------------------------------------
export-linux-32:
	$(MAKE) export ECHOST="debian-32.local:easycrypt/ide/emacs-based"

# --------------------------------------------------------------------
export-linux-64:
	$(MAKE) export ECHOST="debian-64.local:easycrypt/ide/emacs-based"

# --------------------------------------------------------------------
export-macos:
	$(MAKE) export ECHOST="macos.local:easycrypt/ide/emacs-based"

# --------------------------------------------------------------------
build-linux-32: export-linux-32
	ssh -A debian-32.local 'set -e; cd easycrypt; \
	  source ./scripts/activate-toolchain.sh; \
	  make clean; git pull --rebase; make; \
	  make TAG=$(TAG) -C ide/emacs-based linux-32'
	scp debian-32.local:easycrypt/ide/emacs-based/easycrypt-$(TAG)-x86.tar.gz .

# --------------------------------------------------------------------
build-linux-64: export-linux-64
	ssh -A debian-64.local 'set -e; cd easycrypt; \
	  source ./scripts/activate-toolchain.sh; \
	  make clean; git pull --rebase; make; \
	  make TAG=$(TAG) -C ide/emacs-based linux-64'
	scp debian-64.local:easycrypt/ide/emacs-based/easycrypt-$(TAG)-x64.tar.gz .

# --------------------------------------------------------------------
build-macos: export-macos
	ssh -A macos.local 'set -e; cd easycrypt; \
	  source ./scripts/activate-toolchain.sh; \
	  make clean; git pull --rebase; make; \
	  make TAG=$(TAG) -C ide/emacs-based macos'
	scp macos.local:easycrypt/ide/emacs-based/easycrypt-$(TAG)-macos.tar.gz .

# --------------------------------------------------------------------
publish:
	curl --user "$(USER)" --digest -T "easycrypt-$(TAG)-{x86,x64,macos}.tar.gz" \
	  https://www.easycrypt.info/binaries/

# --------------------------------------------------------------------
clean:
	rm -rf $(DEST)
