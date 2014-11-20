# -*- Makefile -*-

# --------------------------------------------------------------------
OPAM ?= 4.01.0
DEST ?= easycrypt

# --------------------------------------------------------------------
.PHONY: default posix linux-32 linux-64 macos

# --------------------------------------------------------------------
default:
	@echo "make [linux-32|linux-64|macos]"

# --------------------------------------------------------------------
posix:
	rm -rf $(DEST) && mkdir $(DEST)
	rsync -avt package/ $(DEST)/
	make -C ../.. DESTDIR=ide/emacs-based/$(DEST) PREFIX=/ install
	rsync -avt ../../_tools/ocaml-$(OPAM)/opam/system/lib/why3/lib/   $(DEST)/lib/
	rsync -avt ../../_tools/ocaml-$(OPAM)/opam/system/lib/why3/share/ $(DEST)/share/
	mv $(DEST)/lib/why3/why3-cpulimit $(DEST)/bin/

# --------------------------------------------------------------------
linux-32: posix
	rsync -avt provers/linux-x86/ $(DEST)/

# --------------------------------------------------------------------
linux-64: posix
	rsync -avt provers/linux-x64/ $(DEST)/

# --------------------------------------------------------------------
macos: linux
	rsync -avt extra/macos/ $(DEST)/share/

# --------------------------------------------------------------------
clean:
	rm -rf $(DEST)
