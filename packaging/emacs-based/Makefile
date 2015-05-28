# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: default linux macos clean

# --------------------------------------------------------------------
default:
	@echo "make [linux|macos]"

linux:
	scripts/build-linux.sh

macos:
	@echo "not implemented yet" >&2 && false

clean:
	rm -rf _build
