# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all easycrypt.pdf clean

LATEXMK = latexmk -bibtex -e '$$clean_ext = "brf";'

all: easycrypt.pdf

easycrypt.pdf:
	$(LATEXMK) -pdf easycrypt

clean:
	$(LATEXMK) -c easycrypt
	rm -f easycrypt.pdf
