# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all %.pdf clean

LATEXMK = latexmk -bibtex -output-directory=_build

all: easycrypt.pdf

%.pdf:
	$(LATEXMK) -pdf $(@:%.pdf=%) && ln -sf _build/$@ .

clean:
	rm -rf _build/ easycrypt.pdf
