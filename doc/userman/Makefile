# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all clean __force__

LATEXMK = latexmk -bibtex -output-directory=_build

all: easycrypt.pdf

%.pdf: __force__
	$(LATEXMK) -pdf $(@:%.pdf=%) && ln -sf _build/$@ .

clean:
	rm -rf _build/ easycrypt.pdf
