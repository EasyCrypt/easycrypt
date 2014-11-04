# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all clean __force__

LATEXMK = latexmk -bibtex -output-directory=_build\
                  -synctex=1 -file-line-error

all: easycrypt.pdf

%.pdf: __force__
	TEXINPUTS=${TEXINPUTS}:../common \
	  $(LATEXMK) -pdf $(@:%.pdf=%) && ln -sf _build/$@ .

clean:
	rm -rf _build/ easycrypt.pdf
