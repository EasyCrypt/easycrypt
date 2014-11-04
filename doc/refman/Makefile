# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all clean __force__

LATEXMK := latexmk -bibtex -output-directory=_build
LATEXMK += -synctex=1 -file-line-error -interaction=nonstopmode
LINKS   := pdf log synctex.gz
MAIN    := easycrypt

all: $(MAIN).pdf

%.pdf: __force__
	TEXINPUTS=${TEXINPUTS}:../common $(LATEXMK) -pdf $(@:%.pdf=%)
	for i in $(LINKS); do ln -sf _build/$*.$$i .; done

clean:
	rm -rf _build/ $(LINKS:%=$(MAIN).%)
