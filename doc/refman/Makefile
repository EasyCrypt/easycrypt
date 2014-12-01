# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all clean __force__

LATEXMK := latexmk -bibtex -output-directory=_build
LATEXMK += -synctex=1
EXTRAMK ?=
LINKS   := pdf log synctex.gz
MAIN    := easycrypt

ifneq (${DRAFT},)
LATEXMK += -e '$$max_repeat = 1' -interaction=errorstopmode
else
LATEXMK += -interaction=batchmode
endif

LATEXMK += $(EXTRAMK)

# --------------------------------------------------------------------
all: $(MAIN).pdf

%.pdf: __force__
	TEXINPUTS=${TEXINPUTS}:../common $(LATEXMK) -pdf $(@:%.pdf=%)
	for i in $(LINKS); do ln -sf _build/$*.$$i .; done

clean:
	rm -rf _build/ $(LINKS:%=$(MAIN).%)
