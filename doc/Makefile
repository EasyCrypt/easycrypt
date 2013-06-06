TEX=pdflatex
IDX=makeindex
BIB=bibtex
MAIN=easycrypt

FILES= *.tex
BBLFILE= $(MAIN).bbl
IDXFILES= easycrypt.idx ambient.idx hoare.idx phl.idx prhl.idx
INDFILES= $(IDXFILES:.idx=.ind)

PDF= $(MAIN).pdf

all: final

$(MAIN).pdf $(MAIN).aux $(IDXFILES): $(MAIN).tex
	$(TEX) $^

index: $(INDFILES)

%.ind: %.idx
	$(IDX) $<

%.bbl: %.aux
	$(BIB) $<

final: $(FILES) $(INDFILES) $(BBLFILE)
	$(TEX) $(MAIN).tex

clean:
	rm -f *.aux *.out *.blg *.bbl *.log *.dvi *.toc *.idx *.ilg *.ind *.lof $(MAIN).pdf *~
