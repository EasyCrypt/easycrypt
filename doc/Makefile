TEX=pdflatex
IDX=makeindex
MAIN=easycrypt

FILES= *.tex

PDF= $(MAIN).pdf

all: $(PDF) 

$(PDF): $(FILES)
	pdflatex $(MAIN).tex 

clean:
	rm -f *.aux *.out *.blg *.bbl *.log *.dvi *.toc *.idx *.ilg *.ind *.lof $(MAIN).pdf *~

scratch:
	$(TEX) $(MAIN)
	$(IDX) $(MAIN)
	$(TEX) $(MAIN)
	$(TEX) $(MAIN)
