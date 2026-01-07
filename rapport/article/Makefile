MAIN=main

all: pdf

pdf:
	pdflatex $(MAIN).tex
	bibtex $(MAIN) || true
	pdflatex $(MAIN).tex
	pdflatex $(MAIN).tex

clean:
	rm -f *.aux *.log *.toc *.out *.bbl *.blg *.lof *.lot

mrproper: clean
	rm -f $(MAIN).pdf

