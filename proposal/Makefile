PDFLATEX=pdflatex
SKIM = skim_revert.sh

all : pdf

pdf : proposal.pdf
	$(SKIM) $(CURDIR)/proposal.pdf

refs : refs.pdf
	$(SKIM) $(CURDIR)/references.pdf

proposal.pdf : proposal.tex proposal-src.tex Makefile refs.bib
	$(PDFLATEX) proposal.tex
	bibtex proposal
	$(PDFLATEX) proposal.tex
	$(PDFLATEX) proposal.tex
	$(PDFLATEX) proposal.tex

refs.pdf : refs.tex proposal-src.tex Makefile
	$(PDFLATEX) -jobname references refs.tex
	bibtex references
	$(PDFLATEX) -jobname references refs.tex
	$(PDFLATEX) -jobname references refs.tex
	$(PDFLATEX) -jobname references refs.tex

clean : 
	rm -f *.aux *.dvi *.ps *.log *~ *.out *.bbl *.rel *.blg
