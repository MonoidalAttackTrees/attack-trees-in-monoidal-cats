PDFLATEX = pdflatex
BIBTEX = bibtex
OTT = ott
OTT_FLAGS := -tex_show_meta false
SKIM := skim_revert.sh
SKIMRevinPath := $(shell command -v $(SKIM) 2> /dev/null)

all: pdf
  # This is for my private machine.  It forces my PDF reader to reload.
  # It should not run unless "skim_revert.sh" is in your PATH.
  ifdef SKIMRevinPath	
	@$(SKIM) type-level-Lina.pdf &>/dev/null
	@$(SKIM) type-level-Lina.pdf &>/dev/null
	@$(SKIM) type-level-Lina.pdf &>/dev/null
  endif

pdf : type-level-Lina.pdf

type-level-Lina.tex : type-level-Lina.ott
	$(OTT) $(OTT_FLAGS) -i type-level-Lina.ott -o type-level-Lina.tex

type-level-Lina.pdf : type-level-Lina.tex Makefile
	$(PDFLATEX) type-level-Lina.tex

clean :
	rm -f *.aux *.dvi *.ps *.log *-ott.tex *-output.tex *.bbl *.blg *.rel *.pdf *~ *.vtc *.out *.spl *-inc.tex
