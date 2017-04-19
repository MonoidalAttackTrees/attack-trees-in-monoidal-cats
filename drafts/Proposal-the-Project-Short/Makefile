PDFLATEX = pdflatex
BIBTEX = bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta true -picky_multiple_parses false
SKIM = skim_revert.sh

all: pdf
  # This is for my private machine.  It forces my PDF reader to reload.
  # It should not run unless "skim_revert.sh" is in your PATH.
  ifeq ($(SKIM), skim_revert.sh)
	$(SKIM) $(CURDIR)/main.pdf
	$(SKIM) $(CURDIR)/main.pdf
	$(SKIM) $(CURDIR)/main.pdf
  endif

pdf : main.pdf

ll-attack-output.tex : ll-attack.tex ll-attack-ott/ll-attack.ott
	$(OTT) $(OTT_FLAGS) -i ll-attack-ott/ll-attack.ott -o ll-attack-ott.tex -tex_name_prefix LLA \
		-tex_filter ll-attack.tex ll-attack-output.tex

attack-trees-output.tex : attack-trees.tex oll/oll.ott
	$(OTT) $(OTT_FLAGS) -i oll/oll.ott -o oll-ott.tex -tex_name_prefix ATLL \
		-tex_filter attack-trees.tex attack-trees-output.tex

main-output.tex : main.tex atrees.ott
	$(OTT) $(OTT_FLAGS) -i atrees.ott -o atrees-ott.tex -tex_name_prefix ATrees \
		-tex_filter main.tex main-output.tex

# Now this takes the full LaTex translation and compiles it using
# pdflatex.
main.pdf : ll-attack-output.tex main-output.tex appendix-SSG-monoidal.tex ref.bib appendix-SMC.tex Makefile attack-trees-output.tex
	$(PDFLATEX) -jobname=main main-output.tex
	$(BIBTEX) main
	$(PDFLATEX) -jobname=main main-output.tex
	$(PDFLATEX) -jobname=main main-output.tex

clean :
	rm -f *.aux *.dvi *.ps *.log *-ott.tex *-output.tex *.bbl *.blg *.rel *.pdf *~

