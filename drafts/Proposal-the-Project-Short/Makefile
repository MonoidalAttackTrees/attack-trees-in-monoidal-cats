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

indexed-atll-output.tex : indexed-atll.tex indexed-atll/indexed-atll.ott
	$(OTT) $(OTT_FLAGS) -i indexed-atll/indexed-atll.ott -o indexed-atll-ott.tex -tex_name_prefix IATLL \
		-tex_filter indexed-atll.tex indexed-atll-output.tex

full-indexed-atll-output.tex : full-indexed-atll.tex indexed-atll/indexed-atll.ott
	$(OTT) $(OTT_FLAGS) -i indexed-atll/indexed-atll.ott -o indexed-atll-ott.tex -tex_name_prefix IATLL \
		-tex_filter full-indexed-atll.tex full-indexed-atll-output.tex

attack-trees-output.tex : attack-trees.tex atll/atll.ott
	$(OTT) $(OTT_FLAGS) -i atll/atll.ott -o atll-ott.tex -tex_name_prefix ATLL \
		-tex_filter attack-trees.tex attack-trees-output.tex

oll-output.tex : oll.tex oll/oll.ott
	$(OTT) $(OTT_FLAGS) -i oll/oll.ott -o oll-ott.tex -tex_name_prefix OLL \
		-tex_filter oll.tex oll-output.tex

main-output.tex : main.tex atll/atll.ott
	$(OTT) $(OTT_FLAGS) -i atll/atll.ott -o atll-ott.tex -tex_name_prefix ATLL \
		-tex_filter main.tex main-output.tex

main.pdf : indexed-atll-output.tex main-output.tex appendix-SSG-monoidal.tex ref.bib appendix-SMC.tex Makefile attack-trees-output.tex full-indexed-atll-output.tex oll-output.tex
	$(PDFLATEX) -jobname=main main-output.tex
	$(BIBTEX) main
	$(PDFLATEX) -jobname=main main-output.tex
	$(PDFLATEX) -jobname=main main-output.tex

clean :
	rm -f *.aux *.dvi *.ps *.log *-ott.tex *-output.tex *.bbl *.blg *.rel *.pdf *~

