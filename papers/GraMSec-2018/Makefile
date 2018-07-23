PDFLATEX = pdflatex
BIBTEX = bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta true -picky_multiple_parses false
SKIM := skim_revert.sh
SKIMRevinPath := $(shell command -v $(SKIM) 2> /dev/null)

all: pdf
  # This is for my private machine.  It forces my PDF reader to reload.
  # It should not run unless "skim_revert.sh" is in your PATH.
ifdef SKIMRevinPath
	$(SKIM) $(CURDIR)/main.pdf
	$(SKIM) $(CURDIR)/main.pdf
	$(SKIM) $(CURDIR)/main.pdf
endif

pdf : main.pdf

attack-trees-output.tex : attack-trees.tex attack-trees/attack-trees.ott
	$(OTT) $(OTT_FLAGS) -i attack-trees/attack-trees.ott -o aterms-ott.tex -tex_name_prefix ATerms \
		-tex_filter attack-trees.tex attack-trees-output.tex

intro-output.tex : intro.tex atll/atll.ott
	$(OTT) $(OTT_FLAGS) -i atll/atll.ott -o atll-ott.tex -tex_name_prefix ATLL \
		-tex_filter intro.tex intro-output1.tex
	scripts/prepr_double_ott.sh intro-output1.tex
	$(OTT) $(OTT_FLAGS) -i indexed-atll/indexed-atll.ott -o indexed-atll-ott.tex -tex_name_prefix IATLL \
		-tex_filter intro-output1.tex intro-output.tex

quaternary-semantics-output.tex : quaternary-semantics.tex attack-trees/attack-trees.ott
	$(OTT) $(OTT_FLAGS) -i attack-trees/attack-trees.ott -o aterms-ott.tex -tex_name_prefix ATerms \
		-tex_filter quaternary-semantics.tex quaternary-semantics-output.tex

main.pdf : main.tex ref.bib Makefile attack-trees-output.tex intro-output.tex quaternary-semantics-output.tex Lina.tex
	$(PDFLATEX) -shell-escape -jobname=main main.tex
	$(BIBTEX) main
	$(PDFLATEX) -shell-escape -jobname=main main.tex
	$(PDFLATEX) -shell-escape -jobname=main main.tex

TEXFILES = attack-trees-output.tex \
	   intro-output.tex \
	   quaternary-semantics-output.tex \
	   main.tex \
	   ref.bib \
	   llncs.cls \
	   aterms-ott.tex \
	   ATM-Tree1.png \
	   ATM-Tree2.png \
	   mathpartir.sty \
	   Lina.tex

arxiv : $(TEXFILES)
	mkdir -p arxiv
	cp $(TEXFILES) arxiv

clean :
	rm -f *.aux *.dvi *.ps *.log *-ott.tex *-output.tex *.bbl *.blg *.rel *.pdf *~

