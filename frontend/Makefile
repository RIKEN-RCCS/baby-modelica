## Makefile

.PHONY: readme notes nj njrun

parser.sml::
	../../byacc/yacc -v modelica-grammar.y
	mv y.tab.c parser.sml

nj::
	ml-build babymodelica.cm Babymodelica.main test-image

njrun::
	sml @SMLload test-image.x86-solaris arg1 arg2

readme:
	sed -n '/# Baby-Modelica/,/__Baby-Modelica comes with ABSOLUTELY NO WARRANTY.__/p' notes.tex > ../README.md

notes:
	pdflatex notes.tex

notes.bbl: notes.tex notes.bib
	bibtex notes

GOMI = notes.aux notes.blg notes.log notes.out notes.toc

clean::
	rm -f $(GOMI)
