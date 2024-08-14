
main.pdf: main.tex fp_syntax.tex biblio.bib
	latexmk -pdf main

.PHONY: clean
clean:
	latexmk -C
	$(RM) main.cb main.cb2 main.bbl
