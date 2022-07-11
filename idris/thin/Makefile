PAPER=thin

all:
	mkdir -p build/latex
	cp ${PAPER}.tex ${PAPER}.bib build/latex/
	cd build/latex && latexmk -pdf -bibtex ${PAPER}.tex
	ln -sf build/latex/${PAPER}.pdf ${PAPER}.pdf

clean:
	rm -r build/latex
