.PHONY=paper

PAPER=thin
DEPENDENCIES=\
  build/latex/robust-catch.tex \
  build/latex/view.tex \
  build/latex/${PAPER}.tex \
  build/latex/${PAPER}.bib \
  build/latex/Lookup.idr.tex \
  build/latex/QuantitativeTT.idr.tex \
  build/latex/Snoc.idr.tex \
  build/latex/Thin.idr.tex \
  build/latex/Thin/Internal.idr.tex \
  build/latex/idris2.sty

all: paper

build/ttc/%.ttm: %.tex
	idris2 -p contrib -c $^

build/latex/%.idr.tex: %.tex build/ttc/%.ttm
	mkdir -p $(basename $@)
	katla literate $*.tex build/ttc/$*.ttm > $@

build/latex/%.tex: %.tex
	mkdir -p build/latex
	cp $^ build/latex/

build/latex/%.bib: %.bib
	mkdir -p build/latex
	cp $^ build/latex/

build/latex/%.sty: %.sty
	mkdir -p build/latex
	cp $^ build/latex

paper: $(DEPENDENCIES)
	mkdir -p build/latex
	cd build/latex && \
	sed -i "s/Smart\.//g" Thin.idr.tex && \
	latexmk -shell-escape -pdf -bibtex ${PAPER}.tex
	ln -sf build/latex/${PAPER}.pdf ${PAPER}.pdf

clean:
	rm -r build/latex
	rm -f *~
