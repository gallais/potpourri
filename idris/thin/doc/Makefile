.PRECIOUS: build/ttc/%.ttm build/ttc/%.ttc

PAPER=esop
DEPENDENCIES=\
  build/latex/llncs.cls \
  build/latex/splncs04.bst \
  build/latex/robust-catch.tex \
  build/latex/view.tex \
  build/latex/imports.tex \
  build/latex/appendix-axioms.tex \
  build/latex/appendix-limitations.tex \
  build/latex/optimisation.tex \
  build/latex/QTT.tex \
  build/latex/CdB.tex \
  build/latex/ast.tex \
  build/latex/abstract.tex \
  build/latex/introduction.tex \
  build/latex/conclusion.tex \
  build/latex/acknowledgements.tex \
  build/latex/efficient.tex \
  build/latex/thin.bib \
  build/latex/Lookup.idr.tex \
  build/latex/Thinnings.idr.tex \
  build/latex/QuantitativeTT.idr.tex \
  build/latex/Snoc.idr.tex \
  build/latex/Example.idr.tex \
  build/latex/VectAsList.idr.tex \
  build/latex/FinAsNat.idr.tex \
  build/latex/LookupRefactor.idr.tex \
  build/latex/WithExpanded.idr.tex \
  build/latex/UTLC.idr.tex \
  build/latex/Thin.idr.tex \
  build/latex/Thin/Internal.idr.tex \
  build/latex/Data/Bits/Integer.idr.tex \
  build/latex/Data/Bits/Integer/Postulated.idr.tex \
  build/latex/idris2.sty

all: esop.pdf thin.pdf

build/ttc/%.ttm build/ttc/%.ttc: %.tex
	idris2 -p contrib -c $^

build/latex/%.idr.tex: %.tex build/ttc/%.ttm build/ttc/%.ttc
	mkdir -p $(basename $@)
	katla literate $*.tex build/ttc/$*.ttm > $@

build/latex/%.tex: %.tex
	mkdir -p build/latex
	cp $^ build/latex/

build/latex/%.cls: %.cls
	mkdir -p build/latex
	cp $^ build/latex/

build/latex/%.bst: %.bst
	mkdir -p build/latex
	cp $^ build/latex/

build/latex/%.bib: %.bib
	mkdir -p build/latex
	cp $^ build/latex/

build/latex/%.sty: %.sty
	mkdir -p build/latex
	cp $^ build/latex

%.pdf: build/latex/%.tex $(DEPENDENCIES)
	mkdir -p build/latex
	cd build/latex && \
	sed -i "s/Smart\.//g" Thin.idr.tex && \
	latexmk -shell-escape -pdf -bibtex $*.tex
	ln -sf build/latex/$*.pdf $*.pdf

clean:
	rm -r build/latex
	rm -r build/ttc
	rm -f *~
