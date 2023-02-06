.PRECIOUS: build/ttc/%.ttm build/ttc/%.ttc

PAPER=paper
DEPENDENCIES=\
  build/latex/robust-catch.tex \
  build/latex/idris2.sty

all: paper.pdf

build/ttc/*/%.ttm build/ttc/*/%.ttc: %.tex
	idris2 -p contrib -c $^

build/latex/%.idr.tex: %.tex build/ttc/*/%.ttm build/ttc/*/%.ttc
	mkdir -p $(dir $@)
	katla literate $*.tex build/ttc/*/$*.ttm > $@

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
	latexmk -shell-escape -pdf -bibtex $*.tex
	ln -sf build/latex/$*.pdf $*.pdf

clean:
	rm -r build/latex
	rm -r build/ttc
	rm -f *~
