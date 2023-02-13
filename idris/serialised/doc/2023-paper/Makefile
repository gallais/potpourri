.PRECIOUS: code/build/ttc/%.ttm code/build/ttc/%.ttc build/latex/%.idr.tex

PAPER=paper
DEPENDENCIES=\
  build/latex/robust-catch.tex \
  build/latex/idris2.sty \
  build/latex/Serialised/Desc.idr.tex \
  build/latex/desc.tex \
  build/latex/trees.tex \
  build/latex/pointers.tex \

all: paper.pdf

code/build/ttc/*/%.ttm code/build/ttc/*/%.ttc: code/%.tex
	cd code && idris2 -c $*.tex

build/latex/%.idr.tex: code/%.tex code/build/ttc/*/%.ttm code/build/ttc/*/%.ttc
	mkdir -p $(dir $@)
	katla literate code/$*.tex code/build/ttc/*/$*.ttm > $@

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
	rm -rf build/latex
	rm -rf code/build/
	rm -f *~
