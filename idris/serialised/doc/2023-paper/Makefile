.PHONY: all common

PAPER=paper
RAW_DEPENDENCIES=\
  robust-catch.tex \
  idris2.sty \
  Serialised/Desc.idr.tex \
  SaferIndexed.idr.tex \
  paper.bib \
  intro.tex \
  desc.tex \
  trees.tex \
  hexdump.tex \
  pointers.tex \
  conclusion.tex \
  acknowledgements.tex

DEPENDENCIES=common \
  $(patsubst %,build/latex/%,$(RAW_DEPENDENCIES))


all: paper.pdf

common:
	$(MAKE) -C ../common

build/latex/%.idr.tex: common
	mkdir -p $(dir $@)
	cp ../common/$@ $@

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

build/latex/idris2.sty: ../common/idris2.sty
	mkdir -p build/latex
	cp $^ build/latex

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
	$(MAKE) clean -C ../common
