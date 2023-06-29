.PHONY: all common

RAW_DEPENDENCIES=\
  sum.csv \
  rightmost.csv \
  copy.csv \
  plot.tex \
  timing.tex \
  binary-tree.tex \
  sum-at.tex \
  data-layout.tex \
  data-layout-nodes.tex \
  data-hexdump.tex \
  robust-catch.tex \
  safefold.tex \
  rightmost.tex \
  hoare.tex \
  idris2.sty \
  Snoc.idr.tex \
  Lib.idr.tex \
  Data/Singleton.idr.tex \
  Motivating.idr.tex \
  Serialised/Desc.idr.tex \
  SaferIndexed.idr.tex \
  SafeFolds.idr.tex \
  paper.bib \
  config.tex \
  abstract.tex \
  intro.tex \
  desc.tex \
  trees.tex \
  hexdump.tex \
  pointers.tex \
  poking.tex \
  bufferfold.tex \
  singleton.tex \
  views.tex \
  serialisation.tex \
  related-work.tex \
  limitations.tex \
  conclusion.tex \
  acknowledgements.tex

DEPENDENCIES=common \
  $(patsubst %,build/latex/%,$(RAW_DEPENDENCIES))

all: paper.pdf

popl: popl.pdf
	pdftk popl.pdf cat 1-27 output popl-paper.pdf
	pdftk popl.pdf cat 28-end output popl-appendices.pdf

common:
	$(MAKE) -C ../common

build/latex/%.idr.tex: common
	mkdir -p $(dir $@)
	cp ../common/$@ $@

build/latex/%.tex: %.tex
	mkdir -p build/latex
	cp $^ build/latex/

build/latex/%.csv: ../common/%.csv
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

build/latex/%.tex: ../common/%.tex
	mkdir -p build/latex
	cp $^ build/latex

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
