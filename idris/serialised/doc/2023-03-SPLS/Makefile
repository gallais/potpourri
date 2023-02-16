PAPER=slides

RAW_DEPENDENCIES=\
  robust-catch.tex \
  idris2.sty \
  Serialised/Desc.idr.tex \
  SaferIndexed.idr.tex \

DEPENDENCIES=common \
  $(patsubst %,build/latex/%,$(RAW_DEPENDENCIES))

all: slides.pdf

common:
	$(MAKE) -C ../common

build/latex/%.idr.tex: common
	mkdir -p $(dir $@)
	cp ../common/$@ $@

build/latex/%.tex: %.tex
	mkdir -p build/latex
	cp $^ build/latex/

build/latex/robust-catch.tex: ../common/robust-catch.tex
	mkdir -p build/latex
	cp $^ build/latex

build/latex/idris2.sty: ../common/idris2.sty
	mkdir -p build/latex
	cp $^ build/latex

%.pdf: build/latex/%.tex $(DEPENDENCIES)
	mkdir -p build/latex
	cd build/latex && \
	latexmk -shell-escape -pdf -bibtex $*.tex
	ln -sf build/latex/$*.pdf $*.pdf

clean:
	make clean -C ../common
	rm -rf build/latex
	rm -rf code/build/
	rm -f *~
