.PRECIOUS: build/ttc/%.ttm build/ttc/%.ttc build/latex/%.idr.tex

PAPER=paper

TEX_FILES:=$(shell find . -name "*.tex" -type f | grep -v build | sed 's|\./||g' | sort)
KATLA_OUTPUT:=$(patsubst %.tex,build/latex/%.idr.tex,$(TEX_FILES))

all: $(KATLA_OUTPUT)

build/ttc/*/%.ttm build/ttc/*/%.ttc: %.tex
	idris2 -c $*.tex

build/latex/%.idr.tex: %.tex build/ttc/*/%.ttm build/ttc/*/%.ttc
	mkdir -p $(dir $@)
	katla literate $*.tex build/ttc/*/$*.ttm > $@

clean:
	rm -rf build/latex
	rm -rf build/
	rm -f *~
