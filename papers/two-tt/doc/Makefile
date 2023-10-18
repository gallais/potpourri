.PRECIOUS: __build/%.tex

AGDA_FILES:= \
 BasicTwoTT.lagda \
 TwoTT.lagda \
 MetaCircuit.lagda \
 STLC.lagda
AGDA_OUTPUT:=$(patsubst %.lagda,__build/%.tex,$(AGDA_FILES))

AGDA=agda

PAPER=pepm

all: $(PAPER).pdf

DEPENDENCIES:=$(AGDA_OUTPUT) \
  agda.sty \
  staging.bib \
  staging.tex \
  unicode.tex \
  config.tex \
  commands.tex \
  acks.tex \

__build/%.sty: %.sty
	@mkdir -p $(dir $@)
	cp $< $@

__build/%.bib: %.bib
	@mkdir -p $(dir $@)
	cp $< $@

__build/%.tex: %.lagda
	@mkdir -p $(dir $@)
	${AGDA} -i . --latex $< --latex-dir=__build > $(basename $@).log
	rm -f __build/agda.sty

%.pdf: %.tex $(DEPENDENCIES)
	latexmk -pdf -outdir=__build -bibtex $<
	ln -sf __build/$(basename $@).pdf .

clean:
	rm -rf __build
