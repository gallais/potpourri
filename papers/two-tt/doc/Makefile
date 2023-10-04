AGDA_FILES:= \
 BasicTwoTT.lagda \
 TwoTT.lagda \
 MetaCircuit.lagda \
 STLC.lagda
AGDA_OUTPUT:=$(patsubst %.lagda,__build/%.tex,$(AGDA_FILES))

AGDA=agda

DEPENDENCIES:=$(AGDA_OUTPUT) \
  staging.bib

__build/%.bib: %.bib
	@mkdir -p $(dir $@)
	cp $< $@

__build/%.tex: %.lagda
	@mkdir -p $(dir $@)
	${AGDA} -i . --latex $< --latex-dir=__build > $(basename $@).log

all: $(DEPENDENCIES)
	latexmk -pdf -outdir=__build -bibtex staging.tex

clean:
	rm -rf __build
