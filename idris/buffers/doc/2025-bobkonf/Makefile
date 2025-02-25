BUILDDIR=__build

.PRECIOUS: $(BUILDDIR)/%.idr.tex

LATEX_DEPENDENCIES=\
  motivation.tex\
  hoarelogic.tex\
  separationlogic.tex\
  writingprograms.tex\

IDRIS_DEPENDENCIES=\
  Data/Buffer/Indexed.idr.tex

DEPENDENCIES=\
  $(LATEX_DEPENDENCIES)\
  $(patsubst %,$(BUILDDIR)/%,$(IDRIS_DEPENDENCIES))

all: slides.pdf

../build/ttc/*/%.ttm ../build/ttc/*/%.ttc: ../%.tex
	cd ..; idris2 -p linear -c $*.tex

__build/%.idr.tex: ../%.tex ../build/ttc/*/%.ttm ../build/ttc/*/%.ttc
	mkdir -p $(dir $@)
	katla literate ../$*.tex ../build/ttc/*/$*.ttm > $@
	perl -0777 -i -pe 's/\\Katlanewline{}\n\\end{code}/\n\\end{code}/igs' $@
	sed -i 's/{code}/{IDRIScode}/g' $@


%.pdf: %.tex ${DEPENDENCIES}
	latexmk -pdf $< -outdir=${BUILDDIR}
	ln -sf ${BUILDDIR}/$@ $@

clean:
	rm -r ${BUILDDIR}
	rm -f slides.pdf
