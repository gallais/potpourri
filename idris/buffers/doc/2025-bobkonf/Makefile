BUILDDIR=__build

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

$(BUILDDIR)/%.idr.tex: ../%.tex
	mkdir -p $(dir $@)
	cd ..; idris2 -p linear -c $*.tex
	katla literate ../$*.tex ../build/ttc/*/$*.ttm > $@
	perl -0777 -i -pe 's/\\Katlanewline{}\n\\end{code}/\n\\end{code}/igs' $@
	sed -i 's/{code}/{IDRIScode}/g' $@


%.pdf: %.tex ${DEPENDENCIES}
	latexmk -pdf $< -outdir=${BUILDDIR}
	ln -sf ${BUILDDIR}/$@ $@

clean:
	rm -r ${BUILDDIR}
	rm -f slides.pdf
