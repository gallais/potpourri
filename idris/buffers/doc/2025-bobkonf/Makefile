BUILDDIR=__build
DEPENDENCIES=\
  motivation.tex\
  hoarelogic.tex\
  separationlogic.tex

all: slides.pdf



%.pdf: %.tex ${DEPENDENCIES}
	latexmk -pdf $< -outdir=${BUILDDIR}
	ln -sf ${BUILDDIR}/$@ $@

clean:
	rm -r ${BUILDDIR}
	rm -f slides.pdf
