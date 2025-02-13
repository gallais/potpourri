BUILDDIR=__build
DEPENDENCIES=../common/data-layout.tex

all: slides.pdf



%.pdf: %.tex ${DEPENDENCIES}
	latexmk -pdf $< -outdir=${BUILDDIR}
	ln -sf ${BUILDDIR}/$@ $@

clean:
	rm -r ${BUILDDIR}
	rm -f slides.pdf
