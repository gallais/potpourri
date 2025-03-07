all: session.pdf

%.pdf: %.tex
	latexmk -pdf -outdir=__build $<
	ln -sf __build/$@ $@
