BUILDDIR=__build/

all: buffer.pdf

%.pdf: %.tex
	latexmk -pdf -bibtex $< -outdir=$(BUILDDIR)
	ln -sf __build/$@ .

clean:
	rm -rf $(BUILDDIR)
