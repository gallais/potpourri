all:
	latexmk -pdf -outdir=__build presentation.tex
	ln -sf __build/presentation.pdf him.pdf

clean:
	rm -rf __build/
	rm -f him.pdf
