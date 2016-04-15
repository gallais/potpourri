all:
	mkdir -p __build/
	./lagdas2tex
	rm -f main.pdf
	cp *.lagda *.tex *.pdf *.bib *.cls __build/
	agda -i . --latex --latex-dir=__build/ main.lagda
	cd __build && latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex --shell-espace %O %S/' main.tex
	ln -sf __build/main.pdf
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1
