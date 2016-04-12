lagdas:
	./lagdas2tex

main:
	mkdir -p __build/
	cp *.lagda *.tex *.pdf *.bib *.cls __build/
	agda -i . --latex --latex-dir=__build/ main.lagda
	cd __build && latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex --shell-espace %O %S/' main.tex
	ln -s __build/main.pdf .
