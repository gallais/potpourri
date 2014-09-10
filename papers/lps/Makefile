all:
	mkdir -p latex/ && cp *.lagda *.sty *.tex *.bib latex/ && cd latex && latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex %O %S/' lps.lagda && cd ..
