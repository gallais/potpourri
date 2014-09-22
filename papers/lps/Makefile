all:
	mkdir -p latex/ && cp *.lagda *.cls *.sty *.tex *.bib *.sed latex/ && \
	agda -i . -i ~/languages/agda/libs/agda-stdlib/src/ -i ~/projects/potpourri/agda/ --latex lps.lagda && \
	cd latex && sed -f rules.sed -i lps.tex && \
	latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex %O %S/' lps.tex && cd ..

clean:
	rm -rf latex/
