all:
	mkdir -p latex/ && cp *.pdf *.lagda *.cls *.tex *.bib *.sed latex/ && \
	agda -i . -i ~/languages/agda/libs/agda-stdlib/src/ -i ~/projects/potpourri/agda/ -i ~/projects/nad-equality --latex lps.lagda && \
	cd latex && sed -f rules.sed -i lps.tex && sed -f rules.sed -i commands.tex && \
	latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex %O %S/' lps.tex && cd ..

clean:
	rm -rf latex/
