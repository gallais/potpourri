FILE         := models
AGDAOPTIONS  := --allow-unsolved-metas
AGDAINCLUDES := -i . -i ~/languages/agda/libs/agda-stdlib/src -i ~/projects/potpourri/agda/

all:
	mkdir -p latex/ && cp *.lagda *.tex *.bib *.sed latex/ && \
	agda $(AGDAOPTIONS) $(AGDAINCLUDES) --latex $(FILE).lagda && \
	cd latex && sed -f rules.sed -i $(FILE).tex && sed -f rules.sed -i commands.tex && \
	latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex %O %S/' $(FILE).tex && cd ..

clean:
	rm -rf latex/
