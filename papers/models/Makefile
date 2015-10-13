PAPER=models
AUXILIARY=usual
SLIDES=slides

all: finish

prepare:
	mkdir -p latex/ && rm -f latex/$(SLIDES).* && cp *.tex *.pdf *.cls *.bib *.sed *.config latex/

paper: prepare
	agda -i . -i ~/languages/agda/libs/agda-stdlib/src/ -i ~/projects/potpourri/agda/ --latex $(PAPER).lagda && \
	cd latex && sed -f rules.sed -i $(PAPER).tex && \
	latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex %O %S/' $(PAPER).tex && cd ..

auxiliary:
	agda -i . -i ~/languages/agda/libs/agda-stdlib/src/ -i ~/projects/potpourri/agda --latex $(AUXILIARY).lagda

slides: prepare
	cd latex && sed -f rules.sed -f rules2.sed -i $(SLIDES).tex -i $(AUXILIARY).tex $(PAPER).tex && \
	latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex %O %S/' $(SLIDES).tex && cd ..

finish: paper auxiliary slides
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1
clean:
	rm *.agdai
	rm -rf latex/
