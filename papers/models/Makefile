FILE=models

all:
	mkdir -p latex/ && cp *.lagda *.tex *.bib *.sed *.config latex/ && \
	agda -i . -i ~/languages/agda/libs/agda-stdlib/src/ -i ~/projects/potpourri/agda/ --latex $(FILE).lagda && \
	cd latex && sed -f rules.sed -i $(FILE).tex && \
	latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex %O %S/' $(FILE).tex && cd .. && \
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1
clean:
	rm -rf latex/
