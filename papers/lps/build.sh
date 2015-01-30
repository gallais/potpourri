#!/bin/sh
FILE=$1
mkdir -p latex/
cp *.pdf *.cls *.tex *.bib *.sed latex/
agda -i . -i ~/languages/agda/libs/agda-stdlib/src/ -i ~/projects/potpourri/agda/ -i ~/projects/nad-equality --latex $FILE.lagda
cd latex
sed -f rules.sed -i $FILE.tex
sed -f rules.sed -i commands.tex
latexmk -bibtex -pdf -e '$pdflatex=q/xelatex %O %S/' $FILE.tex
cd ..
