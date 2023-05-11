all: beamer.gif beamer2.gif

%.gif: ../%.tex
	cp $< .
	pdflatex $<
	convert -verbose -density 300 -coalesce $(*F).pdf $(*F)-%03d.gif && \
	convert -verbose -delay 100 -loop 0 $(*F)-*.gif $(*F)-tmp.gif && \
	convert -verbose -dispose previous -background "rgb(100%,100%,100%)" \
	$(*F)-tmp.gif -trim -layers TrimBounds -coalesce \
	-bordercolor "rgb(100%,100%,100%)" -border 40 -layers optimize $(*F).gif && \
	rm $(*F)-*

clean:
	rm *.gif *.tex *.pdf
