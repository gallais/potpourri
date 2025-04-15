BUILDDIR=__build

LATEX_DEPENDENCIES=\

IDRIS_DEPENDENCIES=\
  System/Concurrency/Session/MuNuN.idr.tex\
  Data/OpenUnion/PrintOnly.idr.tex\

DEPENDENCIES=\
  $(LATEX_DEPENDENCIES)\
  $(patsubst %,$(BUILDDIR)/%,$(IDRIS_DEPENDENCIES))

all: session.pdf

$(BUILDDIR)/%.idr.tex: %.idr.tex
	mkdir -p $(dir $@)
	idris2 -p linear -c $<
	katla literate $< build/ttc/*/$*.ttm > $@
	perl -0777 -i -pe 's/\\Katlanewline{}\n\\end{code}/\n\\end{code}/igs' $@


%.pdf: %.tex ${DEPENDENCIES}
	latexmk -pdf -outdir=$(BUILDDIR) $<
	ln -sf __build/$@ $@

clean:
	rm -rf __build/ build/
