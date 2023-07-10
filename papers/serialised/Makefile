AGDA_SRC_FILES:= \
  Data/Word8.agda \
  Data/Int64/Primitive.agda \
  Data/Word8/Primitive.agda \
  Data/Serialisable/Data.agda \
  Data/Serialisable/Tree.agda \
  Data/Serialisable/Pointer.agda \
  Data/Serialisable/Desc.agda \
  Data/Singleton.agda \
  Data/Buffer.agda \
  Data/Buffer/IO.agda \
  Data/Buffer/Builder/Primitive.agda \
  Data/Buffer/Primitive.agda \
  Data/Buffer/IO/Primitive.agda \
  Data/Buffer/Builder.agda \
  Data/Int64.agda \
  Bob.agda \

IDRIS_SRC_FILES:= \
  Timing.idr \
  System/GC.idr \
  Lib.idr \
  Alice.idr \
  Data/Serialisable/Desc.idr \
  Data/Serialisable/Tree.idr \
  Data/Serialisable/SafeFolds.idr \
  Data/Serialisable/Data.idr \
  Data/Serialisable/Pointer.idr \
  Data/Singleton.idr \

AGDA_FILES:=$(patsubst %,artefact/src/agda/%,$(AGDA_SRC_FILES))
IDRIS_FILES:=$(patsubst %,artefact/src/idris/%,$(IDRIS_SRC_FILES))

OTHER_DEPENDENCIES:= \
  artefact/popl-appendices.pdf \
  artefact/src/Makefile \

all: popl-appendices.tar.gz

popl-appendices.tar.gz: ${AGDA_FILES} ${IDRIS_FILES} ${OTHER_DEPENDENCIES}
	tar -czvf popl-appendices.tar.gz artefact

popl:
	make -C doc/2023-paper popl

artefact/popl-appendices.pdf: popl
	cp doc/2023-paper/popl-appendices.pdf artefact/

artefact/src/%: src/%
	mkdir -p $(dir $@)
	cp $< $@

clean:
	rm -rf artefact/src
	rm -f artefact/*.pdf
