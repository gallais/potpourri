all: javascript vectaslist

javascript:
	idris2 -p contrib -c Main.idr
	idris2 -p contrib --cg javascript -o main Main.idr

vectaslist:
	idris2 -c VectAsList.idr

clean:
	rm -rf build/
