%: %.idr
	idris2 $@.idr -o $@
	./build/exec/$@ $@.input

clean:
	rm -r build/
