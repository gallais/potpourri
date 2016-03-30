all: thesis

thesis:
	./lagda2tex "type-scope-semantics/models.lagda"
	./build
	ln -sf latex/thesis.pdf
clean:
	rm -rf latex/ *.log thesis.pdf
