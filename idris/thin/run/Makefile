.PHONY: build-code

all: build-code

package-src:
	make -C ../src clean
	tar -czf src.tar.gz ../src/

build-code: package-src
	packer build -force build-source-code.json

clean:
	rm -rf packer_cache
	rm -rf output
	rm -rf output-virtualbox-ovf
	rm -f src.tar.gz
