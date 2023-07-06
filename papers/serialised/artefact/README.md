# Seamless, Correct, and Generic Programming over Serialised Data

This is the code accompanying the paper. It contains two versions of
the library: the original written in Idris, and its port to Agda.

## Dependencies

The following artefact has been tested with:

- Idris 2 (development version: [Installation instructions](https://github.com/idris-lang/Idris2/blob/main/INSTALL.md#installing-from-source))
- Agda 2 (development version: [Installation instructions](https://agda.readthedocs.io/en/latest/getting-started/installation.html#installation-development-version))
- The Agda Standard Library (development version: [Github Repository](https://github.com/agda/agda-stdlib))
- hexdump (part of the `util-linux` package)

## Running the artefact

We provide a [`Makefile`](src/Makefile) to run a toy example.
By calling it using `cd src/ && make` you will:

1. compile two executables

  - [`Alice`](src/idris/Alice.idr) written in Idris and using the original library written in Idris
  - [`Bob`](src/agda/Bob.agda) written in Agda using the library's port to Agda

2. run a small bash script that will

   i.   call `Alice` to generate a random tree and serialise it into a file
   ii.  call `hexdump` to print the binary content of the file
   iii. call `Bob` to load the file as a tree, print the tree, take its left branch, and writes the result in a second file
   iv.  call `hexdump` to inspect that second file's content too
   v.   call `Alice` to deserialise the content of the second file and print the tree

This prove that the library allows us to:
1. serialise trees and write them to a file
2. load trees from a file
3. program directly over values stored in buffers (taking the left branch)
4. store values associated to a 'pointer' into a file (writing the left branch)

and demonstrates that this setup allows us to easily exchange values
between independent programs irrespective of their implementation
language.
