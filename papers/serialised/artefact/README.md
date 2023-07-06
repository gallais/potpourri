# Seamless, Correct, and Generic Programming over Serialised Data

This archive contains

1. the [appendices](popl-appendices.pdf)
2. the code

accompanying the draft paper titled
'Seamless, Correct, and Generic Programming over Serialised Data'.

The code comprises two versions of the library: the original one
written in Idris, and its port to Agda.

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

   1. call `Alice` to generate a random tree and serialise it into a file
   2. call `hexdump` to print the binary content of the file
   3. call `Bob` to load the file as a tree,
      print the tree,
      take its left branch,
      and writes the result in a second file
   4. call `hexdump` to inspect that second file's content too
   5. call `Alice` to deserialise the content of the second file and print the tree

A typical trace looks something like the following:

```
Compiling Alice
Compiling Bob
Hello I am Alice, written in Idris!
I just generated the following random tree:
  (node (node (node leaf 178 leaf)
              48
              (node leaf 17 leaf))
        18
        (node (node leaf 112 leaf)
              43
              (node leaf 91 leaf)))
And I am now writing it in file commfile1.

Hello I am hexdump!
Here is the content of the file commfile1:
00000000  07 00 00 00 00 00 00 00  02 00 02 03 02 01 03 01  |................|
00000010  22 00 00 00 00 00 00 00  01 0c 00 00 00 00 00 00  |"...............|
00000020  00 01 01 00 00 00 00 00  00 00 00 b2 00 30 01 01  |.............0..|
00000030  00 00 00 00 00 00 00 00  11 00 12 01 0c 00 00 00  |................|
00000040  00 00 00 00 01 01 00 00  00 00 00 00 00 00 70 00  |..............p.|
00000050  2b 01 01 00 00 00 00 00  00 00 00 5b 00           |+..........[.|
0000005d

Hello I am Bob, written in Agda!
I just read the following tree from file commfile1:
  (node (node (node leaf 178 leaf)
              48
              (node leaf 17 leaf))
        18
        (node (node leaf 112 leaf)
              43
              (node leaf 91 leaf)))
Its rightmost node's value is: 91.
I just serialised the tree's left branch into file commfile2.

Hello I am hexdump!
Here is the content of the file commfile2:
00000000  07 00 00 00 00 00 00 00  02 00 02 03 02 01 03 01  |................|
00000010  0c 00 00 00 00 00 00 00  01 01 00 00 00 00 00 00  |................|
00000020  00 00 b2 00 30 01 01 00  00 00 00 00 00 00 00 11  |....0...........|
00000030  00                                                |.|
00000031

Hello I am Alice, written in Idris!
I just read the following tree from file commfile2:
  (node (node leaf 178 leaf)
        48
        (node leaf 17 leaf))
Its rightmost node's value is: 17.
```

This prove that the library allows us to:
1. serialise trees and write them to a file
2. load trees from a file
3. program directly over values stored in buffers
   (taking the left branch, looking up the rightmost node)
4. store values associated to a 'pointer' into a file
   (writing the left branch into a file)

and demonstrates that this setup allows us to easily exchange values
between independent programs irrespective of their implementation
language.

## Structure of the artefact

The important results are implemented in both Idris and Agda, while
the ones that are only needed for pedagogical purposes in the paper
(e.g. the more contrived --but seen as safe by the compiler--
implementation of `fold`) do not appear in Agda.

### Common modules

The core modules are:

1. `Data.Singleton` for the definition of the singleton family and
the combinators that the idiom bracket notation desugars to.

2. `Data.Serialisable.Desc` for the universe of description and the
encoding of the universe codes as binary data.

3. `Data.Serialisable.Data` for the meaning of these codes as strictly
positive functors, and their fixpoints as inductive types. It also
contains useful functions such as `fold`, `show`, and the generic
`All` predicate lifting.

4. `Data.Serialisable.Pointer` defines alternative meanings as pointers
into buffers and provides the necessary code to (inspect / construct) a
buffer in a correct-by-construction manner.

5. `Data.Serialisable.Tree` defines the inductive type `Tree`
that we use as a running example in the paper. It includes both
pure and correct-by-construction buffer-based versions of `sum`,
`rightmost`, `leftBranch`, `swap`, and `map`.

### Other modules

1. [`Lib`](src/idris/Lib.idr) contains some basic definitions needed
by the Idris 2 implementation.

2. [`SafeFolds`](src/idris/Data/Serialisable/SafeFolds.idr) contains
the implementations of `fold` that are seen as obviously structurally
recursive by Idris thanks to (manual) supercompilation.

3. [`Timing`](src/idris/Timing.idr) is the module we used to generate
the measurements shown in the paper.
It uses [`System.GC`](src/idris/System/GC.idr) to try to minimise the
impact of chezscheme's Garbage Collector on the timings.

4. [`Alice`](src/idris/Alice.idr) and [`Bob`](src/agda/Bob.idr) are the
two programs talking to each other via files containing binary data in
the example ran by the Makefile.

5. [`Data.Word8`](src/agda/Data/Word8.agda)
, [`Data.Int64`](src/agda/Data/Int64.agda)
, [`Data.Buffer`](src/agda/Data/Buffer.agda)
, [`Data.Buffer.IO`](src/agda/Data/Buffer/IO.agda)
, [`Data.Buffer.Builder`](src/agda/Data/Buffer/Builder.agda)
are Agda modules binding Haskell types and functions using the
Foreign Function Interface.
