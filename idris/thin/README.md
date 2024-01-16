# Builtin Types viewed as Inductive Families

## Architecture of the artefact

The directory `src/` contains the annotated source files whose content
is described in the paper
[Builtin Types viewed as Inductive Families](https://arxiv.org/abs/2301.02194).

The directory `run` contains the virtual machine as well as the support
code to run the executable. More specifically:

  1. `run/idris2-vm` contains the virtual machine generated using
     [packer-idris](https://github.com/jfdm/packer-idris).
  2. `run/scripts` contains the bash script the virtual machine runs
  3. `run/build-source-code.json` is the file driving the VM's execution:
     it first obtains the source code (passed via a tarball) and then
     calls the `load-code.sh` defined in `run/scripts`.
  4. `run/Makefile` describes the various targets. Crucially, before running
     the VM we generate a tarball containing the sourced code present in `src/`.

## Correspondence with the paper

### File [`VectAsList.idr`](src/VectAsList.idr)

This combines the content of Section 3.3:

- defining `Vect`, `Nil`, `(::)`, `View`, `view`, `map`, `lookup`

as well as appendix B

- defining `(++)`, `SplitAt`, `(::)`, `splitAt`
- showing the rejected `splitAt` variants using `failing` blocks

### File [`FinAsNat.idr`](src/FinAsNat.idr)

This contains the definition left out of Section 3.3.2:

- defining `Fin`, `Z`, `S`, `View`, `view`


### File [`Data/Bits/Integer/Postulated.idr`](src/Data/Bits/Integer/Postulated.idr)

This matches the content of appendix A.

### File [`Data/Bits/Integer.idr`](src/Data/Bits/Integer.idr)

This matches part of Section 5.3:

- defining `cons`, `cofull`, `full`
- proving `testBit0Cons`, `consShiftR`

### File [`Thin/Internal.idr`](src/Thin/Internal.idr)

This matches the content of the rest of Section 5.3:

- defining `Invariant`, `none`, `ones`
- proving the relation to be proof-irrelevant (`irrelevantInvariant`)
- and invertible (`isDone`, `isKeep`, `isDrop`)

### File [`Thin.idr`](src/Thin.idr)

This matches the content of the rest of Section 5:

- defining `Th`, `done`, `keep`, `drop`, `which`, `View`, `view`, `kept`

### Compiled code

Cf. [Running the artifact](#running-the-artifact) for a description of
how to obtain the compiled version of the `view` function in order to
reproduce the result in Section 5.5.

## Running the VM on the code

### Dependencies

The VM provided with this artifact is a small alpine linux box with
Idris 2 version 0.6.0 installed.
It was built using [packer-idris](https://github.com/jfdm/packer-idris).

To run it, you will need to install (using Ubuntu's package names):

- packer
- virtualbox
- virtualbox-guest-additions-iso

### Running the artifact

Verifying the results should be as simple as running `cd run; make`.
This will load the VM containing `idris2` and run the script defined
in [`load-code.sh`](run/scripts/load-code.sh).

This should give you, after some amount of administrative virtualbox output
describing the machine's booting process, four main steps:

0. Checking the installation (printing the Idris 2 version number)
1. Extracting the code (it is passed to the VM via a tarball)
2. Checking the code (building the `thin.ipkg` package)
3. Compiling the code (compiling `Main.idr` to force code generation)

After this last step, the code the `view` function was compiled to is
extracted using `awk` and displayed in the trace. This is what allows
you to check it corresponds to what is described in Section 5.5.

Running this VM should not take more than a couple of minutes.
