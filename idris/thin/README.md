# Builtin Types viewed as Inductive Families

## Correspondence with the paper

### File `VectAsList.idr`

This combines the content of Section 3.3
(defining `Vect`, `Nil`, `(::)`, `View`, `view`, `map`, `lookup`)
as well as appendix B (defining `(++)`, `SplitAt`, `(::)`,
`splitAt` and its rejected variants).

### File `Data/Bits/Integer/Postulated.idr`

This matches the content of appendix A.

### File `Data/Bits/Integer.idr`

This includes part of Section 5.3's definitions
(`cons`, `cofull`, `full`, `testBit0Cons`, `consShiftR`)

### File `Thin/Internal.idr`

This matches the content of the rest Section 5.3:

- defining `Invariant`, `none`, `ones`
- proving the relation to be proof-irrelevant (`irrelevantInvariant`)
- and invertible (`isDone`, `isKeep`, `isDrop`)

### File `Thin.idr`

This matches the content of the rest of Section 5
(defining `Th`, `done`, `keep`, `drop`, `which`, `View`, `view`,
`kept`).

### Compiled code

Cf. [Running the artifact](#running-the-artifact) for a description of
how to obtain the compiled version of the `view` function in order to
reproduced the result in Section 5.5.

## Running the VM on the code

### Dependencies

The VM used for this artifact requires (using Ubuntu's package names):

- packer
- virtualbox
- virtualbox-guest-additions-iso

### Running the artifact

Verifying the results should be as simple as running `cd run; make`.
This will load a VM containing `idris2` and run the script defined
in `scripts/load-code.sh`.

This should give you, after some amount of administrative virtualbox output
describing the machine's booting process, four main steps:

0. Checking the installation
1. Extracting the code
2. Checking the code
3. Compiling the code

After this last step, the code the `view` function was compiled to is
displayed in the trace thus allowing you to check it corresponds to what
is shown in Section 5.5.

Overall this should not take more than a couple of minutes.
