# Builtin Types viewed as Inductive Families

## Correspondence with the paper


## Dependencies

The VM used for this artifact requires (using Ubuntu's package names):

- packer
- virtualbox
- virtualbox-guest-additions-iso

## Running the artifact

Verifying the results should be as simple as running `cd run; make`.
This will load a VM containing `idris2` and run the script defined
in `scripts/load-code.sh`.

This should give you, after some amount of administrative virtualbox output
describing the machine's booting process, four main steps:

0. Checking the installation
1. Extracting the code
2. Checking the code
3. Compiling the code

After this last step, the code the `view` function was compiled to is displayed.
