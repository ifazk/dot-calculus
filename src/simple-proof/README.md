# A Simple Soundness Proof for Dependent Object Types

This is a simplified version of the [original](https://github.com/samuelgruetter/dot-calculus) Wadlerfest [DOT](http://infoscience.epfl.ch/record/215280/files/paper_1.pdf) type-safety proof.

Please refer to our [technical report](https://arxiv.org/abs/1706.03814) for details.

## Compiling the proof

To compile the proof, navigate to the artifact directory from a terminal window and run `make`. This will do the following:
* compile the `tlc` library;
* compile the safety proof;
* generate documentation.
Successful compilation indicates a correct proof.

## Inspecting Source files

The documentation can be accessed from the Table of Contents (`toc.html`) in the `doc` directory. This page lists links to pretty printed coq source files, but the raw .v files can be found in the `proof` directory. In the pretty-printed versions, the proof scripts are hidden by default, you may click on "Show Proofs" at the top of the page to display all the proofs, or click under the Lemma or Theorem statements to display their proofs.
