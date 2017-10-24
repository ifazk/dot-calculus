# A Simple Soundness Proof for Dependent Object Types

Our [paper](https://plg.uwaterloo.ca/~olhotak/pubs/oopsla17.pdf) presents a simplified type-safety proof for the [version of DOT](https://infoscience.epfl.ch/record/215280) presented at Wadlerfest 2016. This repository contains a formalization of the simple proof in Coq. The definitions of the abstract syntax and several lemmas are based on the [original](https://github.com/samuelgruetter/dot-calculus/blob/master/dev/lf/dot_top_bot.v) Coq proof that comes with Wadlerfest DOT paper.

This directory contains a Coq formalization of the DOT calculus and DOT's type safety proof. Our technique is based on eliminating bad bounds by using *inert types* and applying the *proof recipe*, as described in the OOPSLA'17 [paper](https://plg.uwaterloo.ca/~olhotak/pubs/oopsla17.pdf).

## Documentation

The documentation can be accessed from the [Table of Contents](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/toc.html). This page lists links to pretty printed Coq source files, but the raw `.v` files can be found in the [proof](proof) directory. In the pretty-printed versions, the proof scripts are hidden by default, you may click on "Show Proofs" at the top of the page to display all the proofs, or click under the Lemma or Theorem statements to display their proofs.

### Proof Structure

The Coq proof is split up into the following modules:
  * [Definitions.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Definitions.html): The main inductive definitions and functions that are used in the proof. Defines the abstract syntax and type system.
  * [Binding.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Binding.html): Proves helper lemmas related to opening, closing, and local closure.
  * [SubEnvironments.v](SubEnvironments.v): Defines and proves lemmas related to subenvironments.
  * [Weakening.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Weakening.html): Proves the Weakening Lemma.
  * [RecordAndInertTypes.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/RecordAndInertTypes.html): Defines and proves lemmas related to record and inert types.
  * [Narrowing.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Narrowing.html): Proves the Narrowing Lemma.
  * [OperationalSemantics.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/OperationalSemantics.html): Defines normal forms and the operational semantics of DOT, as well as related helper lemmas.
  * [PreciseTypes.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/PreciseTypes.html): Defines and proves lemmas related to precise typing. In particular, reasons about the possible precise types that a variable can have in an inert environment.
  * [TightTypes.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/TightTypes.html): Defines tight typing and subtyping.
  * [Substitution.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Substitution.html): Proves the Substitution Lemma.
  * [InvertibleTypes.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/InvertibleTypes.html): Defines invertible typing and proves that in an inert context, tight typing implies invertible typing (both for variables and values).
  * [GeneralToTight.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/GeneralToTight.html): Proves that in an inert context, general typing implies tight typing.
  * [CanonicalForms.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/CanonicalForms.html): Proves the Canonical Forms Lemmas for functions and objects.
  * [Safety.v](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Safety.html): Proves the Progress and Preservation Theorems.

The following figure shows a dependency graph between the Coq modules.
![Dependency graph](https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/graph.png)

### Navigating Between the Paper and Proof

| Paper
 | Coq Proof
 |
| Item | Description | Subitems | File | Name | Notation |
| Figure 1
 | DOT abstract syntax
 | variable | [Definitions.v](doc/Definitions.html) | avar |
| term member
 | trm_label |
| type member
 | typ_label |
| term | trm |
| value | val |
| definition | def |
| type | typ |
| Figure 2
 | DOT Type Rules
 | term typing
 | [Definitions.v](doc/Definitions.html) | ty_trm | G ⊢ t : T |
| single-definition typing | ty_def | G ⊢ d : D |
| multiple-definition typing | ty_defs | G ⊢ ds :: T |
| subtyping
 | subtyp | G ⊢ T <: U |
| Figure 3
 | Tight typing rules
 | term typing
 | [TightTypes.v](doc/TightTypes.html) | ty_trm_t | G ⊢<sub>#</sub> t : T |
| subtyping
 | subtyp_t | G ⊢<sub>#</sub> T <: U |
| Definition 3.1
 | Inert context
 | [RecordAndInertTypes.v](doc/RecordAndInertTypes.html) | inert |
| Definition 3.2
 | Inert type
 | [RecordAndInertTypes.v](doc/RecordAndInertTypes.html) | inert_typ |
| Figure 4
 | Precise typing rules
 | [PreciseTypes.v](doc/PreciseTypes.html) | ty_trm_p | G ⊢<sub>!</sub> t : T |
| Theorem 3.3
 | General-to-tight typing (⊢ to ⊢<sub>#</sub>) | [GeneralToTight.v](doc/GeneralToTight.html) | general_to_tight |
| Lemma 3.4
 | Sel-<: replacement | [GeneralToTight.v](doc/GeneralToTight.html)
 | sel_replacement |
| Lemma 3.5
 | Sel-<:# premise
 | [GeneralToTight.v](doc/GeneralToTight.html) | sel_premise |
| Figure 5
 | Invertible typing rules
 | for variables
 | [InvertibleTypes.v](doc/InvertibleTypes.html) | ty_var_inv | G ⊢<sub>##</sub> x : T |
| for values
 | ty_val_inv | G ⊢<sub>##v</sub> v : T |
| Theorem 3.6
 | Tight-to-invertible typing (⊢<sub>#</sub> to ⊢<sub>##</sub>) | for variables
 | [InvertibleTypes.v](doc/InvertibleTypes.html) | tight_to_invertible |
| for values
 | tight_to_invertible_v |
| Lemma 3.7
 | ∀ to Γ(x) | [CanonicalForms.v](doc/CanonicalForms.html) | var_typ_all_to_binds |
| Lemma 3.8
 | ∀ to λ | [CanonicalForms.v](doc/CanonicalForms.html) | val_typ_all_to_lambda |
| Lemma 3.9
 | μ to Γ(x) | [CanonicalForms.v](doc/CanonicalForms.html) | var_typ_rcd_to_binds |
| Lemma 3.10
 | μ to ν | [CanonicalForms.v](doc/CanonicalForms.html) | val_mu_to_new |
| Lemma 3.11
 | Narrowing | [Narrowing.v](doc/Narrowing.html) | narrow_rules
 |
| Figure 7
 | Operational semantics
 | [OperationalSemantics.v](doc/OperationalSemantics.html) | red | e[t<sub>1</sub> ↦ t<sub>2</sub>] |
| Definition 3.12
 | Well-typed evaluation contexts with respect to a typing context | [Definitions.v](doc/Definitions.html) | well_typed |
| Lemma 3.15
 | Value typing
 | [Safety.v](doc/Safety.html) | val_typing |
| Definition 3.16
 | Normal form | [OperationalSemantics.v](doc/OperationalSemantics.html) | normal_form |
| Theorem 3.17
 | Progress | [Safety.v](doc/Safety.html) | progress |
| Theorem 3.18
 | Preservation | [Safety.v](doc/Safety.html) | preservation |
| Lemma 3.19
 | Substitution | [Substitution.v](doc/Substitution.html) | subst_ty_trm |

## Compiling the Proof

To compile the proof, we require `coq 8.6` and related tooling to be run in a unix-like environment. In particular, we require the following tools (all version 8.6) in the `PATH` enviroment variable:
  * coqc
  * coqtop
  * coqdep
  * coqdoc
  * coqmakefile

Other requirements are:
  * make

To compile the proof, run

    git clone https://github.com/amaurremi/dot-calculus
    cd dot-calculus/src/simple-proof
    make

`make` will do the following:

- compile the `tlc` library
- compile the safety proof
- generate documentation.
