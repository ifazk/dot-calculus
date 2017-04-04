Require dpdgraph.dpdgraph.

Require LibLN.
Require Coq.Program.Equality.

Require Definitions.
Require Good_types.
Require Narrowing.
Require Safety.
Require Substitution.
Require Tight_possible_types.
Require Wellformed_store.
Require Canonical_forms2.
Require General_to_tight.
Require Precise_flow.
Require Some_lemmas.
Require Weakening.
Require Canonical_forms1.

Set DependGraph File "file_depend_wo_defs.dpd".

Print FileDependGraph Canonical_forms1 Good_types Narrowing Safety Substitution Tight_possible_types Wellformed_store Canonical_forms2 General_to_tight Precise_flow (*Some_lemmas*) Weakening.

Set DependGraph File "file_depend_wo_defs_slem.dpd".

Print FileDependGraph Canonical_forms1 Good_types Narrowing Safety Substitution Tight_possible_types Wellformed_store Canonical_forms2 General_to_tight Precise_flow (*Some_lemmas*) Weakening.
