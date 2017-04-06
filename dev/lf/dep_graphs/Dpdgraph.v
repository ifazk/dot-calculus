Require dpdgraph.dpdgraph.

Require LibLN.
Require Coq.Program.Equality.

Require Definitions.
Require Weakening.
Require Wellformed_store.
Require Some_lemmas.
Require Precise_flow.
Require Good_types.
Require Tight_possible_types.
Require Substitution.
Require Narrowing.
Require General_to_tight.
Require Canonical_forms1.
Require Canonical_forms2.
Require Safety.

Set DependGraph File "tight_wo_defs.dpd".

Print FileDependGraph
(*Definitions*)
Weakening
Wellformed_store
Some_lemmas
Precise_flow
Good_types
Tight_possible_types
Substitution
Narrowing
General_to_tight
Canonical_forms1
Canonical_forms2
Safety
.

Set DependGraph File "tight_wo_defs_slem.dpd".

Print FileDependGraph
(*Definitions*)
Weakening
Wellformed_store
(*Some_lemmas*)
Precise_flow
Good_types
Tight_possible_types
Substitution
Narrowing
General_to_tight
Canonical_forms1
Canonical_forms2
Safety
.
