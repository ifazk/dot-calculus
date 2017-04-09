Require dpdgraph.dpdgraph.

Require LibLN.
Require Coq.Program.Equality.

Require Definitions.
Require Weakening.
Require Some_lemmas.
Require Precise_flow.
Require Good_types.
Require Narrowing.
Require Tight_possible_types.
Require General_to_tight.
Require Tight_possible_types_val.
Require Wellformed_store.
Require Substitution.
Require Canonical_forms1.
Require Canonical_forms2.
Require Safety.

Set DependGraph File "tight_wo_defs.dpd".

Print FileDependGraph
(*Definitions*)
Weakening
Some_lemmas
Precise_flow
Good_types
Narrowing
Tight_possible_types
General_to_tight
Tight_possible_types_val
Wellformed_store
Substitution
Canonical_forms1
Canonical_forms2
Safety
.

Set DependGraph File "tight_wo_defs_slem.dpd".

Print FileDependGraph
(*Definitions*)
Weakening
(*Some_lemmas*)
Precise_flow
Good_types
Narrowing
Tight_possible_types
General_to_tight
Tight_possible_types_val
Wellformed_store
Substitution
Canonical_forms1
Canonical_forms2
Safety
.
