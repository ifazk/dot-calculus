Require dpdgraph.dpdgraph.

Require LibLN.
Require Coq.Program.Equality.

Require Definitions.
Require Weakening.
Require Helper_lemmas.
Require Narrowing.
Require General_to_tight.
Require Invertible_typing.
Require Wellformed_store.
Require Precise_types.
Require Substitution.
Require Canonical_forms1.
Require Canonical_forms2.
Require Safety.

Set DependGraph File "tight_wo_defs.dpd".

Print FileDependGraph
(*Definitions*)
Weakening
Helper_lemmas
Narrowing
General_to_tight
Invertible_typing
Wellformed_store
Precise_types
Substitution
Canonical_forms1
Canonical_forms2
Safety.

Set DependGraph File "tight_wo_defs_slem.dpd".

Print FileDependGraph
(*Definitions*)
Weakening
(* Helper_lemmas *)
Narrowing
General_to_tight
Invertible_typing
Wellformed_store
Precise_types
Substitution
Canonical_forms1
Canonical_forms2
Safety.
