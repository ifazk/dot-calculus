Require dpdgraph.dpdgraph.

Require LibLN.
Require Coq.Program.Equality.

Require Definitions.
Require Local_Closure.
Require Operational_semantics.
Require Weakening.
Require Narrowing.
Require Helper_lemmas.
Require Precise_types.
Require Tight_types.
Require Substitution.
Require Invertible_typing.
Require General_to_tight.
Require Canonical_forms.
Require Safety.

Set DependGraph File "graph.dpd".

Print FileDependGraph
Definitions
Local_Closure
Operational_semantics
Weakening
Narrowing
Helper_lemmas
Precise_types
Tight_types
Substitution
Invertible_typing
General_to_tight
Canonical_forms
Safety.

(*
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
*)
