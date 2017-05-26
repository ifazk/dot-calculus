Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Precise_flow.
Require Import Inert_types.

(* ###################################################################### *)
(** ** Tight Possible types for values *)

(*
Definition (Tight Possible types)

For a variable v, environment G, the set TPTv(G, v) of simplified possible types
of v is the smallest set SS such that:

If G |-! v:T then T in SS.
If all(x: S)T in SS, G |-# S'<:S and G, x: S' |-# T<:T' then all(x: S')T' in SS.
If S1 in SS and S2 in SS then (S1 & S2) in SS.
If S in SS and G |-! y: {A: S..S} then y.A in SS.
 *)

Reserved Notation "G '|-##v' v ':' T" (at level 40, v at level 59).

Inductive tight_pt_v : ctx -> val -> typ -> Prop :=
  (* Precise typing *)
| t_pt_precise_v : forall G v T,
    G |-! trm_val v : T ->
    G |-##v v : T
  (* Forall *)
| t_pt_all_v : forall L G v S T S' T',
    G |-##v v : typ_all S T ->
    G |-# S' <: S ->
    (forall y, y \notin L ->
      G & y ~ S' |- T ||^ y <: T' ||^ y) ->
    G |-##v v : typ_all S' T'
  (* Tight Selection *)
| t_pt_sel_v : forall G v p A S,
    G |-##v v : S ->
    G |-! trm_path p : typ_rcd (dec_typ A S S) ->
    G |-##v v : typ_path p A
| t_pt_and_v : forall G v T U,
    G |-##v v : T ->
    G |-##v v : U ->
    G |-##v v : typ_and T U
  (* Top *)
| t_pt_top_v : forall G v T,
    G |-##v v : T ->
    G |-##v v : typ_top
where "G '|-##v' v ':' T" := (tight_pt_v G v T).

Hint Constructors tight_pt_v.

Lemma tight_possible_types_closure_tight_v: forall G v T U,
  inert G ->
  tight_pt_v G v T ->
  G |-# T <: U ->
  G |-##v v : U.
Proof.
  introv Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversions HT. inversion H.
  - inversions HT. inversion H. assumption.
  - inversions HT. inversions H. assumption.
  - inversions HT. inversions H.
  - inversions HT. inversions H.
  - inversions HT. inversions H0.
    lets Hb: (inert_unique_tight_bounds Hgd H H5). subst*.
Qed.

Lemma tight_possible_types_lemma_v : forall G v T,
    inert G ->
    G |-# trm_val v : T ->
    G |-##v v : T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hgd eq_refl eq_refl eq_refl).
  apply* tight_possible_types_closure_tight_v.
Qed.
