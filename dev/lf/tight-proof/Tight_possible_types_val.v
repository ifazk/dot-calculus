Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Precise_flow.
Require Import Good_types.

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

Inductive tight_pt_v : ctx -> val -> typ -> Prop :=
  (* Precise typing *)
| t_pt_precise_v : forall G v T,
  ty_trm ty_precise sub_general G (trm_val v) T ->
  tight_pt_v G v T
  (* Forall *)
| t_pt_all_v : forall L G v S T S' T',
  tight_pt_v G v (typ_all S T) ->
  subtyp ty_general sub_tight G S' S ->
  (forall y, y \notin L ->
   subtyp ty_general sub_general (G & y ~ S') (open_typ y T) (open_typ y T')) ->
  tight_pt_v G v (typ_all S' T')
  (* Tight Selection *)
| t_pt_sel_v : forall G v y A S,
  tight_pt_v G v S ->
  ty_trm ty_precise sub_general G (trm_var y) (typ_rcd (dec_typ A S S)) ->
  tight_pt_v G v (typ_sel y A)
| t_pt_and_v : forall G v T U,
  tight_pt_v G v T ->
  tight_pt_v G v U ->
  tight_pt_v G v (typ_and T U)
  (* Top *)
| t_pt_top_v : forall G v T,
  tight_pt_v G v T ->
  tight_pt_v G v typ_top.

Hint Constructors tight_pt_v.

Lemma tight_possible_types_closure_tight_v: forall G v T U,
  good G ->
  tight_pt_v G v T ->
  subtyp ty_general sub_tight G T U ->
  tight_pt_v G v U.
Proof.
  introv Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversions HT. false* good_ty_precise_bot_v.
  - inversions HT. inversions H. false* H0. assumption.
  - inversions HT. inversions H. false* H0. assumption.
  - inversions HT. inversions H. false* H0.
  - inversions HT. inversions H. false* H0.
  - inversions HT. inversions H0. false* H1.
    lets Hb: (good_unique_tight_bounds Hgd H H5). subst*.
Qed.

Lemma tight_possible_types_lemma_v : forall G v T,
    good G ->
    ty_trm ty_general sub_tight G (trm_val v) T ->
    tight_pt_v G v T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hgd eq_refl eq_refl eq_refl).
  apply* tight_possible_types_closure_tight_v.
Qed.
