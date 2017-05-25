Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
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

Reserved Notation "G ',' S '|-##v' v '::' T" (at level 40, S at level 58, v at level 59).

Inductive tight_pt_v : ctx -> sigma -> val -> typ -> Prop :=
  (* Precise typing *)
| t_pt_precise_v : forall G S v T,
  G, S |-! trm_val v :: T ->
  G, S |-##v v :: T
  (* Forall *)
| t_pt_all_v : forall L G S v V T V' T',
  G, S |-##v v :: typ_all V T ->
  G, S |-# V' <: V ->
  (forall y, y \notin L ->
        G & y ~ V', S |- open_typ y T <: open_typ y T') ->
  G, S |-##v v :: typ_all V' T'
  (* Tight Selection *)
| t_pt_sel_v : forall G S v y A V,
  G, S |-##v v :: V ->
  G, S |-! trm_var y :: typ_rcd (dec_typ A V V) ->
  G, S |-##v v :: typ_sel y A
| t_pt_and_v : forall G S v T U,
  G, S |-##v v :: T ->
  G, S |-##v v :: U ->
  G, S |-##v v :: typ_and T U
  (* Loc *)
| t_pt_loc_v : forall G S v T U,
  G, S |-##v v :: typ_ref T ->
  G, S |-# T <: U ->
  G, S |-# U <: T ->  
  G, S |-##v v :: typ_ref U
  (* Top *)
| t_pt_top_v : forall G S v T,
  G, S |-##v v :: T ->
  G, S |-##v v :: typ_top
where "G ',' S '|-##v' v '::' T" := (tight_pt_v G S v T).

Hint Constructors tight_pt_v.

Lemma tight_possible_types_closure_tight_v: forall G S v T U,
  inert G ->
  G, S |-##v v :: T ->
  G, S |-# T <: U ->
  G, S |-##v v :: U.
Proof.
  introv Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversions HT. inversion H.
  - inversions HT. inversion H. assumption.
  - inversions HT. inversions H. assumption.
  - inversions HT. inversions H.
  - inversions HT. inversions H.
  - inversions HT. inversions H0.
    lets Hb: (inert_unique_tight_bounds Hgd H H6). subst*.
Qed.

Lemma tight_possible_types_lemma_v : forall G S v T,
    inert G ->
    G, S |-# trm_val v :: T ->
    G, S |-##v v :: T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hgd eq_refl).
  apply* tight_possible_types_closure_tight_v.
Qed.
