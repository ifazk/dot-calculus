Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inert_types.
Require Import Some_lemmas.
Require Import Narrowing.

(* ###################################################################### *)
(** ** Tight Possible types *)

(*
Definition (Tight Possible types)

For a variable x, environment G, the set TPT(G, x) of simplified possible types
of x defined as v in G is the smallest set SS such that:

If G |-! x:T then T in SS.
If {a:T} in SS and G |-# T<:T' then {a:T'} in SS.
If {A:T..U} in SS, G |-# T'<:T and G |-# U<:U' then {A:T'..U'} in SS.
If S in SS then rec(x: S) in SS.
If all(x: S)T in SS, G |-# S'<:S and G, x: S' |-# T<:T' then all(x: S')T' in SS.
If S1 in SS and S2 in SS then (S1 & S2) in SS.
If S in SS and G |-! y: {A: S..S} then y.A in SS.
 *)

Reserved Notation "G '|-##' p ':' T" (at level 40, p at level 59).

Inductive tight_pt : ctx -> path -> typ -> Prop :=
  (* Precise typing *)
| t_pt_precise : forall G p T,
    G |-! trm_path p : T ->
    G |-## p : T
  (* General term member subtyping *)
| t_pt_dec_trm : forall G p a T T',
    G |-## p : typ_rcd { a [gen] T } ->
    G |-# T <: T' ->
    G |-## p : typ_rcd { a [gen] T' }
  (* Strong term member subtyping *)
| t_pt_dec_trm_strong : forall G p a T,
    G |-## p : typ_rcd { a [strong] T } ->
    G |-## p : typ_rcd { a [gen] T }
  (* Type member subtyping *)
| t_pt_dec_typ : forall G p A T T' U' U,
    G |-## p : typ_rcd { A >: T <: U } ->
    G |-# T' <: T ->
    G |-# U <: U' ->
    G |-## p : typ_rcd { A >: T' <: U' }
  (* Recursive Types *)
| t_pt_bnd : forall G x S,
    G |-## (p_var (avar_f x)) : S ||^ x ->
    G |-## (p_var (avar_f x)) : typ_bnd S
  (* Forall *)
| t_pt_all : forall L G p S T S' T',
    G |-## p : typ_all S T ->
    G |-# S' <: S ->
    (forall y, y \notin L ->
      G & y ~ S' |- T ||^ y <: T' ||^ y) ->
    G |-## p : typ_all S' T'
  (* And *)
| t_pt_and : forall G p S T,
    G |-## p : S ->
    G |-## p : T ->
    G |-## p : typ_and S T
  (* Tight Selection *)
| t_pt_sel : forall G p q A S,
    G |-## p : S ->
    G |-! trm_path q : typ_rcd { A >: S <: S } ->
    norm_t G q ->
    G |-## p : typ_path q A
  (* Top *)
| t_pt_top : forall G p T,
    G |-## p : T ->
    G |-## p : typ_top
where "G '|-##' p ':' T" := (tight_pt G p T).

Hint Constructors tight_pt.

(* ****************************************** *)
(* Invertable to precise *)

Lemma tpt_to_precise_typ_dec: forall G p A S U,
    inert G ->
    norm_t G p ->
    G |-## p : typ_rcd { A >: S <: U } ->
    exists T,
      G |-! trm_path p : typ_rcd { A >: T <: T } /\
      G |-# T <: U /\
      G |-# S <: T.
Proof.
  introv HG Hn Ht.
  dependent induction Ht.
  - lets Hp: (precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHt A T U0 HG Hn eq_refl). destruct IHHt as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.

Lemma tpt_to_precise_trm_dec: forall G p a m T,
    inert G ->
    norm_t G p ->
    G |-## p : typ_rcd { a [m] T } ->
    exists T',
      G |-! trm_path p : typ_rcd { a [m] T' } /\
      G |-# T' <: T.
Proof.
  introv Hi Hn Ht. dependent induction Ht.
  - (* t_pt_precise *)
    exists T. auto.
  - (* t_pt_dec_trm *)
    specialize (IHHt _ _ _ Hi Hn eq_refl). destruct IHHt as [V [Hx Hs]].
    exists V. split; auto.
    eapply subtyp_trans_t; eassumption.
Qed.

Lemma tpt_to_precise_typ_all: forall G p S T,
    inert G ->
    norm_t G p ->
    G |-## p : typ_all S T ->
    exists S' T' L,
      G |-! trm_path p : typ_all S' T' /\
      G |-# S <: S' /\
      (forall y,
          y \notin L ->
              G & y ~ S |- T' ||^ y <: T ||^ y).
Proof.
  introv Hi Hn Ht. dependent induction Ht.
  - exists S T (dom G); auto.
  - specialize (IHHt _ _ Hi Hn eq_refl).
    destruct IHHt as [S' [T' [L' [Hpt [HSsub HTsub]]]]].
    exists S' T' (dom G \u L \u L').
    split; auto.
    assert (Hsub2 : G |-# typ_all S0 T0 <: typ_all S T) by (apply* subtyp_all_t). split.
    + eapply subtyp_trans_t; eauto.
    + intros y Fr.
      assert (Hok: ok (G & y ~ S)) by auto using ok_push, inert_ok.
      apply tight_to_general in H; auto.
      assert (Hnarrow: G & y ~ S |- T' ||^ y <: T0 ||^ y).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.

Lemma invertable_to_tight: forall G p T,
     G |-## p : T ->
     G |-# trm_path p : T.
Proof.
  introv Hi. induction Hi; eauto. apply* precise_to_tight.
Qed.

Lemma tight_possible_types_closure_tight: forall G p T U,
  inert G ->
  G |-## p : T ->
  G |-# T <: U ->
  G |-## p : U.
Proof.
  introv Hi HT Hsub.
  dependent induction Hsub; eauto.
  - inversions HT. false* precise_bot_false.
  - inversion* HT.
  - inversion* HT.
  - inversions HT.
    + false *precise_psel_false.
    + pose proof (inert_unique_tight_bounds Hi H H6). subst. assumption.
Qed.

Lemma term_path_norm_false: forall G x a T,
    inert G ->
    G |-## p_var (avar_f x) : typ_rcd { a [gen] T } ->
    norm_p G (p_sel (p_var (avar_f x)) a) ->
    False.
Proof.
  introv Hi Ht Hn. inversions Hn.
  assert (norm_t G (p_var (avar_f x))) as Hx by admit.
  destruct (tpt_to_precise_trm_dec Hi Hx Ht) as [V [Hp Hs]].
  destruct (p_rcd_unique Hi Hp H1) as [He1 _]. inversion He1.
Qed.

Lemma tight_possible_types_lemma : forall G U p,
    inert G ->
    G |-# trm_path p : U ->
    norm_t G p ->
    G |-## p : U.
Proof.
  introv Hi Hty Hn.
  dependent induction Hty; auto.
  - (* ty_fld_elim_var_t *)
    assert (norm_t G (p_var (avar_f x))) as Hnx. {
      apply tight_to_general in Hty.
      destruct (typing_implies_bound Hty) as [U Hb]. apply* norm_var_t.
    }
    inversions Hn.
    specialize (IHHty (p_var (avar_f x )) Hi eq_refl H4).

  - specialize (IHHty p0  Hi eq_refl). inversions IHHty.
    * apply ty_fld_elim_p in H. auto.
    specialize (IHHty _ Hgd eq_refl eq_refl eq_refl).
    eapply t_pt_bnd.
    apply IHHty.
    reflexivity.
  - specialize (IHHty _ Hgd eq_refl eq_refl eq_refl).
    inversion IHHty; subst; auto.
  - apply t_pt_and; auto.
  - eapply tight_possible_types_closure_tight; auto.
Qed.
