Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inert_types.
Require Import Some_lemmas.
Require Import Narrowing.

Lemma invertible_to_precise_typ_dec: forall G x A S U,
  inert G ->
  G |-## x : typ_rcd (dec_typ A S U) ->
  exists T,
    G |-! trm_var (avar_f x) : typ_rcd (dec_typ A T T) /\
    G |-# T <: U /\
    G |-# S <: T.
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - lets Hp: (precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHinv A T U0 HG eq_refl).
    destruct IHHinv as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.

Lemma invertible_to_precise_trm_dec: forall G x a T,
  inert G ->
  G |-## x : typ_rcd (dec_trm a T) ->
  exists T',
    G |-! trm_var (avar_f x) : typ_rcd (dec_trm a T') /\
    G |-# T' <: T.
Proof.
  introv Hgd Hinv.
  dependent induction Hinv.
  - exists T. auto.
  - specialize (IHHinv _ _ Hgd eq_refl). destruct IHHinv as [V [Hx Hs]].
    exists V. split; auto.
    eapply subtyp_trans_t; eassumption.
Qed.

Lemma invertible_to_precise_typ_all: forall G x S T,
  inert G ->
  G |-## x : typ_all S T ->
  exists S' T' L,
    G |-! trm_var (avar_f x) : typ_all S' T' /\
    G |-# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S |- open_typ y T' <: open_typ y T).
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - exists S T (dom G); auto.
  - specialize (IHHinv _ _ HG eq_refl).
    destruct IHHinv as [S' [T' [L' [Hpt [HSsub HTsub]]]]].
    exists S' T' (dom G \u L \u L').
    split; auto.
    assert (Hsub2 : G |-# typ_all S0 T0 <: typ_all S T).
    { apply subtyp_all_t with (L:=L); assumption. }
    split.
    + eapply subtyp_trans_t; eauto.
    + intros y Fr.
      assert (Hok: ok (G & y ~ S)) by auto using ok_push, inert_ok.
      apply tight_to_general in H; auto.
      assert (Hnarrow: G & y ~ S |- open_typ y T' <: open_typ y T0).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.

Lemma invertible_typing_closure_tight: forall G x T U,
  inert G ->
  G |-## x : T ->
  G |-# T <: U ->
  G |-## x : U.
Proof.
  intros G x T U Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversion HT.
    destruct (precise_bot_false Hgd H).
  - inversion HT; auto. apply ty_and1_p in H. auto.
  - inversion HT; auto. apply ty_and2_p in H. auto.
  - inversions HT.
    + false* precise_psel_false.
    + pose proof (inert_unique_tight_bounds Hgd H H5) as Hu. subst. assumption.
Qed.

Lemma invertible_typing_lemma :
  forall G U x,
    inert G ->
    G |-# trm_var (avar_f x) : U ->
    G |-## x : U.
Proof.
  intros G U x Hgd Hty.
  dependent induction Hty.
  - auto.
  - specialize (IHHty _ Hgd eq_refl).
    eapply ty_bnd_inv.
    apply IHHty.
  - specialize (IHHty _ Hgd eq_refl).
    inversion IHHty; subst; auto.
  - apply ty_and_inv; auto.
  - eapply invertible_typing_closure_tight; auto.
Qed.

Lemma invertible_typing_closure_tight_v: forall G v T U,
  inert G ->
  G |-##v v : T ->
  G |-# T <: U ->
  G |-##v v : U.
Proof.
  introv Hgd HT Hsub.
  dependent induction Hsub; eauto; inversions HT; auto; try solve [inversion* H].
  - inversions H0.
  - lets Hb: (inert_unique_tight_bounds Hgd H H5). subst*.
Qed.

Lemma invertible_typing_lemma_v : forall G v T,
    inert G ->
    G |-# trm_val v : T ->
    G |-##v v : T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hgd eq_refl).
  apply* invertible_typing_closure_tight_v.
Qed.
