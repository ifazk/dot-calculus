Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inert_types.

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
    reflexivity.
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

Lemma invertible_typing_lemma_ invertible_typing_lemma_v : forall G v T,
    inert G ->
    G |-# trm_val v : T ->
    G |-##v v : T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hgd eq_refl).
  apply* invertible_typing_closure_tight_v.
Qed.
