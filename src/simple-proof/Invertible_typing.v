Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inert_types.

Lemma invertible_typing_closure_tight: forall G S x T U,
  inert G ->
  G, S |-## x : T ->
  G, S |-# T <: U ->
  G, S |-## x : U.
Proof.
  intros G S x T U Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversion HT.
    destruct (precise_bot_false Hgd H).
  - inversion HT; auto. apply ty_and1_p in H. auto.
  - inversion HT; auto. apply ty_and2_p in H. auto.
  - inversions HT.
    + false* precise_psel_false.
    + pose proof (inert_unique_tight_bounds Hgd H H6) as Hu. subst. assumption.
Qed.

Lemma invertible_typing_lemma : forall G S U x,
    inert G ->
    G, S |-# trm_var (avar_f x) : U ->
    G, S |-## x : U.
Proof.
  intros G S U x Hgd Hty.
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

Lemma invertible_typing_closure_tight_v: forall G S v T U,
  inert G ->
  G, S |-##v v : T ->
  G, S |-# T <: U ->
  G, S |-##v v : U.
Proof.
  introv Hgd Ht Hsub.
  dependent induction Hsub; eauto; inversions Ht; auto; try solve [inversion* H].
  - inversions H0. 
  - lets Hb: (inert_unique_tight_bounds Hgd H H6). subst*.
Qed.

Lemma invertible_typing_lemma_v : forall G S v T,
    inert G ->
    G, S |-# trm_val v : T ->
    G, S |-##v v : T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hgd eq_refl).
  apply* invertible_typing_closure_tight_v.
Qed.
