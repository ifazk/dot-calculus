Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Wellformed_store.
Require Import Some_lemmas.
Require Import Narrowing.
Require Import Invertible_typing.
Require Import Inert_types.
Require Import General_to_tight.
Require Import Substitution.

Lemma canonical_forms_1: forall G S sta sto x T U,
  G, S |~ sta, sto ->
  inert G ->
  G, S |- trm_var (avar_f x) : typ_all T U ->
  (exists L T' t, 
      binds x (val_lambda T' t) sta /\
      G, S |- T <: T' /\
      (forall y, y \notin L -> G & y ~ T, S |- open_trm y t : open_typ y U)).
Proof.
  introv Hwf Hgd Hty.
  pose proof (general_to_tight_typing Hgd Hty) as Hti.
  pose proof (invertible_typing_lemma Hgd Hti) as Hinv.
  pose proof (invertible_to_precise_typ_all Hgd Hinv) as [T' [U' [L' [Hpt [HSsub HTsub]]]]].
  pose proof (inert_precise_all_inv Hgd Hpt) as Bi.
  pose proof (corresponding_types Hwf Hgd Bi)
    as [[L [V [W [V1 [W1 [t [Hb [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [[V [ds [Hb [Ht Heq]]]] | [V [V' [l [Hb [Ht [Heq [Hs1 Hs2]]]]]]]]].
  subst. inversion Heq; subst. inversions Ht.
  - exists (L \u L' \u L0 \u dom G) V t.
    split; auto.
    assert (forall y W, y # G -> ok (G & y ~ W)) as Hok by (intros; apply* ok_push).
    inversion Hinv; subst.
    + apply (inert_precise_all_inv Hgd) in Hpt.
      apply (inert_precise_all_inv Hgd) in H.
      pose proof (binds_func Hpt H) as H5.
      inversion H5; subst T U; clear H5.
      split. auto. intros y Hy.
      assert (y \notin L0) as Hy0 by auto. assert (y \notin L) as HyL by auto.

      specialize (H2 y Hy0). apply narrow_typing with (G':=G & y ~ V1) in H2.
      apply ty_sub with (T:=open_typ y W).
      assumption. apply* Hs2. apply* subenv_last. apply* Hok.
    + apply tight_to_general in HSsub; auto.
      assert (G, S |- T <: V) as HTV by (apply* subtyp_trans).
      split; auto. intros y Hy. assert (y \notin L0) as Hy0 by auto.
      specialize (H2 y Hy0).
      apply narrow_typing with (G':=G & y ~ T) in H2. apply ty_sub with (T:=open_typ y W).
      assumption. apply subtyp_trans with (T:=open_typ y W1).
      assert (y \notin L) as HL by auto.
      specialize (Hs2 y HL). apply narrow_subtyping with (G':=G & y ~ T) in Hs2.
      assumption. apply* subenv_last. apply* Hok.
      apply* HTsub. apply* subenv_last. apply* Hok.
  - inversion Heq.
  - destruct Heq as [Heq | Heq]; inversion Heq.
Qed.
