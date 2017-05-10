Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Wellformed_store.
Require Import Some_lemmas.
Require Import Narrowing.
Require Import Tight_possible_types.
Require Import Inert_types.
Require Import General_to_tight.
Require Import Substitution.

Lemma canonical_forms_1: forall G s x T U,
  G ~~ s ->
  inert G ->
  G |- trm_var (avar_f x) :: typ_all T U ->
  (exists L T' t, binds x (val_lambda T' t) s /\ G |- T <: T' /\
  (forall y, y \notin L -> G & y ~ T |- t |^ y :: U ||^ y)).
Proof.
  introv Hwf Hgd Hty.
  pose proof (general_to_tight_typing Hgd Hty) as Hti.
  pose proof (tight_to_precise_typ_all Hgd Hti) as [S' [T' [L' [Hpt [HSsub HTsub]]]]].
  pose proof (inert_precise_all_inv Hgd Hpt) as Bi.
  pose proof (corresponding_types Hwf Hgd Bi)
    as [[L [S [V [S1 [V1 [t [Hb [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [S [ds [Hb [Ht Heq]]]]].
  subst. inversion Heq; subst. inversions Ht.
  - exists (L \u L' \u L0 \u dom G) S t.
    split; auto.
    pose proof (tight_possible_types_lemma Hgd Hti) as Htp.
    assert (forall y W, y # G -> ok (G & y ~ W)) as Hok by (intros; apply* ok_push).
    inversion Htp; subst.
    + apply (inert_precise_all_inv Hgd) in Hpt.
      apply (inert_precise_all_inv Hgd) in H.
      pose proof (binds_func Hpt H) as H4.
      inversion H4; subst T U; clear H4.
      split. auto. intros y Hy.
      assert (y \notin L0) as Hy0 by auto. assert (y \notin L) as HyL by auto.
      specialize (H3 y Hy0). apply narrow_typing with (G':=G & y ~ S1) in H3.
      apply ty_sub with (T:=V ||^ y).
      assumption. apply* Hs2. apply* subenv_last. apply* Hok.
    + apply tight_to_general in HSsub; auto.
      assert (G |- T <: S) as HTS by (apply* subtyp_trans).
      split; auto. intros y Hy. assert (y \notin L0) as Hy0 by auto.
      specialize (H3 y Hy0).
      apply narrow_typing with (G':=G & y ~ T) in H3. apply ty_sub with (T:=V ||^ y).
      assumption. apply subtyp_trans with (T:=V1 ||^ y).
      assert (y \notin L) as HL by auto.
      specialize (Hs2 y HL). apply narrow_subtyping with (G':=G & y ~ T) in Hs2.
      assumption. apply* subenv_last. apply* Hok.
      apply* HTsub. apply* subenv_last. apply* Hok.
  - inversion Heq.
Qed.
