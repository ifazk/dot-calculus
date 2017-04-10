Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Wellformed_store.
Require Import Some_lemmas.
Require Import Narrowing.
Require Import Tight_possible_types.
Require Import Good_types.
Require Import General_to_tight.
Require Import Substitution.

(*
Lemma (Canonical forms 1)
If G ~ s and G |- x: all(x: T)U then s(x) = lambda(x: T')t where G |- T <: T' and G, x: T |- t: U.
 *)

Lemma canonical_forms_1: forall G s x T U,
  wf_sto G s ->
  good G ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_all T U) ->
  (exists L T' t, binds x (val_lambda T' t) s /\ subtyp ty_general sub_general G T T' /\
  (forall y, y \notin L -> ty_trm ty_general sub_general (G & y ~ T) (open_trm y t) (open_typ y U))).
Proof.
  introv Hwf Hgd Hty.
  pose proof (general_to_tight_typing Hgd Hty) as Hti.
  pose proof (tight_to_precise_typ_all Hgd Hti) as [S' [T' [L' [Hpt [HSsub HTsub]]]]].
  pose proof (good_precise_all_inv Hgd Hpt) as Bi.
  pose proof (corresponding_types Hwf Hgd Bi)
    as [[L [S [V [S1 [V1 [t [Hb [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [S [ds [Hb [Ht Heq]]]]].
  subst. inversion Heq; subst. inversions Ht.
  - exists (L \u L' \u L0 \u dom G) S t.
    split; auto.
    pose proof (tight_possible_types_lemma Hgd Hti) as Htp.
    assert (forall y W, y # G -> ok (G & y ~ W)) as Hok by (intros; apply* ok_push).
    inversion Htp; subst.
    + apply (good_precise_all_inv Hgd) in Hpt.
      apply (good_precise_all_inv Hgd) in H.
      pose proof (binds_func Hpt H) as H4.
      inversion H4; subst T U; clear H4.
      split. auto. intros y Hy.
      assert (y \notin L0) as Hy0 by auto. assert (y \notin L) as HyL by auto.
      specialize (H3 y Hy0). apply narrow_typing with (G':=G & y ~ S1) in H3.
      apply ty_sub with (T:=open_typ y V). intro Contra. inversion Contra.
      assumption. apply* Hs2. apply* subenv_last. apply* Hok.
    + apply tight_to_general in HSsub; auto.
      assert (subtyp ty_general sub_general G T S) as HTS by (apply* subtyp_trans).
      split; auto. intros y Hy. assert (y \notin L0) as Hy0 by auto.
      specialize (H3 y Hy0).
      apply narrow_typing with (G':=G & y ~ T) in H3. apply ty_sub with (T:=open_typ y V).
      intro Contra. inversion Contra. assumption. apply subtyp_trans with (T:=open_typ y V1).
      assert (y \notin L) as HL by auto.
      specialize (Hs2 y HL). apply narrow_subtyping with (G':=G & y ~ T) in Hs2.
      assumption. apply* subenv_last. apply* Hok.
      apply* HTsub. apply* subenv_last. apply* Hok.
  - pose proof (H (eq_refl _)) as [? Contra]; inversion Contra.
  - inversion Heq.
Qed.
