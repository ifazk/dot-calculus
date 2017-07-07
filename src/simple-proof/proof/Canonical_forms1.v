Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Narrowing.
Require Import Helper_lemmas.
Require Import Precise_types.
Require Import Invertible_typing.
Require Import General_to_tight.
Require Import Wellformed_store.

Lemma invertible_val_to_precise_lambda: forall G v S T,
    G |-##v v : typ_all S T ->
    inert G ->
    exists L S' T',
      G |-! trm_val v : typ_all S' T' /\
      G |- S <: S' /\
      (forall y, y \notin L ->
                 G & y ~ S |- open_typ y T' <: open_typ y T).
Proof.
  introv Ht Hg. dependent induction Ht.
  - exists (dom G) S T. split*.
  - destruct (IHHt S0 T0 eq_refl Hg) as [L' [S1 [T1 [Hp [Hss Hst]]]]].
    exists (L \u L' \u dom G) S1 T1. split. assumption. split. apply subtyp_trans with (T:=S0).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ S)) as Hok. {
      apply* ok_push.
    }
    apply subtyp_trans with (T:=open_typ y T0).
    eapply narrow_subtyping. apply* Hst. apply subenv_last. apply* tight_to_general.
    assumption. assumption.
    apply* H0.
Qed.

Lemma var_typ_all_to_binds: forall G x T U,
    inert G ->
    G |- trm_var (avar_f x) : typ_all T U ->
    (exists L T' U',
        binds x (typ_all T' U') G /\
        G |- T <: T' /\
        (forall y, y \notin L -> G & y ~ T |- (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_all (inert_ok Hin) Hinv) as [T' [U' [L [Htp [Hs1 Hs2]]]]].
  exists L T' U'. repeat split.
  - apply~ inert_precise_all_inv.
  - apply~ tight_to_general.
  - assumption.
Qed.

Lemma val_typ_all_to_lambda: forall G v T U,
    inert G ->
    G |- (trm_val v) : typ_all T U ->
    (exists L T' t,
        v = val_lambda T' t /\
        G |- T <: T' /\
        (forall y, y \notin L -> G & y ~ T |- (open_trm y t) : open_typ y U)).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible_v Hin Htt).
  destruct (invertible_val_to_precise_lambda Hinv Hin) as [L [T' [U' [Htp [Hs1 Hs2]]]]].
  inversions Htp.
  exists (L0 \u L \u (dom G)) T' t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H2 y HL0).
  eapply ty_sub; eauto. eapply narrow_typing in H2; eauto.
  apply~ subenv_last.
Qed.

(*
Lemma (Canonical forms 1)
If G ~ s and G |- x: all(x: T)U then s(x) = lambda(x: T')t where G |- T <: T' and G, x: T |- t: U.
 *)

Lemma canonical_forms_1: forall G s x T U,
  G ~~ s ->
  inert G ->
  G |- trm_var (avar_f x) : typ_all T U ->
  (exists L T' t, binds x (val_lambda T' t) s /\ G |- T <: T' /\
  (forall y, y \notin L -> G & y ~ T |- open_trm y t : open_typ y U)).
Proof.
  introv Hwf Hin Hty.
  destruct (var_typ_all_to_binds Hin Hty) as [L [S [T' [BiG [Hs1 Hs2]]]]].
  destruct (corresponding_types Hwf Hin BiG) as [v [Bis Ht]].
  destruct (val_typ_all_to_lambda Hin Ht) as [L' [S' [t [Heq [Hs1' Hs2']]]]].
  subst.
  exists (L \u L' \u (dom G)) S' t. repeat split~.
  - eapply subtyp_trans; eauto.
  - intros.
    assert (HL: y \notin L) by auto.
    assert (HL': y \notin L') by auto.
    specialize (Hs2 y HL).
    specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    + eapply ty_sub; eauto.
    + apply~ subenv_last.
Qed.
