Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import Narrowing.
Require Import Helper_lemmas.
Require Import Precise_types.
Require Import Invertible_typing.
Require Import General_to_tight.
Require Import Wellformed_store.

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
  destruct (precise_forall_inv Htp) as [t Heq].
  subst. inversions Htp.
  exists (L0 \u L \u (dom G)) T' t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H1 y HL0).
  eapply ty_sub; eauto. eapply narrow_typing in H1; eauto.
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
  destruct (corresponding_types' Hwf Hin BiG) as [v [Bis Ht]].
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
