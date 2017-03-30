Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

(* ###################################################################### *)
(** ** Extra Rec *)

Lemma extra_bnd_rules:
  (forall m1 m2 G t T, ty_trm m1 m2 G t T -> forall G1 G2 x S G',
    G = G1 & (x ~ open_typ x S) & G2 ->
    G' = G1 & (x ~ typ_bnd S) & G2 ->
    ty_trm m1 m2 G' t T)
/\ (forall G d D, ty_def G d D -> forall G1 G2 x S G',
    G = G1 & (x ~ open_typ x S) & G2 ->
    G' = G1 & (x ~ typ_bnd S) & G2 ->
    ty_def G' d D)
/\ (forall G ds T, ty_defs G ds T -> forall G1 G2 x S G',
    G = G1 & (x ~ open_typ x S) & G2 ->
    G' = G1 & (x ~ typ_bnd S) & G2 ->
    ty_defs G' ds T)
/\ (forall m1 m2 G T U, subtyp m1 m2 G T U -> forall G1 G2 x S G',
    G = G1 & (x ~ open_typ x S) & G2 ->
    G' = G1 & (x ~ typ_bnd S) & G2 ->
    subtyp m1 m2 G' T U).
Proof.
  apply rules_mutind; intros; eauto.
  - (* ty_var *)
    subst. apply binds_middle_inv in b. destruct b as [Bi | [Bi | Bi]].
    + apply ty_var. eauto.
    + destruct Bi as [Bin [Eqx EqT ]]. subst.
      apply ty_rec_elim. apply ty_var. eauto.
    + destruct Bi as [Bin [Neqx Bi]]. apply ty_var. eauto.
  - (* ty_all_intro *)
    subst.
    apply_fresh ty_all_intro as y; eauto.
    assert (y \notin L) as FrL by eauto.
    specialize (H y FrL).
    specialize (H G1 (G2 & y ~ T) x S).
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
  - (* ty_new_intro *)
    subst.
    apply_fresh ty_new_intro as y; eauto;
    assert (y \notin L) as FrL by eauto.
    specialize (H y FrL).
    specialize (H G1 (G2 & y ~ open_typ y T) x S).
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
  - (* ty_let *)
    subst.
    apply_fresh ty_let as y; eauto.
    assert (y \notin L) as FrL by eauto.
    specialize (H0 y FrL).
    specialize (H0 G1 (G2 & y ~ T) x S).
    eapply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
  - (* subtyp_all *)
    subst.
    apply_fresh subtyp_all as y; eauto.
    assert (y \notin L) as FrL by eauto.
    specialize (H0 y FrL).
    specialize (H0 G1 (G2 & y ~ S2) x S).
    eapply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
Qed.
