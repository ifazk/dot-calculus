Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Narrowing.
Require Import Inert_types.
Require Import Some_lemmas.
Require Import Invertible_typing.

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
            G & y ~ S |- open_typ y T' <: open_typ y T)
    .
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

(* Lemma 2 *)
Lemma tight_subtyping_sel: forall G x A S U,
    inert G ->
    G |-# trm_var (avar_f x) : typ_rcd (dec_typ A S U) ->
    (G |-# typ_sel (avar_f x) A <: U /\
     G |-# S <: typ_sel (avar_f x) A).
Proof.
  introv HG Hty.
  pose proof (invertible_typing_lemma HG Hty) as Hinv.
  pose proof (invertible_to_precise_typ_dec HG Hinv) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_t in Ht. apply subtyp_trans_t with (T:=T); auto.
  - apply subtyp_sel2_t in Ht. apply subtyp_trans_t with (T:=T); auto.
Qed.

(* Theorem 1 *)
Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall G t T,
     G |- t : T ->
     G = G0 ->
     G |-# t : T) /\
  (forall G S U,
     G |- S <: U ->
     G = G0 ->
     G |-# S <: U).
Proof.
  intros G0 HG.
  apply ts_mutind; intros; subst; try solve [eapply tight_subtyping_sel; auto]; eauto.
Qed.

Lemma general_to_tight_typing: forall G t T,
  inert G ->
  G |- t : T ->
  G |-# t : T.
Proof.
  intros. apply* general_to_tight.
Qed.
