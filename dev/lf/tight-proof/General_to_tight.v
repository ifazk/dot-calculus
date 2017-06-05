Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Narrowing.
Require Import Inert_types.
Require Import Some_lemmas.
Require Import Invertible_typing.

(* ###################################################################### *)
(** ** Tight to precise *)

(* Lemma 1 *)
Lemma tight_to_precise_typ_dec: forall G S x A V U,
  inert G ->
  G, S |-# trm_var (avar_f x) : typ_rcd (dec_typ A V U) ->
  exists T,
    G, S |-! trm_var (avar_f x) : typ_rcd (dec_typ A T T) /\
    G, S |-# T <: U /\
    G, S |-# V <: T.
Proof.
  introv HG Ht.
  lets Hinv: (invertible_typing_lemma HG Ht). clear Ht.
  dependent induction Hinv.
  - lets Hp: (precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHinv A T U0 HG eq_refl). 
    destruct IHHinv as [W [Hx [Hs1 Hs2]]].
    exists W. split*.
Qed.

Lemma tight_to_precise_trm_dec: forall G S x a T,
  inert G ->
  G, S |-# trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
  exists T',
    G, S |-! trm_var (avar_f x) : typ_rcd (dec_trm a T') /\
    G, S |-# T' <: T.
Proof.
  introv Hgd Ht.
  lets Hinv: (invertible_typing_lemma Hgd Ht). clear Ht.
  dependent induction Hinv.
  - exists T. auto.
  - specialize (IHHinv _ _ Hgd eq_refl). destruct IHHinv as [V [Hx Hs]].
    exists V. split; auto.
    eapply subtyp_trans_t; eassumption.
Qed.

Lemma tight_to_precise_typ_all: forall G S x V T,
  inert G ->
  G, S |-# trm_var (avar_f x) : typ_all V T ->
  exists V' T' L,
    G, S |-! trm_var (avar_f x) : typ_all V' T' /\
    G, S |-# V <: V' /\
    (forall y,
        y \notin L ->
            G & y ~ V, S |- open_typ y T' <: open_typ y T).
Proof.
  introv HG Ht.
  lets Hinv: (invertible_typing_lemma HG Ht). clear Ht.
  dependent induction Hinv.
  - exists V T (dom G); auto.
  - specialize (IHHinv _ _ HG eq_refl).
    destruct IHHinv as [V' [T' [L' [Hpt [HSsub HTsub]]]]].
    exists V' T' (dom G \u L \u L').
    split; auto.
    assert (Hsub2 : G, S |-# typ_all V0 T0 <: typ_all V T).
    { apply subtyp_all_t with (L:=L); assumption. }
    split.
    + eapply subtyp_trans_t; eauto.
    + intros y Fr.
      assert (Hok: ok (G & y ~ V)) by auto using ok_push, inert_ok.
      apply tight_to_general in H; auto.
      assert (Hnarrow: G & y ~ V, S |- open_typ y T' <: open_typ y T0).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.

Lemma tight_to_precise_typ_ref: forall G S x T,
  inert G ->
  G, S |-# trm_var (avar_f x) : typ_ref T ->
  exists T',
    G, S |-! trm_var (avar_f x) : typ_ref T' /\
    G, S |-# T' <: T /\
    G, S |-# T <: T'.
Proof.
  introv Hg Ht.
  lets Htp: (invertible_typing_lemma Hg Ht). clear Ht.
  dependent induction Htp.
  - exists T. split*.
  - specialize (IHHtp T0 Hg eq_refl). 
    destruct IHHtp as [U [Hx Hs]]. exists U. split*.
Qed.

(* Lemma 2 *)
Lemma tight_subtyping_sel: forall G S x A V U,
    inert G ->
    G, S |-# trm_var (avar_f x) : typ_rcd (dec_typ A V U) ->
       (G, S |-# typ_sel (avar_f x) A <: U /\
        G, S |-# V <: typ_sel (avar_f x) A).
Proof.
  introv HG Hty.
  pose proof (tight_to_precise_typ_dec HG Hty) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_t in Ht. apply subtyp_trans_t with (T:=T); auto.
  - apply subtyp_sel2_t in Ht. apply subtyp_trans_t with (T:=T); auto.
Qed.

(* Theorem 1 *)
Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall G S t T,
     G, S |- t : T ->
     G = G0 ->
     G, S |-# t : T) /\
  (forall G S V U,
     G, S |- V <: U ->
     G = G0 ->
     G, S |-# V <: U).
Proof.
  intros G0 HG.
  apply ts_mutind; intros; subst; try solve [eapply tight_subtyping_sel; auto]; eauto.
Qed.

Lemma general_to_tight_typing: forall G S t T,
  inert G ->
  G, S |- t : T ->
  G, S |-# t : T.
Proof.
  intros. apply* general_to_tight.
Qed.
