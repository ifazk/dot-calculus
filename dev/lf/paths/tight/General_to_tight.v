Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Narrowing.
Require Import Inert_types.
Require Import Some_lemmas.
Require Import Tight_possible_types.

(* ###################################################################### *)
(** ** Tight to precise *)

(* Lemma 1 *)
Lemma tight_to_precise_typ_dec: forall G x A S U,
  inert G ->
  G |-# trm_path (p_var (avar_f x)) :: typ_rcd (dec_typ A S U) ->
  exists T,
    G |-! trm_path (p_var (avar_f x)) :: typ_rcd (dec_typ A T T) /\
    G |-# T <: U /\
    G |-# S <: T.
Proof.
  introv HG Ht.
  lets Htp: (tight_possible_types_lemma HG Ht). clear Ht.
  dependent induction Htp.
  - lets Hp: (inert_precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHtp A T U0 HG eq_refl).
    destruct IHHtp as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.

Lemma tight_to_precise_trm_dec: forall G x a m T,
  inert G ->
  G |-# trm_path (p_var (avar_f x)) :: typ_rcd {{ a [m] T }} ->
  exists T',
    G |-! trm_path (p_var (avar_f x)) :: typ_rcd {{ a [m] T' }} /\
    G |-# T' <: T.
Proof.
  introv Hgd Ht.
  lets Htp: (tight_possible_types_lemma Hgd Ht). clear Ht.
  dependent induction Htp.
  - exists T. auto.
  - specialize (IHHtp _ _ Hgd eq_refl). destruct IHHtp as [V [Hx Hs]].
    exists V. split; auto.
    eapply subtyp_trans; eassumption.
Qed.

Lemma tight_to_precise_typ_all: forall G x S T,
  inert G ->
  G |-# trm_path (p_var (avar_f x)) :: typ_all S T ->
  exists S' T' L,
    G |-! trm_path (p_var (avar_f x)) :: typ_all S' T' /\
    G |-# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S |- T' ||^ y <: T ||^ y).
Proof.
  introv HG Ht.
  lets Htp: (tight_possible_types_lemma HG Ht). clear Ht.
  dependent induction Htp.
  - exists S T (dom G); auto.
  - specialize (IHHtp _ _ HG eq_refl).
    destruct IHHtp as [S' [T' [L' [Hpt [HSsub HTsub]]]]].
    exists S' T' (dom G \u L \u L').
    split; auto.
    assert (Hsub2 : G |-# typ_all S0 T0 <: typ_all S T).
    { apply subtyp_all with (L:=L); assumption. }
    split.
    + eapply subtyp_trans; eauto.
    + intros y Fr.
      assert (Hok: ok (G & y ~ S)) by auto using ok_push, inert_ok.
      apply tight_to_general in H; auto.
      assert (Hnarrow: G & y ~ S |- T' ||^ y <: T0 ||^ y).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.

(* Lemma 2 *)
Lemma tight_subtyping_sel: forall G x A S U,
    inert G ->
    G |-# trm_path (p_var (avar_f x)) :: typ_rcd (dec_typ A S U) ->
    G |-# typ_path (p_var (avar_f x)) A <: U /\
    G |-# S <: typ_path (p_var (avar_f x)) A.
Proof.
  introv HG Hty.
  pose proof (tight_to_precise_typ_dec HG Hty) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_t in Ht. apply subtyp_trans_t with (T:=T); auto.
  - apply subtyp_sel2_t in Ht. apply subtyp_trans with (T:=T); auto.
Qed.

(* Theorem 1 *)
Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall G t T,
     G |- t :: T ->
     G = G0 ->
     G |-# t :: T) /\
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
  G |- t :: T ->
  G |-# t :: T.
Proof.
  intros. apply* general_to_tight.
Qed.
