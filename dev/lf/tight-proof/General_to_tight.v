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
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_rcd (dec_typ A S U)) ->
  exists T,
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_typ A T T)) /\
    subtyp sub_tight G T U /\
    subtyp sub_tight G S T.
Proof.
  introv HG Ht.
  lets Htp: (tight_possible_types_lemma HG Ht). clear Ht.
  dependent induction Htp.
  - lets Hp: (precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHtp A T U0 HG eq_refl).
    destruct IHHtp as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.

Lemma tight_to_precise_trm_dec: forall G x a T,
  inert G ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_rcd (dec_trm a T)) ->
  exists T',
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_trm a T')) /\
    subtyp sub_tight G T' T.
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
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_all S T) ->
  exists S' T' L,
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_all S' T') /\
    subtyp sub_tight G S S' /\
    (forall y,
        y \notin L ->
            subtyp sub_general (G & y ~ S) (open_typ y T') (open_typ y T))
    .
Proof.
  introv HG Ht.
  lets Htp: (tight_possible_types_lemma HG Ht). clear Ht.
  dependent induction Htp.
  - exists S T (dom G); auto.
  - specialize (IHHtp _ _ HG eq_refl).
    destruct IHHtp as [S' [T' [L' [Hpt [HSsub HTsub]]]]].
    exists S' T' (dom G \u L \u L').
    split; auto.
    assert (Hsub2 : subtyp sub_tight G (typ_all S0 T0) (typ_all S T)).
    { apply subtyp_all with (L:=L); assumption. }
    split.
    + eapply subtyp_trans; eauto.
    + intros y Fr.
      assert (Hok: ok (G & y ~ S)) by auto using ok_push, inert_ok.
      apply tight_to_general in H; auto.
      assert (Hnarrow: subtyp sub_general (G & y ~ S) (open_typ y T') (open_typ y T0)).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.

(* Lemma 2 *)
Lemma tight_subtyping_sel: forall G x A S U,
    inert G ->
    ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_rcd (dec_typ A S U)) ->
    (subtyp sub_tight G (typ_sel (avar_f x) A) U /\
     subtyp sub_tight G S (typ_sel (avar_f x) A)).
Proof.
  introv HG Hty.
  pose proof (tight_to_precise_typ_dec HG Hty) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_tight in Ht. apply subtyp_trans with (T:=T); auto.
  - apply subtyp_sel2_tight in Ht. apply subtyp_trans with (T:=T); auto.
Qed.

(* Theorem 1 *)
Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     G = G0 ->
     m1 = ty_general ->
     m2 = sub_general ->
     ty_trm ty_general sub_tight G t T) /\
  (forall m2 G S U,
     subtyp m2 G S U ->
     G = G0 ->
     m2 = sub_general ->
     subtyp sub_tight G S U).
Proof.
  intros G0 HG.
  apply ts_mutind; intros; subst; try solve [eapply tight_subtyping_sel; auto]; eauto.
Qed.

Lemma general_to_tight_typing: forall G t T,
  inert G ->
  ty_trm ty_general sub_general G t T ->
  ty_trm ty_general sub_tight G t T.
Proof.
  intros. apply* general_to_tight.
Qed.
