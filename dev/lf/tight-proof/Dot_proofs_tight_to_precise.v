Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Dot_definitions.
Require Import Dot_proofs_good_types.
Require Import Dot_proofs_tight_possible_types.

(* ###################################################################### *)
(** ** Tight to precise *)

(* Lemma 1 *)
Lemma tight_to_precise_typ_dec: forall G s x A S U,
  wf_sto G s ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_rcd (dec_typ A S U)) ->
  exists T,
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_typ A T T)) /\
    subtyp ty_general sub_tight G T U /\
    subtyp ty_general sub_tight G S T.
Proof.
  introv Hwf Ht.
  assert (good G) as HG by (apply* wf_good).
  lets Htp: (tight_possible_types_lemma HG Ht). clear Ht.
  dependent induction Htp.
  - lets Hp: (good_precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHtp Hwf HG). destruct IHHtp as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.

(* Lemma 2 *)
Lemma tight_subtyping_sel: forall G s x A S U,
    wf_sto G s ->
    ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_rcd (dec_typ A S U)) ->
    (subtyp ty_general sub_tight G (typ_sel (avar_f x) A) U /\
     subtyp ty_general sub_tight G S (typ_sel (avar_f x) A)).
Proof.
  introv Hwf Hty. 
  lets H: (tight_to_precise_typ_dec Hwf Hty). destruct H as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_tight in Ht. apply subtyp_trans with (T:=T); auto.
  - apply subtyp_sel2_tight in Ht. apply subtyp_trans with (T:=T); auto.
Qed.

(* Theorem 1 *)
Lemma general_to_tight: forall G0 s0,
  wf_sto G0 s0 ->
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     G = G0 ->
     m1 = ty_general ->
     m2 = sub_general ->
     ty_trm ty_general sub_tight G t T) /\
  (forall m1 m2 G S U,
     subtyp m1 m2 G S U ->
     G = G0 ->
     m1 = ty_general ->
     m2 = sub_general ->
     subtyp ty_general sub_tight G S U).
Proof.
  intros G0 s0 Hwf.
  apply ts_mutind; intros; subst; eauto; apply* tight_subtyping_sel.
Qed.
