Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Wellformed_store.
Require Import Has_member.
Require Import Some_lemmas.
Require Import Precise_flow.

(* ###################################################################### *)
(** ** Good types *)

(* Definition (Good types)

A type is good if it of the form
  all(x: S)T
  rec(x: T), where T is a record type
 *)

Inductive good_typ : typ -> Prop :=
  | good_typ_all : forall S T, good_typ (typ_all S T) (* all(x: S)T *)
  | good_typ_bnd : forall T,
      (* a record type is ands of record decs *)
      record_type T ->
      good_typ (typ_bnd T). (* rec(x:T) *)

(* Definition (Good context)

A context is good if it is of the form
  {}
  G, x : T where G is a good context and T is a good type *)

Inductive good : ctx -> Prop :=
  | good_empty : good empty
  | good_all : forall pre x T,
      good pre ->
      good_typ T ->
      x # pre ->
      good (pre & x ~ T).

Lemma wf_good : forall G s, wf_sto G s -> good G.
Proof.
  intros. induction H.
  - apply good_empty.
  - apply good_all.
    + assumption.
    + dependent induction H2.
      * apply good_typ_all.
      * apply good_typ_bnd. pick_fresh z. apply open_record_type_rev with (x:=z); auto.
        apply record_defs_typing with (G:=G & z ~ open_typ z T) (ds:= open_defs z ds); auto.
      * assert (ty_precise = ty_precise) by reflexivity. apply H4 in H5.
        destruct H5. inversion H5.
    + assumption.
Qed.

(* Good contexts bind good:
If G |- x : T and G is a good context then T is a good type. *)

Lemma binds_good : forall G x T,
    binds x T G ->
    good G ->
    good_typ T.
Proof.
  introv Bi Hgood. induction Hgood.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi).
    + destruct H1. subst. assumption.
    + destruct H1. apply (IHHgood H2).
Qed.

Lemma good_binds : forall G x T,
    good G ->
    binds x T G ->
    good_typ T.
Proof.
  introv Bi Hgd.
  eapply binds_good; eauto.
Qed.

Lemma good_typ_bnd_record : forall G x T,
    good G ->
    binds x (typ_bnd T) G ->
    record_type T.
Proof.
  introv Bi Hgd.
  pose proof (good_binds Bi Hgd).
  dependent induction H.
  assumption.
Qed.

Lemma good_unique_tight_bounds' : forall G x T T1 T2 A,
    good_typ T ->
    precise_flow x G T (typ_rcd (dec_typ A T1 T1)) ->
    precise_flow x G T (typ_rcd (dec_typ A T2 T2)) ->
    T1 = T2.
Proof.
  introv Hgt Hpf1 Hpf2.
  induction Hgt.
  - apply precise_flow_all_inv in Hpf1.
    inversion Hpf1.
  - apply (record_unique_tight_bounds H Hpf1 Hpf2).
Qed.

Lemma good_unique_tight_bounds: forall G x T1 T2 A,
  good G ->
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_typ A T1 T1)) ->
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_typ A T2 T2)) ->
  T1 = T2.
Proof.
  introv Hgd Hty1 Hty2.
  assert (exists T, binds x T G) as Bi. {
    eapply typing_implies_bound. eassumption.
  }
  destruct Bi as [T Bi].
  pose proof (good_binds Hgd Bi) as Hgt.
  pose proof (precise_flow_lemma Bi Hty1) as H1.
  pose proof (precise_flow_lemma Bi Hty2) as H2.
  apply (good_unique_tight_bounds' Hgt H1 H2).
Qed.

Lemma good_precise_bot : forall T G x,
    good G ->
    binds x T G ->
    precise_flow x G T typ_bot ->
    False.
Proof.
  intros T G x Hgd Bis Hpf.
  pose proof (binds_good Bis Hgd) as Hgtyp.
  induction Hgtyp.
  - apply precise_flow_all_inv in Hpf.
    inversion Hpf.
  - dependent induction Hpf.
    + pose proof (precise_flow_bnd_inv H Hpf) as H1.
      unfold open_typ in x.
      assert (U = typ_bot) as Hb. {
        induction U; inversions x. reflexivity.
      } subst. destruct H as [ls H]. inversion H.
    + pose proof (precise_flow_bnd_inv'' H Hpf) as H1.
      destruct H1 as [[U' [H11 H12]] | [ls H1]]; try false.
      inversion H1. inversion H3.
    + pose proof (precise_flow_bnd_inv'' H Hpf) as H1.
      destruct H1 as [[U' [H11 H12]] | [ls H1]]; try false.
      inversion H1.
Qed.

Lemma good_ty_precise_bot' : forall T G x,
    good G ->
    binds x T G ->
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) typ_bot ->
    False.
Proof.
  intros.
  pose proof (precise_flow_lemma H0 H1) as H2.
  eapply good_precise_bot; eauto.
Qed.

Lemma good_ty_precise_bot : forall G x,
    good G ->
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) typ_bot ->
    False.
Proof.
  intros.
  pose proof (typing_implies_bound H0) as [T HT].
  apply (good_ty_precise_bot' H HT H0).
Qed.

Lemma good_precise_sel_inv : forall G x y A,
    good G ->
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_sel y A) ->
    False.
Proof.
  introv Hgd Hpt.
  pose proof (typing_implies_bound Hpt) as [T Bis].
  pose proof (good_binds Hgd Bis) as Hgt.
  pose proof (precise_flow_lemma Bis Hpt) as Hpf.
  induction Hgt.
  - apply (precise_flow_all_inv) in Hpf.
    inversion Hpf.
  - pose proof (precise_flow_bnd_inv'' H Hpf) as [[U [Contra H1]] | [ls Contra]]; inversion Contra.
Qed.

Lemma good_precise_dec_implies_record_dec : forall G x D,
    good G ->
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd D) ->
    record_dec D.
Proof.
  introv Hgd Hpt.
  pose proof (typing_implies_bound Hpt) as [T' Bis].
  pose proof (good_binds Hgd Bis) as Hgt.
  pose proof (precise_flow_lemma Bis Hpt) as Hpf.
  induction Hgt.
  - apply (precise_flow_all_inv) in Hpf.
    inversion Hpf.
  - apply (record_precise_dec_implies_record_dec H Hpf).
Qed.

Lemma good_precise_dec_typ_inv : forall G x A S U,
    good G ->
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_typ A S U)) ->
    S = U.
Proof.
  introv Hgd Hpt.
  pose proof (good_precise_dec_implies_record_dec Hgd Hpt) as Hrec.
  inversion Hrec.
  reflexivity.
Qed.

Lemma good_precise_flow_all_inv : forall x G S T U,
    good G ->
    precise_flow x G U (typ_all S T) ->
    U = (typ_all S T).
Proof.
  introv Hgd Hpf.
  pose proof (precise_flow_implies_bound Hpf) as Bis.
  pose proof (good_binds Hgd Bis) as Hgt.
  dependent induction Hgt.
  - symmetry. eapply precise_flow_all_inv. eassumption.
  - pose proof (precise_flow_bnd_inv'' H Hpf) as [ [? [Contra _]] | [? Contra]]; inversion Contra.
Qed.

Lemma good_precise_all_inv : forall x G S T,
    good G ->
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_all S T) ->
    binds x (typ_all S T) G.
Proof.
  introv Hgd Htyp.
  pose proof (typing_implies_bound Htyp) as [U Bi].
  pose proof (precise_flow_lemma Bi Htyp) as Hpf.
  pose proof (good_precise_flow_all_inv Hgd Hpf) as H.
  rewrite <- H.
  assumption.
Qed.

Lemma good_ok : forall G,
    good G ->
    ok G.
Proof.
  intros G HG. induction G using env_ind.
  auto.
  inversions HG. false* empty_push_inv.
  destruct (eq_push_inv H) as [Hx [HT HG]]. subst.
  apply* ok_push.
Qed.
