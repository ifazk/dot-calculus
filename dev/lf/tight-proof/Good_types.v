Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inductive_opens.
Require Import Wellformed_store.
Require Import Has_member.
Require Import Some_lemmas.
Require Import Precise_flow.
Require Import Tight_bound_completeness.

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
    + destruct H0. subst. assumption.
    + destruct H0. apply (IHHgood H1).
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

Lemma binds_typ_bnd_precise : forall G x T,
    binds x (typ_bnd T) G ->
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_bnd T).
Proof.
  introv Bi.
  auto.
Qed.

Lemma good_binds_bot : forall G x,
    good G ->
    binds x typ_bot G ->
    False.
Proof.
  intros G x Hgd Hbd.
  apply binds_good in Hbd.
  - inversion Hbd.
  - assumption.
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
      rewrite open_typ_rewrite' in x.
      inversion x.
      rewrite H1 in H. rewrite <- H4 in H.
      destruct H as [ls H]. inversion H.
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
  - eapply precise_flow_all_inv'. eassumption.
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

(* ###################################################################### *)
(** ** Good Has Member *)

Lemma good_has_member_tightness: forall G x T A S U,
  good G ->
  binds x (typ_bnd T) G ->
  has_member G x (typ_bnd T) A S U ->
  S = U.
Proof.
  introv Hgd Bis Hmem.
  assert (record_type T) as Htype. {
    eapply good_typ_bnd_record; eauto.
  }
  assert (record_type (open_typ x T)) as Htypex. {
    apply open_record_type. assumption.
  }
  assert (has_member G x (open_typ x T) A S U) as Hmemx. {
    inversion Hmem; subst. inversion H0; subst. assumption.
  }
  assert (record_sub (open_typ x T) (typ_rcd (dec_typ A S U))) as Hsub. {
    destruct has_member_rcd_typ_sub_mut as [HL _].
    eapply HL; eauto.
  }
  eapply rcd_typ_eq_bounds. eapply Htypex. eapply Hsub.
Qed.

Lemma good_has_member_covariance: forall G T1 T2 x A S2 U2,
  good G ->
  subtyp ty_general sub_tight G T1 T2 ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) T1 ->
  has_member G x T2 A S2 U2 ->
  exists S1 U1, has_member G x T1 A S1 U1 /\
                subtyp ty_general sub_tight G S2 S1 /\
                subtyp ty_general sub_tight G U1 U2.
Proof.
  introv Hgd Hsub Hty Hmem.
  generalize dependent U2.
  generalize dependent S2.
  dependent induction Hsub; subst; intros.
  - (* top *)
    inversion Hmem; subst. inversion H0.
  - (* bot *)
    exists S2 U2. split.
    apply has_any. assumption. apply has_bot.
    split; apply subtyp_refl.
  - (* refl *)
    exists S2 U2. eauto.
  - (* trans *)
    assert (ty_trm ty_general sub_tight G (trm_var (avar_f x)) T) as HS. {
      eapply ty_sub. intros Hp. subst. eexists; eauto.
      eapply Hty.
      eassumption.
    }
    specialize (IHHsub2 Hgd HS S2 U2 Hmem).
    destruct IHHsub2 as [S3 [U3 [Hmem3 [Hsub31 Hsub32]]]].
    specialize (IHHsub1 Hgd Hty S3 U3 Hmem3).
    destruct IHHsub1 as [S1 [U1 [Hmem1 [Hsub11 Hsub12]]]].
    exists S1 U1. split. apply Hmem1. split; eauto.
  - (* and11 *)
    exists S2 U2. split.
    inversion Hmem; subst. apply has_any. assumption. eapply has_and1. assumption.
    split; eauto.
  - (* and12 *)
    exists S2 U2. split.
    inversion Hmem; subst. apply has_any. assumption. eapply has_and2. assumption.
    split; eauto.
  - (* and2 *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1 [T2 [Heq [Hmem | Hmem]]]]; inversions Heq.
      * specialize (IHHsub1 Hgd Hty S2 U2 Hmem). apply IHHsub1.
      * specialize (IHHsub2 Hgd Hty S2 U2 Hmem). apply IHHsub2.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [y [B [T' [Heq _]]]]. inversion Heq.
    + inversion Hmem.
  - (* fld *)
    inversion Hmem; subst. inversion H0; subst.
  - (* typ *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversions Hmem.
      exists S1 T1. split.
      apply has_any. assumption. apply has_refl.
      split; assumption.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [y [B [T' [Heq _]]]]. inversion Heq.
    + inversion Hmem.
  - (* sel2 *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversions Heq.
      assert (T' = T) as HeqT. {
        eapply good_unique_tight_bounds; eassumption.
      }
      subst. eauto.
    + inversion Hmem.
  - (* sel1 *)
    exists S2 U2. split.
    eapply has_any. assumption. eapply has_sel. eassumption. eassumption.
    eauto.
  - (* all *)
    inversion Hmem; subst. inversion H2; subst.
Qed.

Lemma good_has_member_monotonicity: forall G x T0 T A S U,
    good G ->
    binds x (typ_bnd T0) G ->
    has_member G x T A S U ->
    exists T1, has_member G x (typ_bnd T0) A T1 T1 /\
          subtyp ty_general sub_tight G S T1 /\
          subtyp ty_general sub_tight G T1 U.
Proof.
  introv Hgd Bis Hmem. inversion Hmem; subst.
  generalize dependent U. generalize dependent S.
  dependent induction H; intros.
  - (* var *)
    pose proof (binds_func H Bis) as H1.
    rewrite H1 in Hmem.
    pose proof (good_has_member_tightness Hgd Bis Hmem) as H2.
    exists U. subst. auto.
  - (* rec_intro *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversions Heq.
      apply IHty_trm; eauto.
      inversions H0. assumption.
      inversions H0. inversions H4. assumption.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversion Heq.
    + inversion Hmem.
  - (* rec_elim *)
    apply IHty_trm; eauto.
    apply has_any. assumption. apply has_bnd. assumption.
    apply has_bnd. assumption.
  - (* and_intro *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq [Hmem | Hmem]]]];
      inversions Heq; inversions H1; inversions H9.
      apply IHty_trm1; eauto.
      apply IHty_trm2; eauto. apply has_any; assumption.
      apply IHty_trm1; eauto. apply has_any; assumption.
      apply IHty_trm2; eauto.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversion Heq.
    + inversion Hmem.
  - (* sub *)
    destruct (good_has_member_covariance Hgd H1 H0 Hmem) as [S' [U' [Hmem' [Hsub1' Hsub2']]]].
    inversion Hmem'; subst.
    specialize (IHty_trm Hgd Bis S' U' Hmem' H4).
    destruct IHty_trm as [T1 [Hmem1 [Hsub1 Hsub2]]].
    exists T1. eauto.
Qed.

Lemma good_tight_bound_completeness : forall G x T A S U,
    good G ->
    binds x (typ_bnd T) G ->
    ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_rcd (dec_typ A S U)) ->
    subtyp ty_general sub_tight G (typ_sel (avar_f x) A) U /\
    subtyp ty_general sub_tight G S (typ_sel (avar_f x) A).
Proof.
  introv Hgd Bis Hty.
  assert (has_member G x (typ_rcd (dec_typ A S U)) A S U) as Hmem. {
    apply has_any. assumption. apply has_refl.
  }
  apply good_has_member_monotonicity with (T0:=T) in Hmem.
  destruct Hmem as [T1 [Hmem [Hsub1 Hsub2]]].
  assert (has_member G x (open_typ x T) A T1 T1) as Hmemx. {
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq Hmem]]. inversions Heq. assumption.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversion Heq.
    + inversion Hmem.
  }
  assert (record_type T) as Htype. {
    eapply good_typ_bnd_record; eauto.
  }
  assert (record_type (open_typ x T)) as Htypex. {
    apply open_record_type. assumption.
  }
  assert (open_typ x T = (typ_rcd (dec_typ A T1 T1)) \/ subtyp ty_precise sub_general G (open_typ x T) (typ_rcd (dec_typ A T1 T1))) as Hsub. {
    destruct has_member_rcd_typ_sub2_mut as [HE _].
    eapply HE; eauto.
  }
  assert (ty_trm ty_precise sub_general G (trm_var (avar_f x)) (open_typ x T)) as Htypx. {
    eapply ty_rec_elim.
    eapply ty_var.
    assumption.
  }
  assert (ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_typ A T1 T1))) as Htyp. {
    destruct Hsub as [Heq | Hsub].
    - rewrite Heq in Htypx. apply Htypx.
    - eapply ty_sub.
      intro. eexists. reflexivity.
      eapply Htypx. eapply Hsub.
  }
  split.
  eapply subtyp_trans. eapply subtyp_sel1_tight. eapply Htyp. eapply Hsub2.
  eapply subtyp_trans. eapply Hsub1. eapply subtyp_sel2_tight. eapply Htyp.
  eapply Hgd. eapply Bis.
Qed.
