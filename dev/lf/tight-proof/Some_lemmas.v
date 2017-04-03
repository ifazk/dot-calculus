Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Proofs *)

(* ###################################################################### *)
(** ** Some Lemmas *)

Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a T, record_dec (dec_trm a T)
.

Inductive record_typ : typ -> fset label -> Prop :=
| rt_one : forall D l,
  record_dec D ->
  l = label_of_dec D ->
  record_typ (typ_rcd D) \{l}
| rt_cons: forall T ls D l,
  record_typ T ls ->
  record_dec D ->
  l = label_of_dec D ->
  l \notin ls ->
  record_typ (typ_and T (typ_rcd D)) (union ls \{l})
.

Definition record_type T := exists ls, record_typ T ls.

Lemma open_dec_preserves_label: forall D x i,
  label_of_dec D = label_of_dec (open_rec_dec i x D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open_dec x D).
Proof.
  intros. inversion H; unfold open_dec; simpl; constructor.
Qed.

Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (open_typ x T) ls.
Proof.
  intros. induction H.
  - unfold open_typ. simpl.
    apply rt_one.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
  - unfold open_typ. simpl.
    apply rt_cons; try assumption.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
Qed.

Lemma open_eq_avar: forall x i a1 a2,
  x \notin fv_avar a1 -> x \notin fv_avar a2 ->
  open_rec_avar i x a1 = open_rec_avar i x a2 ->
  a1 = a2.
Proof.
  introv Fr1 Fr2 H. induction a1; induction a2; simpl in H; inversion H.
  - cases_if; cases_if.
    + reflexivity.
    + inversion H. subst. reflexivity.
  - cases_if.
    inversion H. subst. false.
    apply notin_same in Fr2. assumption.
  - cases_if.
    inversion H. subst. false.
    apply notin_same in Fr1. assumption.
  - subst. reflexivity.
Qed.

Lemma open_eq_typ_dec: forall x,
  (forall T1, x \notin fv_typ T1 ->
   forall T2, x \notin fv_typ T2 ->
   forall i, open_rec_typ i x T1 = open_rec_typ i x T2 ->
   T1 = T2) /\
  (forall D1, x \notin fv_dec D1 ->
   forall D2, x \notin fv_dec D2 ->
   forall i, open_rec_dec i x D1 = open_rec_dec i x D2 ->
   D1 = D2).
Proof.
  intros. apply typ_mutind; intros.
  - simpl in H1. induction T2; simpl in H1; inversion H1.
    reflexivity.
  - simpl in H1. induction T2; simpl in H1; inversion H1.
    reflexivity.
  - simpl in H2. induction T2; simpl in H2; inversion H2.
    f_equal. eapply H; eauto.
  - simpl in H3; induction T2; simpl in H3; inversion H3.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
  - simpl in H1; induction T2; simpl in H1; inversion H1.
    f_equal. eapply open_eq_avar; eauto.
  - simpl in H2. induction T2; simpl in H2; inversion H2.
    f_equal.
    eapply H; eauto.
  - simpl in H3. induction T2; simpl in H3; inversion H3.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
  - simpl in H3. induction D2; simpl in H3; inversion H3.
    subst.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
  - simpl in H2. induction D2; simpl in H2; inversion H2.
    subst.
    f_equal.
    eapply H; eauto.
Qed.

Lemma open_eq_typ: forall x i T1 T2,
  x \notin fv_typ T1 -> x \notin fv_typ T2 ->
  open_rec_typ i x T1 = open_rec_typ i x T2 ->
  T1 = T2.
Proof.
  introv Fr1 Fr2 Heq.
  destruct (open_eq_typ_dec x) as [HT HD].
  eapply HT; eauto.
Qed.

Lemma open_record_dec_rev: forall D x,
  x \notin fv_dec D ->
  record_dec (open_dec x D) -> record_dec D.
Proof.
  introv Fr H. remember (open_dec x D) as DX.
  generalize dependent D.
  inversion H; intros.
  - destruct D; unfold open_dec in HeqDX; simpl in HeqDX; inversion HeqDX.
    assert (t0 = t1) as Heq. {
      eapply open_eq_typ; eauto using notin_union_r1, notin_union_r2.
    }
    subst. constructor.
  - destruct D; unfold open_dec in HeqDX; simpl in HeqDX; inversion HeqDX.
    subst. constructor.
Qed.

Lemma open_record_typ_rev: forall T x ls,
   x \notin fv_typ T ->
  record_typ (open_typ x T) ls -> record_typ T ls.
Proof.
  introv Fr H. remember (open_typ x T) as TX.
  generalize dependent T.
  induction H; intros.
  - destruct T; unfold open_typ in HeqTX; simpl in HeqTX; inversion HeqTX.
    subst.
    rewrite <- open_dec_preserves_label.
    apply rt_one; eauto.
    eapply open_record_dec_rev; eauto.
  - destruct T0; unfold open_typ in HeqTX; simpl in HeqTX; inversion HeqTX.
    subst.
    destruct T0_2; unfold open_typ in H5; simpl in H5; inversion H5.
    subst.
    rewrite <- open_dec_preserves_label.
    apply rt_cons; try assumption.
    eapply IHrecord_typ; eauto using notin_union_r1.
    eapply open_record_dec_rev; eauto using notin_union_r2.
    eauto.
    rewrite <- open_dec_preserves_label in H2. apply H2.
Qed.

Lemma open_record_type: forall T x,
  record_type T -> record_type (open_typ x T).
Proof.
  intros. destruct H as [ls H]. exists ls. eapply open_record_typ.
  eassumption.
Qed.

Lemma open_record_type_rev: forall T x,
  x \notin fv_typ T ->
  record_type (open_typ x T) -> record_type T.
Proof.
  introv Fr H. destruct H as [ls H]. exists ls. eapply open_record_typ_rev; eauto.
Qed.

Lemma label_same_typing: forall G d D,
  ty_def G d D -> label_of_def d = label_of_dec D.
Proof.
  intros. inversion H; subst; simpl; reflexivity.
Qed.

Lemma record_defs_typing_rec: forall G ds S,
  ty_defs G ds S ->
  exists ls, record_typ S ls /\ forall l, l \notin ls <-> defs_hasnt ds l.
Proof.
  intros. induction H.
  - eexists. split.
    apply rt_one.
    inversion H; subst; constructor.
    reflexivity.
    apply label_same_typing in H. rewrite <- H.
    intros. split; intro A.
    + unfold defs_hasnt. simpl.
      apply notin_singleton in A.
      rewrite If_r. reflexivity. eauto.
    + unfold defs_hasnt in A. unfold get_def in A.
      case_if. apply notin_singleton. eauto.
  - destruct IHty_defs as [ls [IH1 IH2]].
    eexists. split.
    apply rt_cons; try eassumption.
    inversion H0; subst; constructor.
    reflexivity.
    apply label_same_typing in H0. rewrite <- H0.
    specialize (IH2 (label_of_def d)).
    destruct IH2 as [IH2A IH2B].
    apply IH2B. assumption.
    intros. split; intro A.
    + specialize (IH2 l).
      destruct IH2 as [IH2A IH2B].
      unfold defs_hasnt. simpl.
      rewrite If_r. unfold defs_hasnt in IH2A. apply IH2A.
      apply notin_union in A. destruct A as [A1 A2]. assumption.
      apply notin_union in A. destruct A as [A1 A2]. apply notin_singleton in A2.
      apply label_same_typing in H0. rewrite <- H0 in A2. eauto.
    + apply notin_union. split.
      * specialize (IH2 l).
        destruct IH2 as [IH2A IH2B].
        apply IH2B. inversion A.
        case_if. unfold defs_hasnt. assumption.
      * apply label_same_typing in H0. rewrite <- H0.
        unfold defs_hasnt in A. unfold get_def in A.
        case_if in A.
        apply notin_singleton. eauto.
Qed.

Lemma record_defs_typing: forall G ds S,
  ty_defs G ds S ->
  record_type S.
Proof.
  intros.
  assert (exists ls, record_typ S ls /\ forall l, l \notin ls <-> defs_hasnt ds l) as A.
  eapply record_defs_typing_rec; eauto.
  destruct A as [ls [A1 A2]].
  exists ls. apply A1.
Qed.

Inductive record_sub : typ -> typ -> Prop :=
| rs_refl: forall T,
  record_sub T T
| rs_dropl: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) (typ_rcd D)
| rs_drop: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) T'
| rs_pick: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) (typ_and T' (typ_rcd D))
.

Lemma record_typ_sub_label_in: forall T D ls,
  record_typ T ls ->
  record_sub T (typ_rcd D) ->
  label_of_dec D \in ls.
Proof.
  introv Htyp Hsub. generalize dependent D. induction Htyp; intros.
  - inversion Hsub. subst. apply in_singleton_self.
  - inversion Hsub; subst.
    + rewrite in_union. right. apply in_singleton_self.
    + rewrite in_union. left. apply IHHtyp. assumption.
Qed.

Lemma unique_rcd_typ: forall T A T1 T2,
  record_type T ->
  record_sub T (typ_rcd (dec_typ A T1 T1)) ->
  record_sub T (typ_rcd (dec_typ A T2 T2)) ->
  T1 = T2.
Proof.
  introv Htype Hsub1 Hsub2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Hsub1; inversion Hsub2; subst.
  - inversion H5. subst. reflexivity.
  - inversion H9. subst. reflexivity.
  - apply record_typ_sub_label_in with (D:=dec_typ A T2 T2) in Htyp.
    simpl in Htyp. simpl in H1. unfold "\notin" in H1. unfold not in H1.
    specialize (H1 Htyp). inversion H1.
    assumption.
  - apply record_typ_sub_label_in with (D:=dec_typ A T1 T1) in Htyp.
    simpl in Htyp. simpl in H1. unfold "\notin" in H1. unfold not in H1.
    specialize (H1 Htyp). inversion H1.
    assumption.
  - eapply IHHtyp; eassumption.
Qed.

Lemma precise_to_general:
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     m1 = ty_precise ->
     m2 = sub_general ->
     ty_trm ty_general sub_general G t T) /\
  (forall m1 m2 G S U,
     subtyp m1 m2 G S U ->
     m1 = ty_precise ->
     m2 = sub_general ->
     subtyp ty_general sub_general G S U).
Proof.
  apply ts_mutind; intros; subst; eauto.
Qed.

Lemma tight_to_general:
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     m1 = ty_general ->
     m2 = sub_tight ->
     ty_trm ty_general sub_general G t T) /\
  (forall m1 m2 G S U,
     subtyp m1 m2 G S U ->
     m1 = ty_general ->
     m2 = sub_tight ->
     subtyp ty_general sub_general G S U).
Proof.
  apply ts_mutind; intros; subst; eauto.
  - apply precise_to_general in t; eauto.
  - apply precise_to_general in t; eauto.
Qed.

(* ###################################################################### *)
(** * Misc *)

Lemma var_typing_implies_avar_f: forall G a T,
  ty_trm ty_general sub_general G (trm_var a) T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply IHty_trm; auto.
Qed.

Lemma val_typing: forall G v T,
  ty_trm ty_general sub_general G (trm_val v) T ->
  exists T', ty_trm ty_precise sub_general G (trm_val v) T' /\
             subtyp ty_general sub_general G T' T.
Proof.
  intros G v T H. dependent induction H.
  - exists (typ_all T U). split.
    apply ty_all_intro with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_bnd T). split.
    apply ty_new_intro with (L:=L); eauto. apply subtyp_refl.
  - destruct (IHty_trm _ eq_refl eq_refl eq_refl) as [T' [Hty Hsub]].
    exists T'. split; eauto.
Qed.

Lemma typing_implies_bound: forall m1 m2 G x T,
  ty_trm m1 m2 G (trm_var (avar_f x)) T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_var (avar_f x)) as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm; eauto];
    try solve [inversion Heqt; eapply IHty_trm1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.
