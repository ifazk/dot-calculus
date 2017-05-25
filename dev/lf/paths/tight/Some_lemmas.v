Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.

(* ###################################################################### *)
(* ###################################################################### *)
(** ** Some Lemmas *)

Lemma open_var_eq_p_typ_dec_path: forall x,
    (forall T : typ, forall n : nat,
          open_rec_typ n x T = open_rec_typ_p n (p_var (avar_f x)) T) /\
    (forall D : dec, forall n : nat,
          open_rec_dec n x D = open_rec_dec_p n (p_var (avar_f x)) D) /\
    (forall P : path, forall n : nat,
          open_rec_path n x P = open_rec_path_p n (p_var (avar_f x)) P).
Proof.
  intros. apply typ_mutind; unfold open_typ, open_typ_p; simpl; intros; auto.
  - (* typ_rcd *)
    f_equal*.
  - (* typ_and *)
    rewrite H. rewrite* H0.
  - (* typ_path *)
    rewrite* H.
  - (* typ_bnd *)
    f_equal*.
  - (* typ_all *)
    rewrite H. rewrite* H0.
  - (* dec_typ *)
    rewrite H. rewrite* H0.
  - (* dec_trm *)
    rewrite* H.
  - (* p_var *)
    unfold open_rec_avar, open_rec_avar_p. destruct a; simpl. case_if*. f_equal*.
  - (* p_sel *)
    rewrite* H.
Qed.

Lemma open_var_path_typ_eq: forall x T,
  T ||^ x = open_typ_p (p_var (avar_f x)) T.
Proof.
  intros. apply open_var_eq_p_typ_dec_path.
Qed.

Lemma open_var_path_dec_eq: forall x D,
  open_dec x D = open_dec_p (p_var (avar_f x)) D.
Proof.
  intros. apply open_var_eq_p_typ_dec_path.
Qed.

(* ###################################################################### *)
(** *** Lemmas about Record types *)

Lemma open_dec_preserves_label: forall D x i,
  label_of_dec D = label_of_dec (open_rec_dec_p i x D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

Lemma open_record_dec_p: forall D p,
  record_dec D -> record_dec (open_dec_p p D).
Proof.
  intros. inversion H; unfold open_dec; simpl; constructor.
Qed.

Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open_dec x D).
Proof.
  intros. rewrite open_var_path_dec_eq. apply* open_record_dec_p.
Qed.

Lemma open_record_typ_p: forall T p ls,
  record_typ T ls -> record_typ (open_typ_p p T) ls.
Proof.
  intros. induction H.
  - unfold open_typ_p. simpl.
    apply rt_one.
    apply open_record_dec_p. assumption.
    rewrite <- open_dec_preserves_label. assumption.
  - unfold open_typ. simpl.
    apply rt_cons; try assumption.
    apply open_record_dec_p. assumption.
    rewrite <- open_dec_preserves_label. assumption.
Qed.

Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (T ||^ x) ls.
Proof.
  introv Hr. rewrite open_var_path_typ_eq. apply* open_record_typ_p.
Qed.

Lemma open_record_type_p: forall T p,
  record_type T -> record_type (open_typ_p p T).
Proof.
  intros. destruct H as [ls H]. exists ls. apply* open_record_typ_p.
Qed.

Lemma open_record_type: forall T x,
  record_type T -> record_type (T ||^ x).
Proof.
  introv Hr. rewrite open_var_path_typ_eq. apply* open_record_type_p.
Qed.

(* ###################################################################### *)
(** *** Lemmas about Record has *)

Lemma record_typ_has_label_in: forall T D ls,
  record_typ T ls ->
  record_has T D ->
  label_of_dec D \in ls.
Proof.
  introv Htyp Has. generalize dependent D. induction Htyp; intros.
  - inversion Has. subst. apply in_singleton_self.
  - inversion Has; subst; rewrite in_union.
    + left. apply* IHHtyp.
    + right. inversions H5. apply in_singleton_self.
Qed.

Lemma unique_rcd_typ: forall T A T1 T2,
  record_type T ->
  record_has T (dec_typ A T1 T1) ->
  record_has T (dec_typ A T2 T2) ->
  T1 = T2.
Proof.
  Proof.
  introv Htype Has1 Has2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:=dec_typ A T1 T1) in Htyp.
    + inversions H9. unfold "\notin" in H1. unfold not in H1. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:=dec_typ A T2 T2) in Htyp.
    + inversions H5. unfold "\notin" in H1. unfold not in H1. false* H1.
    + assumption.
  - inversions H5. inversions* H9.
Qed.

Lemma unique_rcd_trm: forall T a m1 m2 U1 U2,
    record_type T ->
    record_has T {{ a [m1] U1 }} ->
    record_has T {{ a [m2] U2 }} ->
    m1 = m2 /\ U1 = U2.
Proof.
  introv Htype Has1 Has2.
  gen U1 U2 m1 m2 a.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:={{ a [m1]  U1 }}) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:={{ a [m1]  U2 }}) in Htyp.
    + inversions H5. false* H1.
    + inversions H5. lets Hr: (record_typ_has_label_in Htyp H9).
      false* H1.
  - inversions H5. inversions* H9.
Qed.

(* ###################################################################### *)
(** *** Lemmas to upcast to general typing *)

Lemma precise_to_general: forall G t T,
  G |-! t :: T ->
  G |- t :: T.
Proof.
  intros; induction H; eauto.
Qed.

Lemma tight_to_general:
  (forall G t T,
     G |-# t :: T ->
     G |- t :: T) /\
  (forall G S U,
     G |-# S <: U ->
     G |- S <: U) /\
  (forall G p,
     norm_t G p ->
     norm G p).
Proof.
  apply ts_mutind_t; intros; subst; eauto.
  - apply precise_to_general in t; eauto.
  - apply precise_to_general in t; eauto.
  - apply* norm_var.
  - apply* norm_path.
Qed.

(* ###################################################################### *)
(** *** Misc Lemmas *)

Lemma var_typing_implies_avar_f: forall G a T,
  G |- trm_path (p_var a) :: T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply* IHty_trm. apply* IHty_trm2. apply* IHty_trm.
Qed.

Lemma val_typing: forall G v T,
  G |- trm_val v :: T ->
  exists T', G |-! trm_val v :: T' /\
             G |- T' <: T.
Proof.
  intros. dependent induction H.
  - exists (typ_all T U). split.
    apply ty_all_intro_p with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_bnd T). split.
    apply ty_new_intro_p with (L:=L); eauto. apply subtyp_refl.
  - specialize (IHty_trm v eq_refl). destruct IHty_trm as [T' [Hty Hsub]].
    exists T'. split; eauto.
Qed.

Lemma typing_implies_bound: forall G x T,
  G |- trm_path (p_var (avar_f x)) :: T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_path (p_var (avar_f x))) as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm; eauto];
    try solve [inversion Heqt; eapply IHty_trm1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.

Lemma typing_implies_bound_p: forall G x T,
  G |-! trm_path (p_var (avar_f x)) :: T ->
  exists S, binds x S G.
Proof.
  intros. eapply typing_implies_bound. apply* precise_to_general.
Qed.
