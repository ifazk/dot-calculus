Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.

(* ###################################################################### *)
(* ###################################################################### *)
(** ** Some Lemmas *)

(* Misc helper lemma used later in this file *)
Lemma hasnt_notin : forall G ds ls t U,
    G /- ds :: U ->
    record_typ U ls ->
    defs_hasnt ds t ->
    t \notin ls.
Proof.
  introv Hds Hrec Hhasnt.
  inversions Hhasnt. gen ds. induction Hrec; intros.
  - inversions Hds. inversions H5; simpl in *; case_if; apply* notin_singleton.
  - apply notin_union; split.
    + inversions Hds. apply (IHHrec ds0 H5). simpl in *. case_if*.
    + inversions Hds. inversions H8; simpl in *; case_if; apply* notin_singleton.
Qed.


(* ###################################################################### *)
(** *** Lemmas about opening *)

Lemma open_fresh_avar_injective : forall x y k z,
    z \notin fv_avar x ->
    z \notin fv_avar y ->
    open_rec_avar k z x = open_rec_avar k z y ->
    x = y.
Proof.
  intros. destruct x, y; inversion H1.
  - case_if.
    + case_if. subst. reflexivity.
    + case_if. assumption.
  - case_if. simpl in H0. inversions H3. false* notin_same.
  - case_if. simpl in H. inversions H3. false* notin_same.
  - reflexivity.
Qed.

Lemma open_fresh_typ_dec_injective:
  (forall T T' k x,
    x \notin fv_typ T ->
    x \notin fv_typ T' ->
    open_rec_typ k x T = open_rec_typ k x T' ->
    T = T') /\
  (forall D D' k x,
    x \notin fv_dec D ->
    x \notin fv_dec D' ->
    open_rec_dec k x D = open_rec_dec k x D' ->
    D = D').
Proof.
  apply typ_mutind; intros.
  - destruct T'; inversions H1. reflexivity.
  - destruct T'; inversions H1. reflexivity.
  - destruct T'; inversions H2. apply f_equal. apply* (H d0 k x).
  - destruct T'; inversions H3.
    assert (t = T'1). {
      apply (H T'1 k x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    assert (t0 = T'2). {
      apply (H0 T'2 k x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    subst*.
  - destruct T'; inversions H1.
    simpl in H. simpl in H0. pose proof (open_fresh_avar_injective a a0 k H H0 H3).
    subst*.
  - destruct T'; inversions H2.
    apply f_equal. apply (H T' (Datatypes.S k) x).
    + simpl in H. assumption.
    + simpl in H0. assumption.
    + assumption.
  - destruct T'; inversions H3.
    assert (t = T'1). {
      apply (H T'1 k x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    assert (t0 = T'2). {
      apply (H0 T'2 (S k) x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    subst*.
  - destruct D'; inversions H3.
    assert (t0 = t3). {
      apply (H t3 k x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    assert (t1 = t4). {
      apply (H0 t4 k x).
      - simpl in H1. auto.
      - simpl in H2. auto.
      - assumption.
    }
    subst*.
  - destruct D'; inversions H2.
    apply f_equal. apply (H t2 k x).
    + simpl in H0. assumption.
    + simpl in H1. assumption.
    + assumption.
Qed.

Lemma open_fresh_trm_val_def_defs_injective:
  (forall t t' k x,
      x \notin fv_trm t ->
      x \notin fv_trm t' ->
      open_rec_trm k x t = open_rec_trm k x t' ->
      t = t') /\
  (forall v v' k x,
      x \notin fv_val v ->
      x \notin fv_val v' ->
      open_rec_val k x v = open_rec_val k x v' ->
      v = v') /\
  (forall d d' k x,
      x \notin fv_def d ->
      x \notin fv_def d' ->
      open_rec_def k x d = open_rec_def k x d' ->
      d = d') /\
  (forall ds ds' k x,
      x \notin fv_defs ds ->
      x \notin fv_defs ds' ->
      open_rec_defs k x ds = open_rec_defs k x ds' ->
      ds = ds').
Proof.
  apply trm_mutind; intros; simpl in *.
  - destruct t'; inversions H1.
    apply (open_fresh_avar_injective _ _ _ H H0) in H3. subst~.
  - destruct t'; inversions H2.
    specialize (H _ _ _ H0 H1 H4). subst~.
  - destruct t'; inversions H1.
    apply (open_fresh_avar_injective _ _ _ H H0) in H3. subst~.
  - destruct t'; inversions H1. simpl in *.
    assert (a = a1). {
      eapply open_fresh_avar_injective; eauto.
    }
    assert (a0 = a2). {
      eapply open_fresh_avar_injective; eauto.
    }
    subst~.
  - destruct t'; inversions H3. simpl in *.
    assert (t = t'1). {
      eapply H; eauto.
    }
    assert (t0 = t'2). {
      eapply H0; eauto.
    }
    subst~.
  - destruct v'; inversions H2. simpl in *.
    assert (t = t0). {
      eapply (proj21 open_fresh_typ_dec_injective); eauto.
    }
    assert (d = d0). {
      eapply H; eauto.
    }
    subst~.
  - destruct v'; inversions H2. simpl in *.
    assert (t = t1). {
      eapply (proj21 open_fresh_typ_dec_injective); eauto.
    }
    assert (t0 = t2). {
      eapply H; eauto.
    }
    subst~.
  - destruct d'; inversions H1. simpl in *.
    apply ((proj21 open_fresh_typ_dec_injective) _ _ _ _ H H0) in H4.
    subst~.
  - destruct d'; inversions H2. simpl in *.
    specialize (H _ _ _ H0 H1 H5).
    subst~.
  - destruct ds'; inversions H1. reflexivity.
  - destruct ds'; inversions H3. simpl in *.
    assert (d = ds'). {
      eapply H; eauto.
    }
    assert (d0 = d1). {
      eapply H0; eauto.
    }
    subst~.
Qed.

Lemma open_fresh_ec_injective : forall e e' z,
    z \notin fv_ec e ->
    z \notin fv_ec e' ->
    open_ec z e = open_ec z e' ->
    e = e'.
Proof.
  intros. dependent induction e; destruct e'; inversions H1.
  - reflexivity.
  - simpl in *. 
    apply (proj42 open_fresh_trm_val_def_defs_injective) in H4; auto.
    assert (e = e'). {
      eapply IHe; auto.
    }
    subst. reflexivity.
  - simpl in *.
    apply (proj41 open_fresh_trm_val_def_defs_injective) in H4; auto.
    subst. reflexivity.
Qed.

(* ###################################################################### *)

(* ###################################################################### *)
(** *** Lemmas about Record types *)

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

Lemma open_record_type: forall T x,
  record_type T -> record_type (open_typ x T).
Proof.
  intros. destruct H as [ls H]. exists ls. eapply open_record_typ.
  eassumption.
Qed.

Lemma ty_defs_record_type : forall G ds T,
    G /- ds :: T ->
    record_type T.
Proof.
  intros.
  dependent induction H.
  - destruct D.
    + inversions H. exists \{ label_typ t }. constructor*. constructor.
    + exists \{ label_trm t }. constructor*. constructor.
  - destruct IHty_defs. destruct D.
    + exists (x \u \{ label_typ t }). constructor*.
      * inversions H0. constructor.
      * inversions H0. simpl in H1. apply (hasnt_notin H H2 H1).
    + exists (x \u \{ label_trm t }). constructor*.
      * constructor.
      * inversions H0. simpl in H1. apply (hasnt_notin H H2 H1).
Qed.

Lemma opening_preserves_labels : forall z T ls ls',
    record_typ T ls ->
    record_typ (open_typ z T) ls' ->
    ls = ls'.
Proof.
  introv Ht Hopen. gen ls'.
  dependent induction Ht; intros.
  - inversions Hopen. rewrite* <- open_dec_preserves_label.
  - inversions Hopen. rewrite* <- open_dec_preserves_label.
    specialize (IHHt ls0 H4). rewrite* IHHt.
Qed.

Lemma record_type_open : forall z T,
    z \notin fv_typ T ->
    record_type (open_typ z T) ->
    record_type T.
Proof.
  introv Hz H. destruct H. dependent induction H.
  - exists \{ l }. destruct T; inversions x. constructor.
    + destruct d; inversions H.
      * apply (proj21 open_fresh_typ_dec_injective) in H3.
        { subst. constructor. }
        { simpl in Hz; auto. }
        { simpl in Hz; auto. }
      * constructor.
    + destruct d; inversions H.
      * apply (proj21 open_fresh_typ_dec_injective) in H3.
        { subst. constructor. }
        { simpl in Hz; auto. }
        { simpl in Hz; auto. }
      * constructor.
  - destruct T; inversions x. simpl in Hz.
    assert (Hz': z \notin fv_typ T1) by auto.
    destruct (IHrecord_typ T1 z Hz' eq_refl) as [ls' ?]. clear Hz'.
    destruct T2; inversions H5.
    destruct d; inversions H0.
    + exists (ls' \u \{ label_typ t }). apply (proj21 open_fresh_typ_dec_injective) in H6.
      * subst. constructor*.
        { constructor. }
        {
          simpl in H2. pose proof (opening_preserves_labels z H1 H).
          rewrite* H0.
        }
      * simpl in Hz; auto.
      * simpl in Hz; auto.
    + exists (ls' \u \{ label_trm t }). constructor*.
      * constructor.
      * simpl in H2. pose proof (opening_preserves_labels z H1 H).
        rewrite* H0.
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
  introv Htype Has1 Has2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:=dec_typ A T1 T1) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:=dec_typ A T2 T2) in Htyp.
    + inversions H5. false* H1.
    + assumption.
  - inversions H5. inversions* H9.
Qed.

Lemma unique_rcd_trm: forall T a U1 U2,
    record_type T ->
    record_has T (dec_trm a U1) ->
    record_has T (dec_trm a U2) ->
    U1 = U2.
Proof.
  introv Htype Has1 Has2.
  generalize dependent U2. generalize dependent U1. generalize dependent a.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:=dec_trm a U1) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:=dec_trm a U2) in Htyp.
    + inversions H5. false* H1.
    + assumption.
  - inversions H5. inversions* H9.
Qed.

(* ###################################################################### *)
(** *** Lemmas to upcast to general typing *)

Lemma precise_to_general: forall G t T,
    G |-! t : T ->
    G |- t : T.
Proof.
  intros. induction H; intros; subst; eauto.
Qed.

Lemma tight_to_general:
  (forall G t T,
     G |-# t : T ->
     G |- t : T) /\
  (forall G S U,
     G |-# S <: U ->
     G |- S <: U).
Proof.
  apply ts_mutind_t; intros; subst; eauto.
  - apply precise_to_general in t; eauto.
  - apply precise_to_general in t; eauto.
Qed.

(* ###################################################################### *)
(** *** Misc Lemmas *)

Lemma var_typing_implies_avar_f: forall G a T,
  G |- trm_var a : T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply IHty_trm; auto.
Qed.

Lemma val_typing: forall G v T,
  G |- trm_val v : T ->
  exists T', G |-! trm_val v : T' /\
        G |- T' <: T.
Proof.
  intros G v T H. dependent induction H.
  - exists (typ_all T U). split.
    apply ty_all_intro_p with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_bnd T). split.
    apply ty_new_intro_p with (L:=L); eauto. apply subtyp_refl.
  - destruct (IHty_trm _ eq_refl) as [T' [Hty Hsub]].
    exists T'. split; eauto.
Qed.

Lemma typing_implies_bound: forall G x T,
  G |- trm_var (avar_f x) : T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_var (avar_f x)) as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm; eauto];
    try solve [inversion Heqt; eapply IHty_trm1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.

Lemma precise_typing_implies_bound: forall G x T,
  G |-! trm_var (avar_f x) : T ->
  exists S, binds x S G.
Proof.
  intros.
  pose proof (precise_to_general H) as H'.
  pose proof (typing_implies_bound H'). assumption.
Qed.

Lemma empty_typing_var: forall x T,
    empty |- trm_var x : T -> False.
Proof.
  intros. dependent induction H.
  - apply* binds_empty_inv.
  - eapply IHty_trm; eauto.
  - eapply IHty_trm; eauto.
  - eapply IHty_trm2; eauto.
  - eapply IHty_trm; eauto.
Qed.
