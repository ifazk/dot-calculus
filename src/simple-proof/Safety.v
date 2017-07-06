Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Narrowing.
Require Import Helper_lemmas.
Require Import Precise_types.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Canonical_forms1.
Require Import Canonical_forms2.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Proofs *)

(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.

(* Typing for the evaluation context / term pair with an empty typing context. Internally, a typing context representing the types of variables in the stack is used. *)
Inductive ty_ec_trm: ctx -> ec -> trm -> typ -> Prop :=
| ty_e_hole : forall G s t T,
    G ~~ s ->
    inert G ->
    G |- t : T ->
    ty_ec_trm G (e_hole s) t T
| ty_e_term : forall L G s u t T U,
    G ~~ s ->
    inert G ->
    G |- t : T ->
    (forall x, x \notin L -> G & x ~ T |- (open_trm x u) : U) ->
    ty_ec_trm G (e_term s u) t U.

Lemma lc_sto_push_inv : forall s x v,
    lc_sto (s & x ~ v) ->
    lc_sto s /\ lc_val v.
Proof.
  intros s x v H.
  inversion H.
  - destruct (empty_push_inv H1).
  - destruct (eq_push_inv H0) as [? [? ?] ]; subst.
    auto.
Qed.

Lemma lc_sto_binds_inv : forall s x v,
    lc_sto s ->
    binds x v s ->
    lc_val v.
Proof.
  intros.
  induction s using env_ind.
  - destruct (binds_empty_inv H0).
  - destruct (binds_push_inv H0) as [[? ?] | [? ?]]; subst.
    + apply (lc_sto_push_inv H).
    + apply IHs; auto.
      apply (lc_sto_push_inv H).
Qed.

Lemma lc_ec_sto_inv : forall e,
    lc_ec e ->
    lc_sto (ec_sto e).
Proof.
  intros e H.
  induction H; auto.
Qed.

Lemma lc_ec_sto_binds_inv : forall e x v,
    lc_ec e ->
    binds x v (ec_sto e) ->
    lc_val v.
Proof.
  intros.
  inversion H; subst; eauto using lc_sto_binds_inv.
Qed.

Lemma lc_defs_has : forall ds d,
    lc_defs ds ->
    defs_has ds d ->
    lc_def d.
Proof.
  intros.
  induction ds.
  - inversion H0.
  - unfold defs_has in H0; simpl in H0.
    cases_if.
    + inversion H0; subst. inversion H; auto.
    + apply IHds; auto. inversion H; auto.
Qed.

Lemma red_term_to_hole: forall s u t t',
    e_term s u / t => e_term s u / t' ->
    e_hole s / t => e_hole s / t'.
Proof.
  intros. dependent induction H.
  - eapply red_apply; eauto.
  - eapply red_project; eauto.
  - induction u; inversions x.
    eapply IHu2; eauto.
Qed.

Lemma lc_term_to_hole: forall s u t,
    lc_term (e_term s u) t ->
    lc_term (e_hole s) t.
Proof.
  intros. inversions H. inversions H0. repeat constructor~.
Qed.

Lemma open_comm_typ_dec: forall x y,
    (forall T n m,
        n <> m ->
        open_rec_typ n x (open_rec_typ m y T) =
        open_rec_typ m y (open_rec_typ n x T)) /\
    (forall D n m,
        n <> m ->
        open_rec_dec n x (open_rec_dec m y D) =
        open_rec_dec m y (open_rec_dec n x D)).
Proof.
  intros. apply typ_mutind; intros; subst; simpl; auto.
  - rewrite~ H.
  - rewrite~ H. rewrite~ H0.
  - destruct a; simpl; auto.
    repeat case_if; subst; simpl; repeat case_if~.
  - rewrite~ H.
  - rewrite~ H. rewrite~ H0.
  - rewrite~ H. rewrite~ H0.
  - rewrite~ H.
Qed.

Lemma open_comm_trm_val_def_defs : forall x y,
    (forall t n m,
        n <> m ->
        open_rec_trm n x (open_rec_trm m y t) =
        open_rec_trm m y (open_rec_trm n x t)) /\
    (forall v n m,
        n <> m ->
        open_rec_val n x (open_rec_val m y v) =
        open_rec_val m y (open_rec_val n x v)) /\
    (forall d n m,
        n <> m ->
        open_rec_def n x (open_rec_def m y d) =
        open_rec_def m y (open_rec_def n x d)) /\
    (forall ds n m,
        n <> m ->
        open_rec_defs n x (open_rec_defs m y ds) =
        open_rec_defs m y (open_rec_defs n x ds)).
Proof.
  intros. apply trm_mutind; intros; subst; simpl; auto.
  - destruct a; simpl; auto.
    repeat case_if; subst; simpl; repeat case_if~.
  - rewrite~ H.
  - destruct a; simpl; auto.
    repeat case_if; subst; simpl; repeat case_if~.
  - destruct a; destruct a0; simpl; auto; repeat case_if~; subst; simpl; repeat case_if~.
  - rewrite~ H. rewrite~ H0.
  - rewrite~ H. rewrite~ (proj21 (open_comm_typ_dec x y)).
  - rewrite~ H. rewrite~ (proj21 (open_comm_typ_dec x y)).
  - rewrite~ (proj21 (open_comm_typ_dec x y)).
  - rewrite~ H.
  - rewrite~ H. rewrite~ H0.
Qed.

Lemma red_preserves_lc :
  forall e t e' t',
    e / t => e' / t' ->
    lc_term e t ->
    lc_term e' t'.
Proof.
  intros.
  destruct H0.
  dependent induction H.
  - pose proof (lc_ec_sto_inv H0).
    pose proof (lc_ec_sto_binds_inv H0 H).
    inversion H3; subst.
    split; auto.
  - pose proof (lc_ec_sto_binds_inv H1 H).
    inversion H3; subst.
    pose proof (lc_defs_has (H7 x) H0).
    inversion H4; subst.
    split; auto.
  - inversion H0; subst.
    inversion H1; subst.
    split; auto. eapply lc_ec_term; auto.
    intros x. unfold open_trm.
    simpl. eapply lc_trm_let; auto.
    intros x0. pose proof (H4 x0).
    assert (0 <> 1) by auto.
    pose proof (proj1 (open_comm_trm_val_def_defs x0 x) t1 0 1 H2).
    unfold open_trm. rewrite H7.
    assert (open_rec_trm 1 x (open_rec_trm 0 x0 t1) = open_rec_trm 0 x0 t1) by (apply lc_opening; auto).
    rewrite H8. apply H.
  - inversion H1; subst.
    inversion H0; subst.
    split; auto.
  - inversion H0; subst. inversion H1; subst. split; auto.
  - inversion H0; subst. inversion H1; subst. split; auto.
Qed.


Lemma preservation_hole: forall G s t e' t' T,
    lc_term (e_hole s) t ->
    e_hole s / t => e' / t' ->
    G ~~ s ->
    inert G ->
    G |- t : T ->
    exists G',
      ty_ec_trm (G & G') e' t' T.
Proof.
  introv Hlc Hred Hwf Hin Ht.
  lets Hlc': (red_preserves_lc Hred Hlc).
  (* inversion Hlc' as [Hlc_ec Hlc_trm]. *)
  dependent induction Ht; try solve [inversion Hred].
  - destruct (canonical_forms_1 Hwf Hin Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    inversions Hred.
    apply (binds_func H4) in Bis. inversions Bis.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    constructor*. rewrite subst_intro_typ with (x:=y); auto.
    rewrite subst_intro_trm with (x:=y); auto.
    eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ.
  - destruct (canonical_forms_2 Hin Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    inversions Hred.
    apply (binds_func H2) in Bis. inversions Bis.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    rewrite <- (defs_has_inv Has H5). constructor*.
  - inversions Hred.
    exists (@empty typ). rewrite concat_empty_r.
    eapply ty_e_term; eauto.
  - specialize (IHHt Hlc Hred Hwf Hin Hlc') as [G' IHHt].
    exists G'. inversions IHHt.
    + eapply ty_e_hole; eauto.
      apply weaken_subtyp with (G2:=G') in H; eauto.
    + apply_fresh ty_e_term as z; eauto; intros. assert (z \notin L) by auto.
      specialize (H3 z H4).
      apply weaken_subtyp with (G2:=(G' & z ~ T0)) in H; rewrite concat_assoc in *; eauto.
Qed.

Lemma preservation: forall G e t e' t' T,
    lc_term e t ->
    e / t => e' / t' ->
    ty_ec_trm G e t T ->
    exists G', ty_ec_trm (G & G') e' t' T.
Proof.
  introv Hlc Hred Ht.
  (* lets Hlc': (red_preserves_lc Hred Hlc). *)
  inversion Hlc as [Hlc_ec Hlc_trm].
  inversions Ht.
  {
    eapply preservation_hole; eauto.
  }
  {
    rename H into Hwf. rename H0 into Hin.
    rename H1 into Ht1. rename H2 into Ht2.
    destruct t.
    - inversions Hred.
      pick_fresh y.
      exists (@empty typ). rewrite concat_empty_r.
      apply ty_e_hole; auto.
      rewrite subst_intro_trm with (x:=y); auto.
      rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
      eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ.
    - inversions Hred.
      pose proof (wf_sto_notin_dom Hwf H4).
      pose proof (val_typing Ht1) as [V [Hv Hs]].
      pick_fresh y. assert (y \notin L) by auto.
      specialize (Ht2 y H0).
      exists (x ~ V).
      apply ty_e_hole.
      * constructor~.
        apply (precise_to_general Hv).
      * constructor~.
        apply (precise_inert_typ Hv).
      * rewrite subst_intro_trm with (x:=y); auto.
        rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
        eapply subst_ty_trm; eauto.
        { eapply weaken_rules; eauto. }
        { apply~ fv_ctx_types_push. }
        {
          rewrite~ subst_fresh_typ.
          pose proof (ty_var (binds_tail x V G)).
          apply (ty_sub H1). apply (weaken_subtyp Hs); eauto.
        }
    - inversion Hred. rewrite <- H3 in Hred. apply red_term_to_hole in Hred. subst.
      apply lc_term_to_hole in Hlc.
      pose proof (preservation_hole Hlc Hred Hwf Hin Ht1) as [G' Ht].
      inversions Ht.
      exists G'.
      eapply ty_e_term with (L:=L \u (dom G) \u (dom G')); eauto. intros.
      assert (x0 \notin L) by auto.
      specialize (Ht2 x0 H3).
      eapply (proj41 weaken_rules); eauto.
    - inversion Hred. rewrite <- H1 in Hred.
      apply red_term_to_hole in Hred. subst.
      apply lc_term_to_hole in Hlc.
      pose proof (preservation_hole Hlc Hred Hwf Hin Ht1) as [G' Ht].
      inversions Ht.
      exists G'.
      eapply ty_e_term with (L:=L \u (dom G) \u (dom G')); eauto. intros.
      assert (x0 \notin L) by auto.
      specialize (Ht2 x0 H2).
      eapply (proj41 weaken_rules); eauto.
    - inversions Hred.
      exists (@empty typ). rewrite concat_empty_r.
      gen L.
      dependent induction Ht1; intros.
      + eapply ty_e_term with (L:=L \u (dom G)); eauto. intros.
        assert (x \notin L) by auto.
        unfold open_trm. simpl. specialize (H x H2).
        apply_fresh ty_let as z; eauto.
        unfold open_trm.
        rewrite~ (proj41 (open_comm_trm_val_def_defs z x)).
        inversions Hlc_ec. specialize (H6 z).
        apply (lc_opening 1 x) in H6. unfold open_trm in H6. rewrite H6.
        assert (z \notin L0) by auto.
        specialize (Ht2 z H3).
        eapply weaken_rules; eauto.
      + eapply IHHt1 with (L:=L \u (dom G)); eauto. intros.
        assert (x \notin L) by auto.
        specialize (Ht2 x H1).
        eapply narrow_typing; eauto. apply~ subenv_last.
  }
Qed.

Lemma progress_red: forall G e t T,
    ty_ec_trm G e t T ->
    (normal_form t \/ exists e' t', e / t => e' / t').
Proof.
  introv Ht.
  destruct e.
  - inversions Ht. rename H0 into Hwf. rename H1 into Hin. rename H3 into Ht.
    dependent induction Ht; try solve [left; auto].
    * destruct (canonical_forms_1 Hwf Hin Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
      right. repeat eexists. apply* red_apply.
    * destruct (canonical_forms_2 Hin Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
      right. repeat eexists. apply* red_project.
    * right. exists (e_term s u) t.
      apply red_hole_to_term.
    * specialize (IHHt Hwf Hin) as [IH | [t' [s' Hred]]].
      + left. assumption.
      + right. exists t' s'. assumption.
  - inversions Ht.
    rename H1 into Hwf. rename H2 into Hin. rename H4 into Ht. clear H7.
    dependent induction Ht; try solve [left; auto].
    * destruct (canonical_forms_1 Hwf Hin Ht1) as [L' [T' [t [Bis [Hsub Hty]]]]].
      right. repeat eexists. apply* red_apply.
    * destruct (canonical_forms_2 Hin Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
      right. repeat eexists. apply* red_project.
    * right. exists (e_term s (trm_let u t0)) t.
      eapply red_let_let.
    * specialize (IHHt Hwf Hin) as [IH | [t' [s' Hred]]].
      + left. assumption.
      + right. exists t' s'. assumption.
Qed.

Lemma progress: forall G e t T,
    lc_term e t ->
    ty_ec_trm G e t T ->
    (normal_form t \/
     exists e' t',
       e / t => e' / t' /\
       lc_term e' t').
Proof.
  introv Hlc Ht.
  destruct (progress_red Ht).
  - left~.
  - destruct H as [e' [t' Hred']]. right. exists e' t'. split~.
    eapply red_preserves_lc; eauto.
Qed.
