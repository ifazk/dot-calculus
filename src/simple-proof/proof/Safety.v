(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions.
Require Import Operational_semantics.
Require Import Local_Closure.
Require Import Weakening Narrowing Helper_lemmas Precise_types Substitution Canonical_forms.

(** Reduction in an empty context *)
Notation "t '|->' u" := (empty [t |-> u]) (at level 50).

(** Typing in an empty context *)
Notation "'⊢' t ':' T" := (empty ⊢ t: T) (at level 40, t at level 59).

(** * Progress *)

(** If a value [v] has type [T], then [v] has a precise type [T']
    that is a subtype of [T].
    This lemma corresponds to Lemma 3.13 in the paper. *)
Lemma val_typing: forall G v T,
  G ⊢ trm_val v : T ->
  exists T', G ⊢! trm_val v : T' /\
        G ⊢ T' <: T.
Proof.
  intros G v T H. dependent induction H; eauto.
  destruct (IHty_trm _ eq_refl) as [T' [Hty Hsub]]. eauto.
Qed.

Lemma open_rec_preserve_normal_form: forall k x t,
    x \notin fv_trm t ->
    normal_form (open_rec_trm k x t) ->
    normal_form t.
Proof.
  intros. generalize dependent x.
  generalize dependent k.
  induction t; auto; intros;
    try (solve [
    unfold open_trm in H0; unfold open_rec_trm in H0;
    inversion H0]).
  unfold open_trm in H0. unfold open_rec_trm in H0.
  inversion H0. fold open_rec_trm in *.
  unfold fv_trm in H. fold fv_trm in H.
  assert (x \notin fv_trm t2); auto.
  specialize (IHt2 _ _ H4 H2).

  destruct t1; simpl; inversion H1.
  constructor. auto.
Qed.


Corollary open_preserve_normal_form : forall x t,
    x \notin fv_trm t ->
    normal_form (open_trm x t) ->
    normal_form t.
Proof. apply open_rec_preserve_normal_form. Qed.


Lemma open_bound_lc_trm : forall k x t,
    lc_trm (open_trm x t) ->
    open_rec_trm (S k) x t = t.
Proof.
  intros.
  apply lc_at_opening with (n:=S k) (x:=x) in H.
  eapply (proj1 (lc_open_rec_open_trm_val_def_defs x _)).
  - instantiate (1 := 0). auto.
  - eassumption.
Qed.


Lemma close_rec_typ_dec_no_capture : forall x,
    (forall T k, x \notin fv_typ (close_rec_typ k x T)) /\
    (forall D k, x \notin fv_dec (close_rec_dec k x D)).
Proof.
  intros x.
  apply typ_mutind; intros; simpl; auto;
    match goal with
    | [ |- _ \notin fv_avar (close_rec_avar _ _ ?a) ] => destruct a
    end; simpl;
      try case_if; unfold fv_avar; auto.
Qed.


Lemma close_rec_trm_val_def_defs_no_capture: forall x,
    (forall t k, x \notin fv_trm (close_rec_trm k x t)) /\
    (forall v k, x \notin fv_val (close_rec_val k x v)) /\
    (forall d k, x \notin fv_def (close_rec_def k x d)) /\
    (forall ds k, x \notin fv_defs (close_rec_defs k x ds)).
Proof.
  intro x.
  apply trm_mutind; intros; simpl; auto;
    try apply notin_union;
    repeat split;
    try applys close_rec_typ_dec_no_capture;
    repeat
      match goal with
      | [ |- _ \notin fv_avar (close_rec_avar _ _ ?a) ] => destruct a; simpl
      end;
    repeat case_if; unfold fv_avar; auto.
Qed.


Lemma open_rec_eval_to_open_rec : forall e x t t' v,
    x \notin dom e \u fv_trm t \u fv_val v ->
    lc_sto e -> lc_val v ->
    e & x ~ v[ open_trm x t |-> t'] ->
    exists f, (x \notin (fv_trm f)) /\ t' = open_trm x f.
Proof.
  intros. exists (close_trm x t'). remember (close_trm x t') as ct. split.
  - subst ct. applys close_rec_trm_val_def_defs_no_capture.
  - symmetry. rewrite Heqct. applys open_left_inverse_close_trm_val_def_defs.
    eapply lc_env_eval_to_lc_trm.
    + apply lc_sto_cons; eassumption.
    + eassumption.
Qed.


Lemma subenv_empty_supremum : forall G, subenv G empty.
Proof.
  unfold subenv. intros.
  unfold binds in H. rewrite get_empty in H.
  inversion H.
Qed.


Inductive indc_subenv: ctx -> ctx -> Prop :=
| new_subenv_empty : indc_subenv empty empty
| new_subenv_push: forall G G' x T T',
    indc_subenv G G' ->
    ok G ->
    ok G' ->
    x # G ->
    x # G' ->
    G ⊢ T <: T' ->
    indc_subenv (G & x ~ T) (G' & x ~ T').
Hint Constructors indc_subenv.


Lemma indc_subenv_implies_subenv : forall G1 G2,
    indc_subenv G1 G2 -> subenv G1 G2.
Proof.
  introv H. induction H.
  - apply subenv_empty_supremum.
  - unfold subenv. intros y Tb Bi. apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
    + destruct Bi. subst. right. exists T. split.
      * apply binds_push_eq.
      * apply weaken_subtyp; auto.
    + destruct Bi. unfold subenv in IHindc_subenv.
      destruct (IHindc_subenv _ _ H6).
      * left. apply binds_push_neq; trivial.
      * destruct H7 as [T1 [Hb Hs]]. right.
        exists T1. split.
        -- apply binds_push_neq; trivial.
        -- apply weaken_subtyp; auto.
Qed.
Hint Resolve indc_subenv_implies_subenv.

Lemma indc_subenv_refl : forall G, ok G -> indc_subenv G G.
Proof.
  intros G H. induction H; auto.
Qed.
Hint Resolve indc_subenv_refl.


Lemma indc_subenv_trans : forall G1 G2 G3,
    indc_subenv G1 G2 ->
    indc_subenv G2 G3 ->
    indc_subenv G1 G3.
Proof.
  introv H. gen G3. induction H; intros; auto.
  dependent induction H5.
  - apply empty_push_inv in x. contradiction.
  - rename x into He. apply eq_push_inv in He. destruct_all.
    subst.
    apply IHindc_subenv in H5.
    constructor; auto.
    apply indc_subenv_implies_subenv in H.
    apply narrow_subtyping with (G':=G) in H10; auto.
    eapply subtyp_trans; eauto.
Qed.
Hint Resolve indc_subenv_trans.


Lemma indc_subenv_push : forall G1 G2 x T,
    indc_subenv G1 G2 ->
    ok (G1 & x ~ T) -> ok (G2 & x ~ T) ->
    indc_subenv (G1 & x ~ T) (G2 & x ~ T).
Proof.
  intros. induction H; intros; auto.
  constructor; auto;
    repeat
      match goal with
      | H : empty = _ & _ |- _ => destruct (empty_push_inv H)
      | H : _ & _ ~ _ = _ & _ ~ _ & _ ~ _ |- _ => apply eq_push_inv in H; destruct_all; subst; trivial
      | H : ok (?G & ?x ~ ?T & _ ~ _) |- x # ?G & ?x ~ ?T => inversion H
      end.
Qed.
Hint Resolve indc_subenv_push.


Definition subst_env x y e := map (subst_val x y) e.


Lemma binds_subst_env : forall x y b v e,
    binds b v e -> binds b (subst_val x y v) (subst_env x y e).
Proof.
  introv. gen x y b v. induction e using env_ind; intros.
  - destruct (binds_empty_inv H).
  - apply binds_push_inv in H.
    destruct_all; subst; unfold subst_env; rewrite map_push.
    + auto.
    + apply binds_push_neq; auto.
Qed.


Lemma binds_fv_sto_vals : forall x y v e,
    binds y v e ->
    x \notin fv_sto_vals e ->
    x \notin fv_val v.
Proof.
  intros. unfold fv_sto_vals in H0.
  eapply fv_in_values_binds.
  - eassumption.
  - assumption.
Qed.


Lemma open_subst_defs : forall x y z a ds t,
    z <> x ->
    defs_has (open_defs z ds) (def_trm a t) ->
    defs_has (open_defs z (subst_defs x y ds)) (def_trm a (subst_trm x y t)).
Proof.
  introv. gen x y z a t. induction ds; intros.
  - inversion H0.
  - unfold open_defs in *. simpls.
    unfold defs_has in *. simpls. case_if.
    + destruct d; simpls; case_if; auto.
      inversion H0. subst.
      rewrite subst_open_commut_trm. unfold subst_fvar.
      case_if; try contradiction. auto.
    + case_if; apply IHds; destruct d; simpls; auto; contradiction.
Qed.


Lemma open_subst_defs2 : forall x y a ds t,
    y <> x ->
    defs_has (open_defs x ds) (def_trm a t) ->
    defs_has (open_defs y (subst_defs x y ds)) (def_trm a (subst_trm x y t)).
Proof.
  introv. gen x y a t. induction ds; intros.
  - inversion H0.
  - unfold open_defs in *. simpls.
    unfold defs_has in *. simpls. case_if.
    + destruct d; simpls; case_if; auto.
      inversion H0. subst.
      rewrite subst_open_commut_trm. unfold subst_fvar.
      case_if; try contradiction. auto.
    + case_if; apply IHds; destruct d; simpls; auto; contradiction.
Qed.


Lemma lc_at_subst_avar : forall v x y k,
    lc_at_var k v <-> lc_at_var k (subst_avar x y v).
Proof.
  intros.
  split; intros;
    try solve [inversion H; simpls; auto].
  destruct v; auto.
Qed.


Lemma lc_at_subst_typ_dec : forall k,
  (forall T, lc_at_typ k T -> forall x y, lc_at_typ k (subst_typ x y T)) /\
  (forall D, lc_at_dec k D -> forall x y, lc_at_dec k (subst_dec x y D)).
Proof.
  apply lc_at_typ_mutind; intros; simpls; auto.
  constructor. apply lc_at_subst_avar. trivial.
Qed.


Lemma lc_at_subst_trm_val_def_defs : forall k,
    (forall t, lc_at_trm k t -> forall x y, lc_at_trm k (subst_trm x y t)) /\
    (forall v, lc_at_val k v -> forall x y, lc_at_val k (subst_val x y v)) /\
    (forall d, lc_at_def k d -> forall x y, lc_at_def k (subst_def x y d)) /\
    (forall ds, lc_at_defs k ds -> forall x y, lc_at_defs k (subst_defs x y ds)).
Proof.
  apply lc_at_mutind; intros; simpls; auto;
    repeat constructor;
    try solve [apply lc_at_subst_avar; trivial];
    try applys lc_at_subst_typ_dec; trivial.
Qed.


Lemma open_fv_avar : forall v x y k,
    x \notin fv_avar v \u \{y} ->
    x \notin fv_avar (open_rec_avar k y v).
Proof.
  intros. destruct v; simpls; try case_if; unfold fv_avar; auto.
Qed.


Lemma open_fv_typ_dec :
  (forall T x y k, x \notin fv_typ T \u \{y} -> x \notin fv_typ (open_rec_typ k y T)) /\
  (forall D x y k, x \notin fv_dec D \u \{y} -> x \notin fv_dec (open_rec_dec k y D)).
Proof.
  apply typ_mutind; intros; simpls; auto;
    apply open_fv_avar; auto.
Qed.


Lemma open_fv_trm_val_def_defs :
  (forall t x y k, x \notin fv_trm t \u \{y} -> x \notin fv_trm (open_rec_trm k y t)) /\
  (forall v x y k, x \notin fv_val v \u \{y} -> x \notin fv_val (open_rec_val k y v)) /\
  (forall d x y k, x \notin fv_def d \u \{y} -> x \notin fv_def (open_rec_def k y d)) /\
  (forall ds x y k, x \notin fv_defs ds \u \{y} -> x \notin fv_defs (open_rec_defs k y ds)).
Proof.
  Local Hint Resolve open_fv_avar.
  apply trm_mutind; intros; simpls; auto;
    try apply notin_union_l;
    try applys open_fv_typ_dec; auto.
Qed.


Lemma fv_sto_vals_push : forall e x y v,
    y \notin fv_sto_vals e \u fv_val v ->
    y \notin fv_sto_vals (e & x ~ v).
Proof.
  intros. apply notin_union in H. destruct H.
  unfold fv_sto_vals in *.
  unfold fv_in_values in *. rewrite values_def in *.
  rewrite single_def.
  rewrite concat_def.
  rewrite LibList.app_cons_one.
  rewrite LibList.map_cons. simpl.
  apply notin_union_l; auto.
Qed.


Lemma eval_renaming_subst : forall x y e1 e2 v t1 t2,
    x \notin dom e1 \u fv_sto_vals e1 \u dom e2 ->
    y \notin dom e1 \u fv_sto_vals e1
      \u dom e2 \u fv_sto_vals e2 \u fv_val v \u fv_trm t1 ->
    (e1 & x ~ v & e2)[t1 |-> t2] ->
    (e1 & y ~ subst_val x y v & subst_env x y e2)[subst_trm x y t1 |-> subst_trm x y t2].
Proof.
  Local Hint Resolve binds_subst_env.

  Local Ltac contra_bind :=
    repeat match goal with
           | [ H : _ \notin _ \u _ |- _ ] => apply notin_union in H; destruct H
           end;
    match goal with
    | [ _ : ?x \notin dom ?e, _ : binds ?x _ ?e |- _ ] =>
      exfalso; eapply binds_fresh_inv; [eassumption | auto 1]
    end.

  Local Ltac solve_left_most :=
    repeat apply binds_concat_left; unfold subst_env; try rewrite dom_map; auto;
    rewrite (proj1 (proj2 (subst_fresh_trm_val_def_defs _ _))); auto;
    eapply binds_fv_sto_vals; eauto.

  introv Hfx Hfy He. dependent induction He; simpls.
  - apply binds_middle_inv in H0; destruct_all; repeat case_if; subst;
      try solve [contra_bind];
      rewrite subst_open_commut_trm; unfold subst_fvar; case_if; try contradiction;
        apply red_apply with (subst_typ x y T); auto 1;
          assert (Hs : val_lambda (subst_typ x y T) (subst_trm x y t) =
                       subst_val x y (val_lambda T t));
          auto;
          rewrite Hs;
          try match goal with
              | [ |- binds ?y _ (_ & ?y ~ _ & _) ] =>
                apply binds_middle_eq; unfold subst_env; rewrite dom_map; auto
              end;
          try solve [apply binds_concat_right;
                     apply binds_subst_env; trivial];
          solve_left_most.
  - apply binds_middle_inv in H0; destruct_all; repeat case_if; subst;
      try solve [contra_bind];
      apply red_project with (T:=subst_typ x y T) (ds:=subst_defs x y ds); auto;
        assert (Hs : val_new (subst_typ x y T) (subst_defs x y ds) = subst_val x y (val_new T ds));
        auto;
        try rewrite Hs.
    + apply binds_concat_right; apply binds_subst_env; trivial.
    + apply open_subst_defs; auto.
    + apply binds_middle_eq; unfold subst_env; rewrite dom_map; auto.
    + apply open_subst_defs2; auto.
    + solve_left_most.
    + apply open_subst_defs; auto.
  - case_if; simpls;
      subst; rewrite subst_open_commut_trm; unfold subst_fvar;
        case_if; try contradiction; constructor;
          inversion H; constructor; auto;
            applys lc_at_subst_trm_val_def_defs; trivial.
  - inversion H. inversion H2.
    repeat constructor; auto;
      applys lc_at_subst_trm_val_def_defs; trivial.
  - inversion H.
    repeat constructor; auto;
      applys lc_at_subst_trm_val_def_defs; trivial.
  - econstructor.
    + inversion H. inversion H4.
      repeat constructor;
        applys lc_at_subst_trm_val_def_defs; trivial.
    + intros.
      instantiate (1 := L \u dom e1 \u fv_sto_vals e1 \u dom e2 \u fv_sto_vals e2
                            \u fv_val v \u fv_val v0 \u fv_trm t \u \{x} \u \{y}) in H2.

      assert (x0 <> x); auto.
      assert (x0 <> y); auto.

      assert (subst_fvar x y x0 = x0). {
        unfold subst_fvar. case_if; auto.
      }
      rewrite <- H5.
      rewrite <- subst_open_commut_trm. rewrite <- subst_open_commut_trm.
      rewrite H5.

      assert (x0 \notin L); auto.
      specialize (H1 _ H6 v (e2 & x0 ~ v0) e1).

      assert (y \notin fv_trm (open_trm x0 t)). {
        applys open_fv_trm_val_def_defs; auto.
      }
      assert (y \notin fv_sto_vals (e2 & x0 ~ v0)). {
        apply fv_sto_vals_push. auto.
      }

      assert (y \notin dom e1 \u fv_sto_vals e1
                \u dom (e2 & x0 ~ v0) \u fv_sto_vals (e2 & x0 ~ v0)
                \u fv_val v \u fv_trm (open_trm x0 t)); auto.

      assert (x \notin dom e1 \u fv_sto_vals e1 \u dom (e2 & x0 ~ v0)); auto.

      assert (subst_env x y (e2 & x0 ~ v0) = subst_env x y e2 & x0 ~ subst_val x y v0). {
        unfold subst_env. apply map_push.
      }
      specialize (H1 H9 _ H10).
      rewrite H11 in H1.
      repeat rewrite concat_assoc in H1.
      apply H1. auto.
Qed.


Lemma progress_ec: forall G' G e t T,
    lc_sto e ->
    lc_trm t ->
    indc_subenv G' G ->
    inert G' ->
    G' ~~ e ->
    G ⊢ t: T ->
    ok G ->
    (normal_form t \/ exists t', e[t |-> t']).
Proof with auto.
  introv Hlce Hlc Hsenv Hig Hwf Ht Hokg. gen G' e.
  induction Ht; eauto; intros.
  - Case "ty_all_elim".
    apply narrow_typing with (G':=G') in Ht1; auto.
    destruct (canonical_forms_fun Hig Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    right. repeat eexists. apply* red_apply.
  - Case "ty_new_elim".
    apply narrow_typing with (G':=G') in Ht; auto.
    destruct (canonical_forms_obj Hig Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    right. repeat eexists. apply* red_project.
  - Case "ty_let".
    destruct t.
    + SCase "t = trm_var a".
      apply narrow_typing with (G':=G') in Ht; auto.
      destruct (var_typing_implies_avar_f Ht); subst.
      right. exists (open_trm x u). constructor...
    + SCase "t = trm_val v".
      apply val_typing in Ht.
      destruct Ht as [T' [H1 H2]].
      pose proof (precise_inert_typ H1) as Hpit.
      pick_fresh x.
      destruct H0 with (x:=x) (G' := G' & x ~ T') (e := e & x ~ v); auto.
      * inversion Hlc. trivial. applys lc_at_to_open_trm_val_def_defs...
      * intros. eapply indc_subenv_trans; econstructor; eauto.
      * constructor; auto. inversion Hlc. inversion H5. trivial.
      * intros. apply precise_to_general in H1.
        constructor; auto. eapply narrow_typing in H1; eauto.
      * left.
        destruct u; auto; apply open_preserve_normal_form in H3; auto.
      * right. destruct H3.

        (* exists. eapply red_let_val; auto. *)
        (* intros. *)


        pose proof H3. inversion Hlc. inversion H7.
        apply open_rec_eval_to_open_rec in H3; auto.
        destruct_all. subst.
        exists (trm_let (trm_val v) x1).

        apply red_let_val with (L \u dom G \u fv_ctx_types G \u dom G
                                  \u fv_ctx_types G \u dom e \u fv_sto_vals e
                                  \u fv_trm (open_trm x u) \u fv_val v \u fv_typ T
                                  \u fv_typ U \u fv_typ T' \u fv_trm x1
                                  \u dom (empty : sto) \u fv_sto_vals empty); auto.
        intros.

        replace (e & x ~ v) with (e & x ~ v & empty) in H4;
          try (rewrite <- concat_empty_r; trivial).


        replace (e & x0 ~ v) with (e & x0 ~ v & empty);
        try (rewrite <- concat_empty_r; trivial).

        assert (Hsubstv : subst_val x x0 v = v). {
          applys subst_fresh_trm_val_def_defs. auto.
        }
        rewrite <- Hsubstv.

        assert (Hleft : open_trm x0 u = subst_trm x x0 (open_trm x u)). {
          apply subst_intro_trm. auto.
        }
        rewrite Hleft.

        assert (Hright : open_trm x0 x1 = subst_trm x x0 (open_trm x x1)). {
          apply subst_intro_trm. auto.
        }
        rewrite Hright.

        replace empty with (subst_env x x0 empty); try apply map_empty; trivial.

        apply eval_renaming_subst; auto.
    + SCase "t = trm_sel a t".
      right.
      inversion Hlc.
      destruct (IHHt H3 Hokg G' Hsenv Hig e Hlce Hwf) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    + SCase "t = trm_app a a0".
      right.
      inversion Hlc.
      destruct (IHHt H3 Hokg G' Hsenv Hig e Hlce Hwf) as [Hnf | [t' Hr]]. inversion Hnf.
      eexists. constructor*.
    + SCase "t = trm_let t1 t2".
      right. eexists. constructor. inversion Hlc. trivial.
Qed.

(** ** Progress Theorem
    If [⊢ t : T], then either [t] is a normal form,
    or [t]] reduces to some [t']. *)
Theorem progress: forall t T,
    lc_trm t ->
    ⊢ t: T ->
    normal_form t \/ (exists t', t |-> t').
Proof.
  intros. apply* progress_ec; constructor; auto.
Qed.

(** * Preservation *)

Lemma preservation_ec: forall G G' e t t' T,
    lc_trm t ->
    indc_subenv G' G ->
    G' ~~ e ->
    inert G' ->
    G ⊢ t: T ->
    e[t |-> t'] ->
    ok G ->
    G' ⊢ t': T.
Proof.
  Local Hint Resolve open_bound_lc_trm.
  introv Hlc Hsenv Hwf Hi Ht Hr Hok. gen e t'. gen G'.
  induction Ht; introv Hsenv Hi Hwf Hr; try solve [inversions Hr]; eauto.
  - Case "ty_all_elim".
    apply narrow_typing with (G':=G') in Ht1; auto.
    apply narrow_typing with (G':=G') in Ht2; auto.
    destruct (canonical_forms_fun Hi Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    inversions Hr.
    apply (binds_func H4) in Bis. inversions Bis.
    pick_fresh y. apply* renaming_typ.
  - Case "ty_new_elim".
    apply narrow_typing with (G':=G') in Ht; auto.
    destruct (canonical_forms_obj Hi Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    inversions Hr.
    apply (binds_func H3) in Bis. inversions Bis.
    rewrite <- (defs_has_inv Has H5). assumption.
  - Case "ty_let".
    inversions Hr.
    * SCase "red_let_var".
      pick_fresh x. assert (x \notin L); auto. specialize (H x H1).
      apply subst_ty_trm with (y:=y) in H; auto.
      -- assert (subst_typ x y U = U). {
           apply subst_fresh_typ_dec. auto.
         }
         rewrite H2 in H.
         assert (open_trm y u = subst_trm x y (open_trm x u)). {
           apply subst_intro_trm. auto.
         }
         rewrite <- H3 in H.
         apply narrow_typing with (G':=G') in H; auto.
      -- assert (subst_typ x y T = T). {
           apply subst_fresh_typ_dec. auto.
         }
         rewrite H2. trivial.
    * SCase "red_let_let".
      clear H0 IHHt.
      assert (forall x, x \notin (L \u dom G) -> G & x ~ T ⊢ open_trm x u : U). {
        intros. assert (x \notin L); auto.
      }
      clear H.
      dependent induction Ht.
      -- apply narrow_typing with (G' := G') in Ht; eauto.
         remember ((((((((((((L \u L0) \u dom G) \u fv_ctx_types G) \u dom G')
                            \u fv_ctx_types G') \u dom e) \u fv_trm u) \u fv_trm s)
                        \u fv_trm t0) \u fv_typ U) \u fv_typ T) \u fv_typ U0) as bigL.
         econstructor; eauto. intros.
         instantiate (1 := bigL) in H2.
         unfold open_trm, open_rec_trm. fold open_rec_trm.

         assert (open_rec_trm 1 x u = u). {
           inversion H5. apply open_bound_lc_trm.
           applys lc_at_to_open_trm_val_def_defs. trivial.
         }
         rewrite H3. clear H3.

         rewrite HeqbigL in H2.
         assert (x \notin L0); auto.
         specialize (H _ H3).
         assert (subenv (G' & x ~ T) (G & x ~ T)). {
           apply subenv_push; auto.
         }
         apply narrow_typing with (G' := G' & x ~ T) in H; auto.
         rewrite <- HeqbigL in H2.
         econstructor; eauto.
         intros. instantiate (1 := bigL \u \{ x }) in H6.
         subst bigL.
         assert (x0 \notin L \u dom G); auto.
         specialize (H1 _ H7).
         assert (G' & x0 ~ U0 ⊢ open_trm x0 u : U). {
           eapply narrow_typing; [eassumption | |]; auto.
         }
         eapply (proj1 weaken_rules); eauto.
      -- eapply IHHt; eauto; intros.
         specialize (H0 _ H1).
         eapply narrow_typing; eauto.
    * SCase "red_let_trm".
      inversion Hlc.
      specialize (IHHt H3 Hok _ Hsenv Hi _ Hwf t'0 H6).
      eapply ty_let; eauto. intros.
      instantiate (1 := (((((((((L \u dom G) \u fv_ctx_types G) \u dom G')
                                \u fv_ctx_types G') \u dom e) \u fv_trm t) \u fv_trm u)
                            \u fv_trm t'0) \u fv_typ T) \u fv_typ U) in H7.
      assert (x \notin L); auto.
      specialize (H _ H8).
      apply narrow_typing with (G':=G' & x ~ T) in H; auto.
    * SCase "red_let_val".
      apply val_typing in Ht.
      destruct Ht as [T' [H1 H2]].
      pose proof (precise_inert_typ H1) as Hpit.
      pose proof H1 as Htt.
      apply precise_to_general in Htt.
      apply narrow_typing with (G':=G') in Htt; auto.
      pick_fresh x. assert (x \notin L); auto.
      assert (ok (G & x ~ T)); auto.
      assert (indc_subenv (G' & x ~ T') (G & x ~ T)). {
        apply indc_subenv_trans with (G & x ~ T'); auto. }
      assert (inert (G' & x ~ T')); auto.
      assert (G' & x ~ T' ~~ e & x ~ v). {
        constructor; auto.
      }
      assert (x \notin L0); auto.
      inversion Hlc.

      apply (proj1 (lc_at_to_open_trm_val_def_defs x)) in H14.
      specialize (H0 _ H3 H14 H5 (G' & x ~ T') H7 H8 (e & x ~ v) H9 _ (H6 _ H10)).
      apply_fresh ty_let as y; eauto.

      apply weaken_ty_trm with (G2:=(y ~ T')) in H0; auto.

      pose proof (proj1 (subst_rules y T')) as Hsubst.
      specialize (Hsubst _ _ _ H0 G' (y ~ T') x).
      assert (HsubstU : subst_typ x y U = U). {
        apply subst_fresh_typ. auto.
      }
      rewrite HsubstU in Hsubst.

      assert (Hxyt : subst_typ x y T' = T'). {
        apply subst_fresh_typ. auto.
      }

      assert (Hopeny : subst_ctx x y (y ~ T') = y ~ T'). {
        unfold subst_ctx. rewrite map_single. rewrite Hxyt. trivial.
      }
      rewrite* Hopeny in Hsubst.

      assert (Hopent : subst_trm x y (open_trm x t'0) = open_trm y t'0). {
        rewrite subst_open_commut_trm.
        rewrite (proj1 (subst_fresh_trm_val_def_defs _ _)); auto.
        unfold subst_fvar. case_if; auto.
      }
      rewrite Hopent in Hsubst.

      apply Hsubst; auto.
      rewrite Hxyt. auto.

  - apply narrow_typing with (G' := G') in Ht; auto.
    apply narrow_subtyping with (G' := G') in H; auto.
    eapply ty_sub; eauto.
Qed.


(** ** Preservation Theorem
    If [⊢ t : T] and [t |-> t'], then [⊢ t': T]. *)
Theorem preservation: forall (t t' : trm) T,
    lc_trm t ->
    ⊢ t: T ->
    t |-> t' ->
    ⊢ t' : T.
Proof.
  intros. eapply preservation_ec; eauto. constructor.
Qed.
