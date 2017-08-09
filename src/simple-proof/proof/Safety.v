(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Narrowing.
Require Import Helper_lemmas.
Require Import Precise_types.
Require Import Substitution.
Require Import Canonical_forms.

(** * Normal Forms
A normal form is defined in the WadlerFest DOT paper as:

[n ::= x | v | let x = v in n]

This corresponds to an evaluation context of the form
[(let x = v in)* [ ]] whose hole is filled by a variable [x]
or value [v]. *)

Inductive normal_form_trm: trm -> Prop :=
| nf_var: forall x, normal_form_trm (trm_var x)
| nf_val: forall v, normal_form_trm (trm_val v).

Definition normal_form (e : ec) (t : trm) : Prop :=
  match e with
  | e_hole _   => normal_form_trm t
  | e_term _ _ => False
  end.

Hint Unfold normal_form.
Hint Constructors normal_form_trm.

Inductive closed_ec_typing : ec -> trm -> typ -> Prop :=
| cet: forall G e t T, ty_ec_trm G e t T ->
  closed_ec_typing e t T.

Notation "'|-' e '[' t ']:' T" := (closed_ec_typing e t T) (at level 40, t at level 59).

(** If the term [(let x = v in)* let x = [t] in u] represented by an
    evaluation context is locally closed, so is the term
    [(let x = v in)* [t]]. *)
Lemma lc_term_to_hole: forall s u t,
    lc_term (e_term s u) t ->
    lc_term (e_hole s) t.
Proof.
  intros. inversions H. inversions H0. repeat constructor~.
Qed.

(** * Progress *)

(** If [(let x = v in)* let y = [t] in u]
    reduces to [(let x = v in)* let y = [t'] in u],
    then [(let x = v in)* [t]]
    reduces to [(let x = v in)* [t']].

    This lemma is used to reduce cases involving [let y = [t] in u]
    into simpler cases involving [[t]]. *)
Lemma red_term_to_hole: forall s u t t',
    e_term s u / t |-> e_term s u / t' ->
    e_hole s / t |-> e_hole s / t'.
Proof.
  intros. dependent induction H.
  - eapply red_apply; eauto.
  - eapply red_project; eauto.
  - induction u; inversions x.
    eapply IHu2; eauto.
Qed.

(** ** Progress Theorem
    If [|- e[t] : T], then either [e[t]] is a normal form,
    or [e[t]] reduces to some [e'[t']]. *)
Lemma progress: forall e t T,
    |- e[t]: T ->
    (normal_form e t \/ exists e' t', e / t |-> e' / t').
Proof.
  introv Ht. destruct Ht as [* Ht]. destruct e; inversions Ht.
  - rename H0 into Hi. rename H3 into Ht. rename H1 into Hwf.
    dependent induction Ht; try solve [left; auto].
    * destruct (canonical_forms_fun Hi Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
      right. repeat eexists. apply* red_apply.
    * destruct (canonical_forms_obj Hi Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
      right. repeat eexists. apply* red_project.
    * right. exists (e_term s u) t.
      apply red_congruence_let.
    * specialize (IHHt Hi) as [IH | [t' [s' Hred]]].
      + assumption.
      + left. assumption.
      + right. exists t' s'. assumption.
  - clear H7.
    rename H1 into Hin. rename H2 into Hwf. rename H4 into Ht.
    dependent induction Ht; right.
    * repeat eexists; apply red_let_var.
    * pick_fresh x. repeat eexists; apply red_congruence_val with (x:=x); auto.
    * destruct (canonical_forms_fun Hin Hwf Ht1) as [L' [T' [t [Bis [Hsub Hty]]]]].
      repeat eexists. apply* red_apply.
    * pick_fresh x. repeat eexists; apply red_congruence_val with (x:=x); auto.
    * destruct (canonical_forms_obj Hin Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
      repeat eexists. apply* red_project.
    * repeat eexists; apply red_let_let.
    * repeat eexists; apply red_let_var.
    * repeat eexists; apply red_let_var.
    * repeat eexists; apply red_let_var.
    * specialize (IHHt Hin) as [IH | [t' [s' Hred]]]; eauto.
      inversion IH.
Qed.

(** * Preservation *)

(** Reduction preserves local closure. *)
Lemma red_preserves_lc :
  forall e t e' t',
    e / t |-> e' / t' ->
    lc_term e t ->
    lc_term e' t'.
Proof.
  intros.
  destruct H0.
  dependent induction H; try solve [inversions H1; inversions H0; split*].
  - pose proof (lc_ec_sto_inv H0).
    pose proof (lc_ec_sto_binds_inv H0 H).
    inversions H3. split~.
  - pose proof (lc_ec_sto_binds_inv H1 H). inversions H3.
    pose proof (lc_defs_has (H7 x) H0). inversions H3. split~.
  - inversions H0. inversions H1.
    split; auto. eapply lc_ec_term; auto.
    intros x. unfold open_trm.
    simpl. eapply lc_trm_let; auto.
    intros x0. unfold open_trm.
    rewrite~ (proj1 (open_comm_trm_val_def_defs x0 x)).
    rewrite~ lc_opening.
Qed.

(** Special case of type preservation for evaluation contexts of the
    form [(let x=v in)* [ ]].

    If [e] and [t] are locally closed, [|- e[t]: T],
    and [e[t] |-> e'[t']], then [|- e'[t']: T]. *)
Lemma red_preserves_type_hole: forall G s t e' t' T,
    lc_term (e_hole s) t ->
    e_hole s / t |-> e' / t' ->
    ty_ec_trm G (e_hole s) t T ->
    exists G', ty_ec_trm (G & G') e' t' T.
Proof.
  introv Hlc Hred Ht.
  inversions Ht.
  rename H0 into Hin. rename H1 into Hwf. rename H3 into Ht.
  lets Hlc': (red_preserves_lc Hred Hlc).
  dependent induction Ht; try solve [inversion Hred].
  - destruct (canonical_forms_fun Hin Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    inversions Hred.
    apply (binds_func H4) in Bis. inversions Bis.
    exists (@empty typ). rewrite concat_empty_r.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    constructor*. rewrite subst_intro_typ with (x:=y); auto.
    rewrite subst_intro_trm with (x:=y); auto.
    eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ.
  - destruct (canonical_forms_obj Hin Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    inversions Hred.
    apply (binds_func H2) in Bis. inversions Bis.
    exists (@empty typ). rewrite concat_empty_r.
    rewrite <- (defs_has_inv Has H5). constructor*.
  - inversions Hred.
    exists (@empty typ). rewrite concat_empty_r.
    eapply ty_e_term; eauto.
  - specialize (IHHt Hlc Hred Hin Hwf Hlc') as [G' IHHt].
    exists G'. inversions IHHt.
    + eapply ty_e_hole; auto.
      apply weaken_subtyp with (G2:=G') in H; eauto.
    + apply_fresh ty_e_term as z; eauto; intros. assert (z \notin L) by auto.
      specialize (H3 z H4).
      apply weaken_subtyp with (G2:=(G' & z ~ T0)) in H; rewrite concat_assoc in *; eauto.
Qed.

(** Type Preservation:
    If [e] and [t] are locally closed, [|- e[t]: T], and [e[t] |-> e'[t']],
    then [|- e'[t']: T]. *)
Lemma red_preserves_type: forall G e t e' t' T,
    lc_term e t ->
    e / t |-> e' / t' ->
    ty_ec_trm G e t T ->
    exists G', ty_ec_trm (G & G') e' t' T.
Proof.
  introv Hlc Hred Ht.
  inversions Ht; rename H into Hin; rename H0 into Hwf; rename H1 into Ht.
  inversion Hlc as [Hlc_ec Hlc_trm].
  apply* red_preserves_type_hole. constructor~.
  destruct t.
  - inversions Hred.
    pick_fresh y.
    exists (@empty typ). rewrite concat_empty_r.
    apply ty_e_hole; auto.
    rewrite subst_intro_trm with (x:=y); auto.
    rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
    eapply subst_ty_trm; auto. rewrite~ subst_fresh_typ.
  - inversions Hred.
    pose proof (wf_sto_notin_dom Hwf H5).
    pose proof (val_typing Ht) as [V [Hv Hs]].
    pick_fresh y. assert (y \notin L) by auto.
    specialize (H2 y H0).
    exists (x ~ V).
    apply ty_e_hole.
    * constructor~. eapply precise_inert_typ; eauto.
    * constructor~.
      apply (precise_to_general Hv).
    * rewrite subst_intro_trm with (x:=y); auto.
      rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
      eapply subst_ty_trm; auto.
      { eapply weaken_rules; eauto. }
      { apply~ fv_ctx_types_push. }
      {
        rewrite~ subst_fresh_typ.
        pose proof (ty_var (binds_tail x V G)).
        apply (ty_sub H1). apply (weaken_subtyp Hs); eauto.
      }
  - inversion Hred. rewrite <- H4 in Hred. apply red_term_to_hole in Hred. subst.
    apply lc_term_to_hole in Hlc.
    pose proof (red_preserves_type_hole Hlc Hred (ty_e_hole Hin Hwf Ht)) as [G' Ht'].
    inversions Ht'. exists G'.
    eapply ty_e_term with (L:=L \u (dom G) \u (dom G')); eauto. intros.
    assert (x0 \notin L) by auto.
    specialize (H2 x0 H4).
    eapply (proj41 weaken_rules); eauto.
  - inversion Hred. rewrite <- H1 in Hred.
    apply red_term_to_hole in Hred. subst.
    apply lc_term_to_hole in Hlc.
    pose proof (red_preserves_type_hole Hlc Hred (ty_e_hole Hin Hwf Ht)) as [G' Ht'].
    inversions Ht'. exists G'.
    eapply ty_e_term with (L:=L \u (dom G) \u (dom G')); eauto. intros.
    eapply (proj41 weaken_rules); eauto.
  - inversions Hred.
    exists (@empty typ). rewrite concat_empty_r.
    gen L.
    dependent induction Ht; intros.
    + eapply ty_e_term with (L:=L \u (dom G)); eauto. intros.
      assert (x \notin L) by auto.
      unfold open_trm. simpl. specialize (H x H3).
      apply_fresh ty_let as z; eauto.
      unfold open_trm.
      rewrite~ (proj41 (open_comm_trm_val_def_defs z x)).
      inversion Hlc as [Hlc_ec Hlc_trm].
      inversions Hlc_ec. specialize (H7 z).
      apply (lc_opening 1 x) in H7. unfold open_trm in H7. rewrite H7.
      assert (z \notin L0) by auto.
      specialize (H2 z H4).
      eapply weaken_rules; eauto.
    + eapply IHHt with (L:=L \u (dom G)); auto. intros.
      assert (x \notin L) by auto.
      specialize (H2 x H1).
      eapply narrow_typing; eauto. apply~ subenv_last.
Qed.

(** ** Preservation Theorem
    Reduction preserves both local closure and the type of the term being reduced.

    If [e] and [t] are locally closed, [|- e[t]: T], and [e[t] |-> e'[t']], then
    [e'] and [t'] are locally closed and [|- e'[t']: T]. *)
Lemma preservation: forall e t e' t' T,
    lc_term e t ->
    e / t |-> e' / t' ->
    |- e [t]: T ->
    lc_term e' t' /\ |- e' [t']: T.
Proof.
  introv Hl Hr Ht. split. apply* red_preserves_lc. destruct Ht.
  destruct (red_preserves_type Hl Hr H) as [G' Hty].
  econstructor. eauto.
Qed.
