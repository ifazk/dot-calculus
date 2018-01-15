(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas about opening, closing, and local closure. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import LibLN.
Require Import Sequences.
Require Import Definitions Binding.

(** * Environment Lookup *)

(** * Path lookup *)

(** Looking up a path in a stack (generalization of variable binding). *)

Reserved Notation "s '∋' t" (at level 40).
Reserved Notation "s '⟦' t '⟼' u '⟧'" (at level 40).
Reserved Notation "s '↓' p '==' ds" (at level 40).

Inductive lookup_step : sta -> trm -> trm -> Prop :=

(** [s(x) = v ]   #<br>#
    [―――――――――]   #<br>#
    [s[x ⟼ v]]   *)
| lookup_var : forall s x v,
    binds x v s ->
    s ⟦ trm_path (pvar x) ⟼ trm_val v ⟧

(** [s ↓ p = ...{a = t}... ]   #<br>#
    [――――――――――――――――――――――]   #<br>#
    [s[p.a ⟼ t]]              *)
| lookup_sel : forall s p ds a t,
    s ↓ p == ds ->
    defs_has ds { a := t } ->
    s ⟦ trm_path p•a ⟼ t ⟧

where "s '⟦' p '⟼' t '⟧'" := (lookup_step s p t)

(** Opening of definitions:
    If [s ∋ (p, ν(x: T)ds)], then [lookup_open] gives us [ds] opened with [p]. *)

with lookup_open : sta -> path -> defs -> Prop :=

(** [s [[ p ⟼ ν(T)ds ]] ]    #<br>#
    [――――――――――――――――――――]    #<br>#
    [s ↓ p = ds^p        ]        *)
| lookup_defs : forall s p T ds,
    s ⟦ trm_path p ⟼ trm_val (val_new T ds) ⟧ ->
    s ↓ p == open_defs_p p ds

where "s '↓' p '==' ds" := (lookup_open s p ds).

Notation "s '⟦' t '⟼*' u '⟧'" := (star (lookup_step s) t u) (at level 40).

Inductive lookup : sta -> path * val -> Prop :=
| lookup_def: forall s p v,
    s ⟦ trm_path p ⟼* trm_val v ⟧ ->
    s ∋ (p, v)

where "s '∋' t" := (lookup s t).

Hint Constructors lookup lookup_open lookup_step.

Scheme lookup_mut := Induction for lookup_step Sort Prop
  with lookup_open_mut := Induction for lookup_open Sort Prop.
Combined Scheme lookup_mutind from lookup_mut, lookup_open_mut.

(** ** Lemmas about Environment Lookup *)

Lemma lookup_empty_mut :
  (forall s t u,
      s ⟦ t ⟼ u ⟧ ->
      s = empty ->
      False) /\
  (forall s p ds,
      s ↓ p == ds ->
      s = empty ->
      False).
Proof.
  apply lookup_mutind; auto. intros. subst. false* binds_empty_inv.
Qed.

Lemma lookup_empty : forall t u,
    empty ⟦ t ⟼ u ⟧ -> False.
Proof.
  intros. eapply (proj21 lookup_empty_mut); eauto.
Qed.

Lemma lookup_push_eq_inv_var :
    forall s x v t,
    s & x ~ v ⟦ tvar x ⟼ t ⟧ ->
    t = trm_val v.
Proof.
  introv Hx. inversions Hx;
    try (destruct (last_field _ _ H) as [bs Hbs]; inversion Hbs).
  apply binds_push_eq_inv in H1. subst*.
Qed.

Lemma lookup_push_neq : forall s x bs v y t,
    s ⟦ trm_path (p_sel (avar_f x) bs) ⟼ t ⟧ ->
    x <> y ->
    s & y ~ v ⟦ trm_path (p_sel (avar_f x) bs) ⟼ t ⟧.
Proof.
  introv Hp Hn. dependent induction Hp.
  Admitted.

Lemma lookup_strengthen: forall s y v x bs t,
    s & y ~ v ⟦ trm_path (p_sel (avar_f x) bs) ⟼ t ⟧ ->
    y <> x ->
    s ⟦ trm_path (p_sel (avar_f x) bs) ⟼ t ⟧.
Proof.
Admitted.

(*
Lemma named_path_lookup:
    (forall s t ps,
        s ∋ t // ps -> forall p v,
        t = (p, v) ->
        exists x bs, p = p_sel (avar_f x) bs) /\
    (forall s p ds ps,
        s ↓ p == ds // ps ->
        exists x bs, p = p_sel (avar_f x) bs).
Proof.
  apply lookup_mutind; intros.
  - inversions H. repeat eexists.
  - destruct_all. inversions H0. repeat eexists.
  - inversions H1. destruct_all. subst. repeat eexists.
  - eauto.
Qed.

Lemma named_path_lookup_l: forall s p ps v,
    s ∋ (p, v) // ps ->
    exists x bs, p = p_sel (avar_f x) bs.
Proof.
  intros. apply* (proj21 named_path_lookup).
Qed.

(** * Testing lookup definition *)

Variables a b c d: trm_label.
Variables x y z: var.
Hypothesis Hab: a <> b.
Hypothesis Hxy: y <> x.

(* λ(z: ⊤)0.c *)
Definition lambda := val_lambda typ_top (trm_path (p_sel (avar_b 0) (c :: nil))).

(* ν(z: {d: ⊤}) {d = z.d} *)
Definition zObj :=
  val_new (typ_rcd (dec_trm d typ_top))
          (defs_cons defs_nil
                     (def_trm d (trm_path (p_sel (avar_b 0) (d :: nil))))).

(* ν(y: {c: ⊤})
        {c = λ(z: ⊤)y.c} *)
Definition yObj :=
  val_new (typ_rcd (dec_trm c typ_top))
          (defs_cons defs_nil
                     (def_trm c (trm_val lambda))).

(* ν(x: {a: ⊤}    ∧ {b: ⊤})
        {a = x.b} ∧ {b = y.c} *)
Definition xObj :=
  val_new (typ_and
             (typ_rcd (dec_trm a typ_top))
             (typ_rcd (dec_trm b typ_top)))
          (defs_cons (defs_cons defs_nil
             (def_trm b (trm_path (p_sel (avar_f y) (c :: nil)))))
             (def_trm a (trm_path (p_sel (avar_b 0) (b :: nil))))).

(* {y = yObj, x = xObj} *)
Definition s := (y ~ yObj & x ~ xObj).

(* s ∋ (x.a, λ(x: ⊤)y.c) // [x.b]*)
Lemma test_lookup_x:
  exists ps,
  s ∋ ((pvar x) • a, open_val y lambda) // ps. (*(((pvar x) • b) :: ((pvar y) • c) :: nil).*)
Proof.
  simpl. eexists. rewrite proj_rewrite.
  apply* lookup_path; unfold s.
  - econstructor. apply* lookup_var. apply binds_push_eq.
  - unfold defs_has. simpl. repeat case_if. eauto.
  - rewrite proj_rewrite. apply* lookup_path.
    * econstructor. apply* lookup_var. apply binds_push_eq.
    * unfold defs_has. simpl. repeat case_if*. inversions C. false* Hab.
    * assert (p_sel (avar_f y) (c :: nil) = (pvar y) • c) as Heq by auto. rewrite Heq.
      apply* lookup_val.
      econstructor. apply* lookup_var. apply binds_push_neq. apply binds_single_eq. apply Hxy.
      unfold defs_has. simpl. repeat case_if. unfold lambda, open_val. simpl. case_if*.
Qed.

Definition s2 := z ~ zObj.

Lemma test_lookup_z: forall ps v,
  s2 ∋ (p_sel (avar_f z) (d :: nil), v) // ps -> False.
Proof.
  introv H.
  dependent induction H; assert (s2 ∋ (pvar z, zObj) // nil) as Hb by (apply* lookup_var; apply* binds_single_eq).
  - unfolds sel_fields. destruct p. inversions x.
    inversions H. unfolds zObj.
    lets Hl: (lookup_func Hb H1). inversions Hl. unfolds defs_has. simpls. repeat case_if.
  - inversions H. unfolds sel_fields. destruct p. inversions x. simpls.
    lets Hl: (lookup_func H2 Hb). inversions Hl. inversions H0. repeat case_if. inversions H3. eauto.
Qed.
*)

Lemma lookup_inv_path_t: forall s t u,
    s ⟦ t ⟼ u ⟧ ->
    exists p, t = trm_path p.
Proof.
  introv Hs. induction Hs; eauto.
Qed.

Lemma lookup_inv_path_u: forall s t u,
    s ⟦ t ⟼ u ⟧ ->
    (exists p, u = trm_path p) \/ (exists v, u = trm_val v).
Proof.
  introv Hs. Admitted.


Lemma lookup_val_inv: forall s v t,
    s ⟦ trm_val v ⟼* t ⟧ ->
    t = trm_val v.
Proof.
  introv Hs. dependent induction Hs. auto. inversion H.
Qed.

Lemma lookup_path_inv: forall s t p,
    s ⟦ t ⟼* trm_path p ⟧ ->
    exists q, t = trm_path q.
Proof.
  introv Hs. dependent induction Hs; eauto. destruct (IHHs _ eq_refl) as [q Heq]. subst.
  inversions H; eauto.
Qed.

Lemma lookup_last_path: forall s p v,
    s ∋ (p, v) ->
    exists q, s ⟦ trm_path p ⟼* trm_path q ⟧ /\
         s ⟦ trm_path q ⟼ trm_val v ⟧.
Proof.
  introv Hl.
  inversions Hl. dependent induction H1.
  destruct (lookup_inv_path_u H) as [[q Heq] | [w Heq]]; subst.
  - specialize (IHstar _ _ eq_refl eq_refl). destruct IHstar as [r [Hs Hl]].
    exists r. split. eapply star_trans. apply star_one. apply  H. all: auto.
  - apply lookup_val_inv in H1. inversions H1.
    exists p. split*. apply star_refl.
Qed.

Lemma lookup_step_func_mut :
  (forall s t t1,
      s ⟦ t ⟼ t1 ⟧ -> forall t2,
      s ⟦ t ⟼ t2 ⟧ ->
      t1 = t2) /\
  (forall s p ds1,
    s ↓ p == ds1 -> forall ds2,
    s ↓ p == ds2 ->
    ds1 = ds2).
Proof.
  apply lookup_mutind; intros.
  - Case "lookup_var".
    inversions H. lets Hb: (binds_func b H2). subst*.
    unfolds sel_fields. destruct p. inversion H0.
  - Case "lookup_sel".
    inversions H0; unfolds sel_fields; destruct p. inversion H1. destruct p0.
    inversions H1. specialize (H _ H2). subst. apply* defs_has_inv.
  - Case "lookup_defs".
    lets Hl: (lookup_defs l). inversions H0. specialize (H _ H1). inversion* H.
Qed.

Lemma lookup_step_func: forall s t t1 t2,
      s ⟦ t ⟼ t1 ⟧ ->
      s ⟦ t ⟼ t2 ⟧ ->
      t1 = t2.
Proof.
  intros. apply* lookup_step_func_mut.
Qed.

Lemma lookup_irred: forall s v,
    irred (lookup_step s) (trm_val v).
Proof.
  inversion 1.
Qed.

Lemma lookup_func : forall s p v1 v2,
    s ∋ (p, v1) ->
    s ∋ (p, v2) ->
    v1 = v2.
Proof.
  introv Hs1 Hs2.
  lets H: (lookup_step_func). specialize (H s). inversions Hs1. inversions Hs2.
  assert (irred (lookup_step s) (trm_val v1)) as Hirr1 by apply* lookup_irred.
  assert (irred (lookup_step s) (trm_val v2)) as Hirr2 by apply* lookup_irred.
  lets Hf: (finseq_unique H H2 Hirr1 H3 Hirr2). inversion* Hf.
Qed.
