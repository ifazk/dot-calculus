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
Reserved Notation "s '⟦' p '⟼' t '⟧'" (at level 40).
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
    defs_has ds (def_trm a t) ->
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

Inductive lookup : sta -> path * val -> Prop :=
| lookup_def: forall s p v,
    star (lookup_step s) (trm_path p) (trm_val v) ->
    s ∋ (p, v)

where "s '∋' t" := (lookup s t).

Hint Constructors lookup lookup_open lookup_step.

Scheme lookup_mut := Induction for lookup_step Sort Prop
  with lookup_open_mut := Induction for lookup_open Sort Prop.
Combined Scheme lookup_mutind from lookup_mut, lookup_open_mut.

(** ** Lemmas about Environment Lookup *)
(*
Lemma lookup_func_mut :
  (forall s t,
    s [[ p  t -> forall p v1 v2,
    t = (p, v1) ->
    s ∋ (p, v2) ->
    v1 = v2) /\
  (forall s p ds1,
    s ↓ p == ds1 -> forall ds2,
    s ↓ p == ds2 ->
    ds1 = ds2).
Proof.
  apply lookup_mutind; intros.
  - Case "lookup_var".
    inversions H. dependent induction H0; unfolds sel_fields; try (destruct p; inversions x).
    lets Hb: (binds_func b H). subst*.
  - Case "lookup_val".
    inversions H0. inversions H1; unfolds sel_fields, pvar; destruct p.
    * inversion H0.
    * destruct p0. inversions H0. specialize (H _ _ H4). subst. lets Hd: (defs_has_inv H6 d). inversion* Hd.
    * inversions H0. destruct p0. inversions H2.
      specialize (H _ _ H3). subst. lets Hd: (defs_has_inv H5 d). inversion Hd.
  - Case "lookup_path".
    inversions H1. inversions H2; unfolds sel_fields, pvar.
    * destruct p. inversion H1.
    * destruct p0, p. inversions H1. specialize (H _ _ H5). subst. lets Hd: (defs_has_inv H7 d). inversion Hd.
    * destruct p0, p. inversions H1.  specialize (H _ _ H4). subst. lets Hd: (defs_has_inv H6 d). inversions Hd.
      inversions l. inversions H4. apply* H0.
  - Case "lookup_defs".
    lets Hl: (lookup_defs l). inversions H0. specialize (H _ _ _ _ eq_refl H1).
    inversion* H.
Qed.

Lemma lookup_func : forall s p v1 v2 ps1 ps2,
    s ∋ (p, v1) // ps1 ->
    s ∋ (p, v2) // ps2 ->
    v1 = v2.
Proof.
  intros. lets Hl: (proj21 lookup_func_mut). specialize (Hl _ _ _ H _ _ _ _ eq_refl H0). apply Hl.
Qed.
 *)

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
