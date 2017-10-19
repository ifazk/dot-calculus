(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas about opening, closing, and local closure. *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

(** * Lemmas About Opening *)

Ltac avar_solve :=
  repeat match goal with
  | [ a: avar |- _ ] =>
    destruct a; simpl; auto; repeat case_if; subst; simpls; repeat case_if*;
    subst; simpls; repeat case_if*
  end.

(** The following [open_fresh_XYZ_injective] lemmas state that given two
    symbols (variables, types, terms, etc.) [X] and [Y] and a variable [z],
    if [z \notin fv(X)] and [z \notin fv(Y)], then [X^z = Y^z] implies [X = Y]. *)

(** - variables *)
Lemma open_fresh_avar_injective : forall x y k z,
    z \notin fv_avar x ->
    z \notin fv_avar y ->
    open_rec_avar k z x = open_rec_avar k z y ->
    x = y.
Proof.
  intros. avar_solve; inversion* H1; try (inversions H3; false* notin_same).
Qed.

(** - types and declarations *)
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

  Ltac invert_open :=
    match goal with
    | [ H: open_rec_typ _ _ _ = open_rec_typ _ _ ?T' |- _ ] =>
       destruct T'; inversions* H
    | [ H: open_rec_dec _ _ _ = open_rec_dec _ _ ?D' |- _ ] =>
       destruct D'; inversions* H
    end.

  apply typ_mutind; intros; invert_open; simpl in *;
    f_equal; eauto using open_fresh_avar_injective.
Qed.

(** The following [lc_open_rec_open_XYZ] lemmas state that if opening
    a symbol (variables, types, terms, etc.) at index [n] that is
    already opened at index [m] results in the same opened symbol,
    opening the symbol itself at index [n] results in the same symbol. *)


(** - types and declarations *)
Lemma lc_open_rec_open_typ_dec: forall x y,
    (forall T n m,
        n <> m ->
        open_rec_typ n x (open_rec_typ m y T) = open_rec_typ m y T ->
        open_rec_typ n x T = T) /\
    (forall D n m,
        n <> m ->
        open_rec_dec n x (open_rec_dec m y D) = open_rec_dec m y D ->
        open_rec_dec n x D = D).
Proof.
  introv. apply typ_mutind; intros; simpls; auto; avar_solve;
            try solve [(inversions H1; erewrite H; eauto)
                      || (inversions H2; erewrite H; eauto; erewrite H0; eauto)].
  - inversions H1. rewrite H with (m:=S m); auto.
  - inversions H2. erewrite H; eauto. rewrite H0 with (m:=S m); auto.
Qed.

(** - terms, values, definitions, and list of definitions *)
Lemma lc_open_rec_open_trm_val_def_defs: forall x y,
    (forall t n m,
        n <> m ->
        open_rec_trm n x (open_rec_trm m y t) = open_rec_trm m y t ->
        open_rec_trm n x t = t) /\
    (forall v n m,
        n <> m ->
        open_rec_val n x (open_rec_val m y v) = open_rec_val m y v ->
        open_rec_val n x v = v) /\
    (forall d n m,
        n <> m ->
        open_rec_def n x (open_rec_def m y d) = open_rec_def m y d ->
        open_rec_def n x d = d) /\
    (forall ds n m,
        n <> m ->
        open_rec_defs n x (open_rec_defs m y ds) = open_rec_defs m y ds ->
        open_rec_defs n x ds = ds).
Proof.
  intros.
  pose proof (proj21 (lc_open_rec_open_typ_dec x y)) as Htyp.
  apply trm_mutind;
    intros; simpls; auto;
      match goal with
      | [ H : _ = _ |- _ ] => injection H as ?; f_equal; eauto
      end; avar_solve.
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
    try apply open_fv_typ_dec; auto.
Qed.


(** * Local Closure

  Our definition of [trm] accepts terms that contain de Bruijn indices that are unbound.
  A symbol [X] is considered locally closed, denoted [lc X], if all de Bruijn indices
  in [X] are bound.
   We will require a term to be locally closed in the final safety theorem. *)

(** Only named variables are locally closed. *)
Inductive lc_at_var (k : nat) : avar -> Prop :=
| lc_at_f : forall x, lc_at_var k (avar_f x)
| lc_at_b : forall i, i < k -> lc_at_var k (avar_b i).
Hint Constructors lc_at_var.


(** Locally closed types and declarations. *)
Inductive lc_at_typ (k : nat) : typ -> Prop :=
| lc_at_typ_top : lc_at_typ k typ_top
| lc_at_typ_bot : lc_at_typ k typ_bot
| lc_at_typ_rcd : forall D,
    lc_at_dec k D ->
    lc_at_typ k (typ_rcd D)
| lc_at_typ_and : forall T1 T2,
    lc_at_typ k T1 ->
    lc_at_typ k T2 ->
    lc_at_typ k (typ_and T1 T2)
| lc_at_typ_sel : forall x L,
    lc_at_var k x ->
    lc_at_typ k (typ_sel x L)
| lc_at_typ_bnd : forall T,
    lc_at_typ (S k) T ->
    lc_at_typ k (typ_bnd T)
| lc_at_typ_all : forall T1 T2,
    lc_at_typ (S k) T2 ->
    lc_at_typ k T1 ->
    lc_at_typ k (typ_all T1 T2)
with lc_at_dec (k : nat) : dec -> Prop :=
| lc_at_dec_typ : forall L T U,
    lc_at_typ k T ->
    lc_at_typ k U ->
    lc_at_dec k (dec_typ L T U)
| lc_at_dec_trm : forall a T,
    lc_at_typ k T ->
    lc_at_dec k (dec_trm a T).
Hint Constructors lc_at_typ lc_at_dec.


(** Locally closed terms, values, and definitions. *)
Inductive lc_at_trm (k : nat) : trm -> Prop :=
| lc_at_trm_var : forall a,
    lc_at_var k a ->
    lc_at_trm k (trm_var a)
| lc_at_trm_val : forall v,
    lc_at_val k v ->
    lc_at_trm k (trm_val v)
| lc_at_trm_sel : forall x a,
    lc_at_var k x ->
    lc_at_trm k (trm_sel x a)
| lc_at_trm_app : forall f a,
    lc_at_var k f ->
    lc_at_var k a ->
    lc_at_trm k (trm_app f a)
| lc_at_trm_let : forall t1 t2,
    lc_at_trm k t1 ->
    lc_at_trm (S k) t2 ->
    lc_at_trm k (trm_let t1 t2)
with lc_at_val (k : nat) : val -> Prop :=
| lc_at_val_new : forall T ds,
    lc_at_typ (S k) T ->
    lc_at_defs (S k) ds ->
    lc_at_val k (val_new T ds)
| lc_at_val_lam : forall T t,
    lc_at_typ k T ->
    lc_at_trm (S k) t ->
    lc_at_val k (val_lambda T t)
with lc_at_def (k : nat) : def -> Prop :=
| lc_at_def_typ : forall L T,
    lc_at_typ k T ->
    lc_at_def k (def_typ L T)
| lc_at_def_trm : forall a t,
    lc_at_trm k t ->
    lc_at_def k (def_trm a t)
with lc_at_defs (k : nat) : defs -> Prop :=
| lc_at_defs_nil : lc_at_defs k defs_nil
| lc_at_defs_cons : forall ds d,
    lc_at_defs k ds ->
    lc_at_def k d ->
    lc_at_defs k (defs_cons ds d).
Hint Constructors lc_at_trm lc_at_val lc_at_def lc_at_defs.


Notation "'lc_var' x" := (lc_at_var 0 x) (at level 0).
Notation "'lc_typ' T" := (lc_at_typ 0 T) (at level 0).
Notation "'lc_dec' D" := (lc_at_dec 0 D) (at level 0).

Notation "'lc_trm' t" := (lc_at_trm 0 t) (at level 0).
Notation "'lc_val' v" := (lc_at_val 0 v) (at level 0).
Notation "'lc_def' d" := (lc_at_def 0 d) (at level 0).
Notation "'lc_defs' ds" := (lc_at_defs 0 ds) (at level 0).


Scheme lc_at_trm_mut  := Induction for lc_at_trm Sort Prop
with   lc_at_val_mut  := Induction for lc_at_val Sort Prop
with   lc_at_def_mut  := Induction for lc_at_def Sort Prop
with   lc_at_defs_mut := Induction for lc_at_defs Sort Prop.
Combined Scheme lc_at_mutind from lc_at_trm_mut, lc_at_val_mut, lc_at_def_mut, lc_at_defs_mut.

Scheme lc_at_typ_mut := Induction for lc_at_typ Sort Prop
with   lc_at_dec_mut := Induction for lc_at_dec Sort Prop.
Combined Scheme lc_at_typ_mutind from lc_at_typ_mut, lc_at_dec_mut.


(** Locally closed stores *)
Inductive lc_sto : sto -> Prop :=
| lc_sto_empty : lc_sto empty
| lc_sto_cons : forall x v s,
    lc_sto s ->
    lc_val v ->
    lc_sto (s & x ~ v).
Hint Constructors lc_sto.


Lemma lc_at_relaxing_typ_dec :
    (forall T k j, lc_at_typ k T -> j >= k -> lc_at_typ j T) /\
    (forall D k j, lc_at_dec k D -> j >= k -> lc_at_dec j D).
Proof with auto.
  apply typ_mutind; intros; simpl; auto;
    match goal with
    | [ H : lc_at_typ _ _ |- _ ] => inversions H
    | [ H : lc_at_dec _ _ |- _ ] => inversions H
    end;
    try match goal with
    | [ H : lc_at_var _ _ |- _ ] => inversions H
    end;
    repeat constructor;
    try match goal with
        | [ H : _ -> _ |- _ ] => eapply H; try eassumption
        end;
    omega.
Qed.


Lemma lc_at_relaxing_trm_val_def_defs:
  (forall t k j, lc_at_trm k t -> j >= k -> lc_at_trm j t) /\
  (forall v k j, lc_at_val k v -> j >= k -> lc_at_val j v) /\
  (forall d k j, lc_at_def k d -> j >= k -> lc_at_def j d) /\
  (forall ds k j, lc_at_defs k ds -> j >= k -> lc_at_defs j ds).
Proof.
  apply trm_mutind; intros; simpl; auto;
    match goal with
    | [ H : lc_at_trm _ _ |- _ ] => inversions H
    | [ H : lc_at_val _ _ |- _ ] => inversions H
    | [ H : lc_at_def _ _ |- _ ] => inversions H
    | [ H : lc_at_defs _ _ |- _ ] => inversions H
    | [ H : lc_at_typ _ _ |- _ ] => inversions H
    end;
    repeat match goal with
           | [ H : lc_at_var _ _ |- _ ] => inversions H
           end;
    repeat constructor;
    try eapply lc_at_relaxing_typ_dec; try eassumption;
    try match goal with
        | [ H : _ -> _ |- _ ] => eapply H; try eassumption
        end;
    omega.
Qed.


Lemma lc_at_to_open_avar : forall x v k,
    lc_at_var (S k) v -> lc_at_var k (open_rec_avar k x v).
Proof with auto.
  intros. inversion H; subst; repeat constructor.
  simpl. case_if...
  constructor. omega.
Qed.


Lemma lc_at_to_open_typ_dec : forall x,
    (forall T k, lc_at_typ (S k) T -> lc_at_typ k (open_rec_typ k x T)) /\
    (forall D k, lc_at_dec (S k) D -> lc_at_dec k (open_rec_dec k x D)).
Proof.
  intro x.
  apply typ_mutind; intros; simpl; auto;
    match goal with
    | [ H : lc_at_typ (S _) _ |- _ ] => inversions H
    | [ H : lc_at_dec (S _) _ |- _ ] => inversions H
    end;
    try solve [constructor; try fold open_rec_dec; try fold open_rec_typ; auto];
    solve [repeat constructor; apply lc_at_to_open_avar; auto].
Qed.


Lemma lc_at_to_open_trm_val_def_defs : forall x,
    (forall t k, lc_at_trm (S k) t -> lc_at_trm k (open_rec_trm k x t)) /\
    (forall v k, lc_at_val (S k) v -> lc_at_val k (open_rec_val k x v)) /\
    (forall d k, lc_at_def (S k) d -> lc_at_def k (open_rec_def k x d)) /\
    (forall ds k, lc_at_defs (S k) ds -> lc_at_defs k (open_rec_defs k x ds)).
Proof.
  intro x.
  apply trm_mutind; intros; simpl; auto;
    match goal with
    | [ H : lc_at_trm (S _) _ |- _ ] => inversions H
    | [ H : lc_at_val (S _) _ |- _ ] => inversions H
    | [ H : lc_at_def (S _) _ |- _ ] => inversions H
    | [ H : lc_at_defs (S _) _ |- _ ] => inversions H
    | [ H : lc_at_typ (S _) _ |- _ ] => inversions H
    end;
    repeat constructor; auto;
    try solve [try fold open_rec_trm; auto];
    try solve [apply lc_at_to_open_typ_dec; auto];
    solve [apply lc_at_to_open_avar; auto].
Qed.


Lemma open_to_lc_at_avar : forall x v k, lc_at_var k (open_rec_avar k x v) -> lc_at_var (S k) v.
Proof.
  intros. inversion H; subst;
      destruct v; simpl in *;
        try case_if; subst; repeat constructor; auto.
  inversion H0. omega.
Qed.


Lemma open_to_lc_at_typ_dec : forall x,
    (forall T k, lc_at_typ k (open_rec_typ k x T) -> lc_at_typ (S k) T) /\
    (forall D k, lc_at_dec k (open_rec_dec k x D) -> lc_at_dec (S k) D).
Proof with eauto.
  intro x.
  apply typ_mutind; intros; simpl; auto;
    match goal with
    | [ H : lc_at_typ _ _ |- _ ] => inversions H
    | [ H : lc_at_dec _ _ |- _ ] => inversions H
    end;
    repeat constructor; auto;
      eapply open_to_lc_at_avar...
Qed.


Lemma open_to_lc_at_trm_val_def_defs : forall x,
    (forall t k, lc_at_trm k (open_rec_trm k x t) -> lc_at_trm (S k) t) /\
    (forall v k, lc_at_val k (open_rec_val k x v) -> lc_at_val (S k) v) /\
    (forall d k, lc_at_def k (open_rec_def k x d) -> lc_at_def (S k) d) /\
    (forall ds k, lc_at_defs k (open_rec_defs k x ds) -> lc_at_defs (S k) ds).
Proof.
  intro x.
  apply trm_mutind; intros; simpl;
    match goal with
    | [ H : lc_at_trm _ _ |- _ ] => inversions H
    | [ H : lc_at_val _ _ |- _ ] => inversions H
    | [ H : lc_at_def _ _ |- _ ] => inversions H
    | [ H : lc_at_defs _ _ |- _ ] => inversions H
    | [ H : lc_at_typ _ _ |- _ ] => inversions H
    end;
    repeat constructor; auto;
    try solve [try fold open_rec_trm; auto];
    first [eapply open_to_lc_at_typ_dec | eapply open_to_lc_at_avar]; eauto.
Qed.


Lemma open_left_inverse_close_avar:
  forall v x k, lc_at_var k v -> open_rec_avar k x (close_rec_avar k x v) = v.
Proof with auto.
  intros. unfold open_rec_avar, close_rec_avar.
  inversion H; repeat case_if; subst...
  omega.
Qed.
Hint Resolve open_left_inverse_close_avar.


Lemma open_left_inverse_close_typ_dec:
  (forall T x k, lc_at_typ k T -> open_rec_typ k x (close_rec_typ k x T) = T) /\
  (forall D x k, lc_at_dec k D -> open_rec_dec k x (close_rec_dec k x D) = D).
Proof with auto.
  apply typ_mutind; intros; simpl in *; auto;
  match goal with
  | [ H : lc_at_typ _ _ |- _ ] => inversions H
  | [ H : lc_at_dec _ _ |- _ ] => inversions H
  end;
  try apply func_eq_2;
  try apply func_eq_1...
Qed.


Lemma open_left_inverse_close_trm_val_def_defs :
  (forall t k x, lc_at_trm k t -> open_rec_trm k x (close_rec_trm k x t) = t) /\
  (forall v k x, lc_at_val k v -> open_rec_val k x (close_rec_val k x v) = v) /\
  (forall d k x, lc_at_def k d -> open_rec_def k x (close_rec_def k x d) = d) /\
  (forall ds k x, lc_at_defs k ds -> open_rec_defs k x (close_rec_defs k x ds) = ds).
Proof.
  apply trm_mutind; intros; simpl in *; auto;
    match goal with
    | [ H : lc_at_trm _ _ |- _ ] => inversions H
    | [ H : lc_at_val _ _ |- _ ] => inversions H
    | [ H : lc_at_def _ _ |- _ ] => inversions H
    | [ H : lc_at_defs _ _ |- _ ] => inversions H
    end;
    try apply func_eq_2;
    try apply func_eq_1; auto;
      apply open_left_inverse_close_typ_dec; auto.
Qed.


(** The following [lc_at_opening_XYZ] lemmas state that opening a locally
    closed symbol (variables, types, terms, etc.) at any index
    results in the same symbol. *)

(** - variables *)
Lemma lc_at_opening_avar: forall m n x y,
    n >= m ->
    lc_at_var m y ->
    open_rec_avar n x y = y.
Proof.
  introv Hge Hl. inversion Hl; simpls~.
  case_if~. omega.
Qed.


(** - types and declarations *)
Lemma lc_at_opening_typ_dec: forall x m,
    (forall T, lc_at_typ m T -> forall n, n >= m -> open_rec_typ n x T = T) /\
    (forall D, lc_at_dec m D -> forall n, n >= m -> open_rec_dec n x D = D).
Proof.
  Local Hint Resolve lc_at_opening_avar.
  intro x. apply lc_at_typ_mutind; intros; simpls; f_equal*;
  match goal with
  | [ H : _ -> _ -> open_rec_typ _ _ _ = _ |- _ ] => apply H
  end; omega.
Qed.


(** - terms, values, definitions, and list of definitions *)
Lemma lc_at_opening_trm_val_def_defs: forall x m,
  (forall t, lc_at_trm m t -> forall n, n >= m -> open_rec_trm n x t = t) /\
  (forall v, lc_at_val m v -> forall n, n >= m -> open_rec_val n x v = v) /\
  (forall d, lc_at_def m d -> forall n, n >= m -> open_rec_def n x d = d) /\
  (forall ds, lc_at_defs m ds -> forall n, n >= m -> open_rec_defs n x ds = ds).
Proof.
  Local Hint Resolve lc_at_opening_avar.
  intro x.
  apply lc_at_mutind; intros; simpls; f_equal*;
    try solve
        [match goal with
         | [ H : _ -> _ -> ?f _ _ ?t = ?t |- ?f _ _ ?t = ?t ] => apply H
         end; omega];
  eapply lc_at_opening_typ_dec;
    try eassumption;
    try omega.
Qed.


(** The [lc_at_opening_trm_val_def_defs] lemma, specialized to terms. *)
Lemma lc_at_opening : forall t n x,
    lc_trm t ->
    open_rec_trm n x t = t.
Proof.
  intros. eapply lc_at_opening_trm_val_def_defs; try eassumption; try omega.
Qed.


(** * Lemmas About Local Closure *)

(** When a binding is removed from a locally closed store, the
    resulting store and the value in the binding are both
    locally closed. *)
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


(** Values in a locally closed store are also locally closed. *)
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


(** A definition in a locally closed list of definitions is also
    locally closed. *)
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
    + inversions H0. inversion H; auto.
    + apply IHds; auto. inversion H; auto.
Qed.

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
