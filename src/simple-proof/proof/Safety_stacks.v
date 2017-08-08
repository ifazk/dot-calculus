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
Require Import Safety.
Require Import Invertible_typing.
Require Import General_to_tight.

Reserved Notation "s1 '//' t1 '|->' s2 '//' t2" (at level 40, s2 at level 39).

Inductive sto_red : trm -> sto -> trm -> sto -> Prop :=
| red_sel : forall x m s t T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    s // trm_sel (avar_f x) m |-> s // t
| red_app : forall f a s T t,
    binds f (val_lambda T t) s ->
    s // trm_app (avar_f f) (avar_f a) |-> s // open_trm a t
| red_let : forall v t s x,
    x # s ->
    s // trm_let (trm_val v) t |-> s & x ~ v // open_trm x t
| red_let_var : forall t s x,
    s // trm_let (trm_var (avar_f x)) t |-> s // open_trm x t
| red_let_tgt : forall t0 t s t0' s',
    s // t0 |-> s' // t0' ->
    s // trm_let t0 t |-> s' // trm_let t0' t
where "s1 // t1 |-> s2 // t2" := (sto_red t1 s1 t2 s2).

Inductive sto_trm_typ : sto -> trm -> typ -> Prop :=
| sto_trm_typ_c : forall G s t T,
    inert G ->
    G ~~ s ->
    G |- t : T ->
    sto_trm_typ s t T.

Notation "'|-' s ',' t ':' T" := (sto_trm_typ s t T) (at level 40, t at level 59).

Inductive norm_form: trm -> Prop :=
| nf_var: forall x, norm_form (trm_var x)
| nf_val: forall v, norm_form (trm_val v).

Hint Constructors norm_form.

Theorem safety : forall s t T,
    |- s, t: T ->
    (norm_form t \/ exists s' t', s // t |-> s' // t' /\ |- s', t': T).
Proof.
  destruct 1 as [* Hi Hwf Ht].
  induction Ht; try solve [left; eauto].
  - Case "All-E".
    right. destruct (canonical_forms_fun Hi Hwf Ht1) as [L [T' [t [Hb [Hs Hy]]]]].
    Admitted.

Theorem preservation : forall s s' t t' T,
    |- s, t : T ->
    s // t |-> s' // t' ->
    exists s' t', |- s', t' : T.
Proof. eauto using safety. Qed.

Theorem progress: forall s t T,
    |- s, t : T ->
    (exists s' t', s // t |-> s' // t') \/ norm_form t.
Proof.
  intros. destruct (safety H) as [Hn | [s'' [t'' [Hred Hty]]]]; eauto.
Qed.
