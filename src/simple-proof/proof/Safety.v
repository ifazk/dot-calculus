(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions.
Require Import Operational_semantics.
Require Import Weakening Narrowing Helper_lemmas Precise_types Substitution Canonical_forms.

(** Reduction in an empty context *)
Notation "t '|->' u" := (empty [t |-> u]) (at level 50).

(** Typing in an empty context *)
Notation "'|-' t ':' T" := (empty |- t: T) (at level 40, t at level 59).

(** * Progress *)

(** todo: doc*)
Lemma progress_ec: forall G e t T,
    G |- e[t]: T ->
    (normal_form t \/ exists t', e[t |-> t']).
Proof.
  destruct 1 as [* Hwf Ht]. induction Ht; eauto.
  - Case "ty_all_elim". admit.
  - Case "ty_new_elim". admit.
  - Case "ty_let". admit.
Qed.


(** ** Progress Theorem
    If [|- t : T], then either [t] is a normal form,
    or [t]] reduces to some [t']. *)
Theorem progress: forall t T,
    |- t: T ->
    normal_form t \/ (exists t', t |-> t').
Proof.
  introv Ht. assert (empty |- empty[t]: T) as He by (repeat constructor*).
  apply* progress_ec.
Qed.

(** * Preservation *)

Lemma preservation_ec: forall G e t t' T,
  G |- e[t]: T ->
  e[t |-> t'] ->
  G |- e[t']: T.
Proof.
  destruct 1 as [* Hwf Ht]. induction Ht.
  - Case "ty_var". admit.
  - Case "ty_all_intro". admit.
  - Case "ty_all_elim". admit.
  - Case "ty_new_intro". admit.
  - Case "ty_new_elim". admit.
  - Case "tylet". admit.
  - Case "ty_rec_intro". admit.
  - Case "ty_rec_elim". admit.
  - Case "ty_and_intro". admit.
  - Case "ty_sub". admit.
Qed.

(** ** Preservation Theorem
    If [|- t : T] and [t |-> t'], then [|- t': T]. *)
Theorem preservation: forall (t t' : trm) T,
  |- t: T ->
  t |-> t' ->
  |- t' : T.
Proof.
  introv Ht Hr.
  assert (empty |- empty[t]: T) as He by (repeat constructor*).
  destruct* (preservation_ec He Hr).
Qed.
