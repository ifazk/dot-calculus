Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Dot_definitions.
Require Import Dot_proofs_some_lemmas.

(* ###################################################################### *)
(** * Misc Inversions *)

Lemma all_intro_inversion: forall G S t U,
  ty_trm ty_precise sub_general G (trm_val (val_lambda S t)) U ->
  exists T, U = typ_all S T.
Proof.
  intros. dependent induction H.
  - eexists. reflexivity.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
Qed.

Lemma new_intro_inversion: forall G T ds U,
  ty_trm ty_precise sub_general G (trm_val (val_new T ds)) U ->
  U = typ_bnd T /\ record_type T.
Proof.
  intros. inversion H; subst.
  - apply record_new_typing in H. split; eauto.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H0 Heqm1). destruct H0. inversion H0.
Qed.

Inductive good_typ : typ -> Prop :=
  | good_typ_all : forall S T, good_typ (typ_all S T)
  | good_typ_rcd : forall d, good_dec d -> good_typ (typ_rcd d)
  | good_typ_and : forall T U, good_typ T -> good_typ U -> good_typ (typ_and T U)
  | good_typ_bnd : forall T, good_typ (typ_bnd T)
with good_dec : dec -> Prop :=
  | good_dec_typ : forall A T, good_dec (dec_typ A T T)
  | good_dec_trm : forall a T, good_dec (dec_trm a T).

Inductive good : ctx -> Prop :=
  | good_empty : good empty
  | good_all : forall pre x T,
          good pre ->
          good_typ T ->
          good (pre & x ~ T).

Lemma binds_good: forall G x T,
    binds x T G ->
    good G ->
    good_typ T.
Proof.
    introv Bi Good. induction Good.
    - false* binds_empty_inv.
    - destruct (binds_push_inv Bi).
      + destruct H0. subst. assumption.
      + destruct H0. apply (IHGood H1).
Qed.

Lemma wf_good : forall G s, wf_sto G s -> good G.
Proof.
  intros. induction H.
  - apply good_empty.
  - apply good_all.
    + assumption.
    + dependent induction H2.
      * apply good_typ_all.
      * apply good_typ_bnd.
      * assert (ty_precise = ty_precise) by reflexivity. apply H4 in H5.
        destruct H5. inversion H5.
Qed.

