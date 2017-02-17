Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Dot_definitions.
Require Import Dot_proofs_weakening.
Require Import Dot_proofs_wellformed_store.
Require Import Dot_proofs_substitution.
Require Import Dot_proofs_some_lemmas.
Require Import Dot_proofs_narrowing.
Require Import Dot_proofs_has_member.
Require Import Dot_proofs_tight_bound_completeness.
Require Import Dot_proofs_misc_inversions.

(* ###################################################################### *)
(** ** Possible types *)

(* Good types *)

(* Definition (Good types)

A declaration is a good declaration if it is of the form
   A: T..T
   a: T

A type is good if it of the form
  { D }
  rec(x: T)
  all(x: S)T
  T ^ U, where T and U are good types *)

Inductive good_dec : dec -> Prop :=
     | good_dec_typ : forall A T, good_dec (dec_typ A T T)
     | good_dec_trm : forall a T, good_dec (dec_trm a T).

Inductive good_typ : typ -> Prop :=
  | good_typ_all : forall S T, good_typ (typ_all S T) (* all(x: S)T *)
  | good_typ_rcd : forall d, good_dec d -> good_typ (typ_rcd d) (* { D } *)
  | good_typ_and : forall T U, good_typ T -> good_typ U -> good_typ (typ_and T U) (* T ^ U *)
  (*| good_typ_bnd : forall T, good_typ (typ_bnd T).*) (* rec(x:T) *)
  | good_typ_bnd : forall T,
      record_type T ->
      good_typ (typ_bnd T). (* rec(x:T) *)

(* Definition (Good context)

A context is good if it is of the form
  {}
  G, x : T where G is a good context and T is a good type *)

Inductive good : ctx -> Prop :=
  | good_empty : good empty
  | good_all : forall pre x T,
      good pre ->
      good_typ T ->
      good (pre & x ~ T).

(* Good contexts bind good:
If G |- x : T and G is a good context then T is a good type. *)

Lemma binds_good : forall G x T,
    binds x T G ->
    good G ->
    good_typ T.
Proof.
  introv Bi Hgood. induction Hgood.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi).
    + destruct H0. subst. assumption.
    + destruct H0. apply (IHHgood H1).
Qed.

Lemma binds_good_dec : forall G x d,
    binds x (typ_rcd d) G ->
    good G ->
    good_dec d.
Proof.
  introv Bi Hgood.
  dependent induction Hgood.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi) as [[H1 H2] | [H1 H2]].
    + subst. inversion H; assumption.
    + apply IHHgood. assumption.
Qed.

Lemma binds_good_dec1 : forall G x T d,
    binds x (typ_and (typ_rcd d) T) G ->
    good G ->
    good_dec d.
Proof.
  introv Bi Hgood.
  dependent induction Hgood.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi) as [[H1 H2] | [H1 H2]].
    + subst. inversion H; subst. inversion H2; assumption.
    + apply IHHgood. assumption.
Qed.

Lemma binds_good_dec2 : forall G x T d,
    binds x (typ_and T (typ_rcd d)) G ->
    good G ->
    good_dec d.
Proof.
  introv Bi Hgood.
  dependent induction Hgood.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi) as [[H1 H2] | [H1 H2]].
    + subst. inversion H; subst. inversion H3; assumption.
    + apply IHHgood. assumption.
Qed.

Inductive s_possible_types: ctx -> var -> typ -> Prop :=
| s_pt_top : forall G x,
  s_possible_types G x typ_top   (* 8. Top in SPT *)
| s_pt_and : forall G x S1 S2,
  s_possible_types G x S1 ->
  s_possible_types G x S2 ->
  s_possible_types G x (typ_and S1 S2) (* 5. S1, S2 in SPT -> S1 ^ S2 in SPT *)
| s_pt_sel : forall G x y A S,
  s_possible_types G x S ->
  ty_trm ty_precise sub_general G (trm_var y) (typ_rcd (dec_typ A S S)) ->
  s_possible_types G x (typ_sel y A) (* 6. S in SPT, G |-! y : {A : S .. S} -> y.A in SPT *)
| s_pt_bnd : forall G x S S',
  s_possible_types G x S ->
  S = open_typ x S' ->
  s_possible_types G x (typ_bnd S') (* 7. T is S -> rec(x:T) in SPT *)
| s_pt_open : forall G x T,
  (* binds x (typ_bnd T) G -> *)
  s_possible_types G x (typ_bnd T) ->
  s_possible_types G x (open_typ x T) (* ---- 1. G(x)=rec(T) -> T^x in SPT *)
| s_pt_and_inv1 : forall G x T U,
  s_possible_types G x (typ_and T U) ->
  s_possible_types G x T (* 2a. T ^ U in SPT -> T in SPT *)
| s_pt_and_inv2 : forall G x T U,
  s_possible_types G x (typ_and T U) ->
  s_possible_types G x U (* 2b. T ^ U in SPT -> T in SPT *)
| s_pt_dec_typ : forall G x A T T' U' U,
  s_possible_types G x (typ_rcd (dec_typ A T U)) ->
  subtyp ty_general sub_general G T' T ->
  subtyp ty_general sub_general G U U' ->
  s_possible_types G x (typ_rcd (dec_typ A T' U'))
| s_pt_all : forall L G x S T S' T',
  s_possible_types G x (typ_all S T) ->
  subtyp ty_general sub_general G S' S ->
  (forall y, y \notin L ->
   subtyp ty_general sub_general (G & y ~ S') (open_typ y T) (open_typ y T')) ->
  s_possible_types G x (typ_all S' T')
| s_pt_binds : forall G x T,
  binds x T G ->
  s_possible_types G x T (* 1. G(x)=T -> T in SPT *)
.

Lemma s_possible_types_bot_rec:
  forall T x G,
    good G ->
    s_possible_types G x (typ_bnd T) ->
    record_type T.
Proof.
  intros T x G Hgd Hspt.



Lemma s_possible_types_bot_rec: forall G x,
    good G ->
    s_possible_types G x (typ_bnd typ_bot) ->
    False.
Proof.
  intros G x Hgd Hspt.
  dependent induction Hspt.
  -
    +
    + subst.
      assert (H3: T = typ_bot).
      { destruct T; inversion H. reflexivity. }
      inversion Hs

      destruct T. assumption.
      unfold open_typ in H.


Lemma s_possible_types_bot: forall G x,
    good G ->
    s_possible_types G x typ_bot ->
    False.
Proof.
  intros G x Hgd Hspt.
  dependent induction Hspt.
  - unfold open_typ in x.
    destruct T; inversion x.
    simpl in x.
    apply IHHspt. assumption.

    invert x.


Lemma s_possible_types_closure_tight: forall G x S T,
  good G ->
  s_possible_types G x S ->
  subtyp ty_general sub_tight G S T ->
  s_possible_types G x T.
Proof.
  introv Hgd HS Hsub. dependent induction Hsub.
  - (* Top *) constructor.
  - (* Bot *) inversion HS; subst.
    * admit.
    *
Qed.

Lemma s_possible_types_closure: forall G s x v S T,
  good G ->
  s_possible_types G x v S ->
  subtyp ty_general sub_general G S T ->
  s_possible_types G x v T.
Proof.
  intros. eapply possible_types_closure_tight; eauto.
  eapply general_to_tight_subtyping; eauto.
Qed.

Lemma s_possible_types_lemma :
  forall G U x,
    good G -> (* G good *)
    ty_trm ty_general sub_general G (trm_var (avar_f x)) U -> (* G |- x : U *)
    s_possible_types G x U (* U \in SPT(G,x,T) *).
Proof.
  introv Hgt Hty.
  dependent induction Hty.
  - (* Hty : G(x)=T0 *)
    constructor; auto.
  - (* Hty : G |- x : T0^x *)
    apply s_pt_bnd with (open_typ x T); auto.
  - (* Hty : G |- x : rec(y:T0) *)
    apply s_pt_open. auto.
  - (* Hty : G |- x : T, G |- x : U *)
    apply s_pt_and; auto.
  - (* Hty : G |- x : T, H0 : G |- T <: U *)
    pose proof (IHHty Hgt) as H1.
    pose proof (ty_sub H Hty H0) as H2.
    dependent induction H1.
    + inversion H0; subst.
      * constructor.
      * constructor.
      *


      (*
| s_pt_open : forall G x T,
  good G -> binds x (typ_bnd T) G ->
  s_possible_types G x (open_typ x T) (* 1. G(x)=rec(y:T) -> T^x in SPT *)
                   *)
Lemma s_possible_types_lemma :
  forall G T U x,
    good G -> (* G good *)
    binds x T G -> (* G(x) = T *)
    ty_trm ty_general sub_general G (trm_var (avar_f x)) U -> (* G |- x : U *)
    s_possible_types G x U (* U \in SPT(G,x,T) *).
Proof.
  introv Hgc Bis Hty.
  dependent induction Hty.
  - (* Hty : G(x)=T0 *)
    rewrite (binds_func H Bis).
    constructor.
    constructor; auto.
  - (* Hty : G |- x : T0^x *)
    apply s_pt_bnd with (open_typ x T0).
    apply (IHHty Hgc Bis).
    reflexivity.
  - (* Hty : G |- x : rec(y:T0) *)
    pose proof (IHHty Hgc Bis) as H1.
    inversion H1; subst.
    + assumption.
    +
      admit.
    +
    + assert (H1 : subtyp ty_general sub_general G T1 (open_typ
    +
    + subst.
      inversion H0.
      apply s_pt_subtyp with .
    admit.
  - constructor; auto.
  -
Lemma binds_good : forall G x T,
    binds x T G ->
    good G ->
    good_typ T.
  lets A: (possible_types_completeness Hwf Hty).
  destruct A as [v' [Bis' Hp]].
  unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis. inversions Bis.
  assumption.
Qed.
