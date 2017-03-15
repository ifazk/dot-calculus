Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Dot_definitions.

(* ###################################################################### *)
(** ** Inductive opening *)

(* Inductive definitions of opening together with rewrite rules *)

Inductive open_ind_avar : (nat * var * avar) -> avar -> Prop :=
| open_avar_b_eq : forall k u,
    open_ind_avar (k, u, avar_b k) (avar_f u)
| open_avar_b_neq : forall k i u,
    k <> i ->
    open_ind_avar (k, u, avar_b i) (avar_b i)
| open_avar_f : forall k u x,
    open_ind_avar (k, u, avar_f x) (avar_f x)
.

Theorem open_avar_rewrite : forall k u a res,
    res = open_rec_avar k u a <->
    open_ind_avar (k, u, a) res.
Proof.
  intros k u. induction a.
  - intros res.
    simpl. cases_if; split; intros Hres.
    + subst. constructor.
    + inversion Hres.
      * reflexivity.
      * false.
    + rewrite Hres. constructor. assumption.
    + inversion Hres.
      * false.
      * reflexivity.
  - intros res. split; intros Hres.
    + simpl in Hres. subst. constructor.
    + inversion Hres. reflexivity.
Qed.

Theorem open_avar_rewrite' : forall k u a res,
    open_rec_avar k u a = res <->
    open_ind_avar (k, u, a) res.
Proof.
  intros. split; intros H.
  - symmetry in H. apply open_avar_rewrite. apply H.
  - symmetry. apply open_avar_rewrite. apply H.
Qed.

Inductive open_ind_typ : (nat * var * typ) -> typ -> Prop :=
| open_typ_top : forall k u, open_ind_typ (k, u, typ_top) typ_top
| open_typ_bot : forall k u, open_ind_typ (k, u, typ_bot) typ_bot
| open_typ_rcd : forall k u D D',
    open_ind_dec (k, u, D) D' ->
    open_ind_typ (k, u, typ_rcd D) (typ_rcd D')
| open_typ_and : forall k u T1 T2 T1' T2',
    open_ind_typ (k, u, T1) T1' ->
    open_ind_typ (k, u, T2) T2' ->
    open_ind_typ (k, u, (typ_and T1 T2)) (typ_and T1' T2')
| open_typ_sel : forall k u x x' L,
    open_ind_avar (k, u, x) x' ->
    open_ind_typ (k, u, (typ_sel x L)) (typ_sel x' L)
| open_typ_bnd : forall k u T T',
    open_ind_typ (S k, u, T) T' ->
    open_ind_typ (k, u, (typ_bnd T)) (typ_bnd T')
| open_typ_all : forall k u T1 T2 T1' T2',
    open_ind_typ (k, u, T1) T1' ->
    open_ind_typ (S k, u, T2) T2' ->
    open_ind_typ (k, u, (typ_all T1 T2)) (typ_all T1' T2')
with
open_ind_dec : (nat * var * dec) -> dec -> Prop :=
| open_dec_type : forall k u L T T' U U',
    open_ind_typ (k, u, T) T' ->
    open_ind_typ (k, u, U) U' ->
    open_ind_dec (k, u, dec_typ L T U) (dec_typ L T' U')
| open_dec_trm : forall k u m T T',
    open_ind_typ (k, u, T) T' ->
    open_ind_dec (k, u, dec_trm m T) (dec_trm m T')
.

Scheme open_typ_mut := Induction for open_ind_typ Sort Prop
with   open_dec_mut := Induction for open_ind_dec Sort Prop.
Combined Scheme open_typ_dec_mut from open_typ_mut, open_dec_mut.

Theorem open_rec_typ_dec_ind_typ_dec :
    (forall T T_res k u, T_res = open_rec_typ k u T ->
     open_ind_typ (k, u, T) T_res) /\
    (forall D D_res k u, D_res = open_rec_dec k u D ->
     open_ind_dec (k, u, D) D_res).
Proof.
  apply typ_mutind.
  - intros T_res k u Hres. simpl in Hres; subst; constructor.
  - intros T_res k u Hres. simpl in Hres; subst; constructor.
  - intros D HDres T_res k u Hres. simpl in Hres; subst; constructor.
    apply HDres. reflexivity.
  - intros T HT U HU Tres k u Hres.
    simpl in Hres; subst; constructor; auto.
  - intros a T Tres k u Hres.
    simpl in Hres; subst; constructor.
    apply open_avar_rewrite.
    reflexivity.
  - intros T HT T_res k u Hres.
    simpl in Hres; subst; constructor.
    apply HT. reflexivity.
  - intros T HT T' HT' Tres k u Hres.
    simpl in Hres; subst; constructor; auto.
  - intros L T HT T' HT' Tres k u Hres.
    simpl in Hres; subst; constructor; auto.
  - intros L T HT D_res k u Hres.
    simpl in Hres; subst; constructor; auto.
Qed.

Theorem open_rec_typ_ind_typ :
  forall T T_res k u,
    T_res = open_rec_typ k u T ->
    open_ind_typ (k, u, T) T_res.
Proof.
  apply open_rec_typ_dec_ind_typ_dec.
Qed.

Theorem open_rec_dec_ind_dec :
  forall D D_res k u,
    D_res = open_rec_dec k u D ->
    open_ind_dec (k, u, D) D_res.
Proof.
  apply open_rec_typ_dec_ind_typ_dec.
Qed.

Theorem open_ind_typ_dec_rec_typ_dec :
    (forall p T_res,
        open_ind_typ p T_res ->
        (forall k u T,
        p = (k, u, T) ->
        T_res = open_rec_typ k u T)) /\
    (forall p D_res,
        open_ind_dec p D_res ->
        (forall k u D,
        p = (k, u, D) ->
        D_res = open_rec_dec k u D)).
Proof.
  apply open_typ_dec_mut.
  - intros k u k' u' T Hp.
    inversion Hp; reflexivity.
  - intros k u k' u' T Hp.
    inversion Hp; reflexivity.
  - intros k u D D' Ho IH k' u' T Hp.
    inversion Hp.
    simpl. apply f_equal.
    apply IH; auto.
  - intros k u T1 T2 T1' T2' HT1 IHT1 HT2 IHT2 k' u' T Hp.
    inversion Hp.
    simpl. f_equal; auto.
  - intros k u x x' L Hx k' u' T Hp.
    inversion Hp; simpl; f_equal.
    apply open_avar_rewrite; subst; auto.
  - intros k u T1 T1' HT1 IHT1 k' u' T Hp.
    inversion Hp; subst; simpl; f_equal; auto.
  - intros k u T1 T2 T1' T2' HT1 IHT1 HT2 IHT2 k' u' T Hp.
    inversion Hp; subst; simpl; f_equal; auto.
  - intros k u L T T' U U' HT IHT HU IHU k' u' T0 Hp.
    inversion Hp; subst; simpl; f_equal; auto.
  - introv HT IHT. intros k' u' D Hp.
    inversion Hp; subst; simpl; f_equal; auto.
Qed.

Theorem open_ind_typ_rec_typ' :
  forall p T_res,
    open_ind_typ p T_res ->
    (forall k u T,
        p = (k, u, T) ->
        T_res = open_rec_typ k u T).
Proof.
  apply open_ind_typ_dec_rec_typ_dec.
Qed.

Theorem open_ind_dec_rec_dec' :
  forall p D_res,
    open_ind_dec p D_res ->
    (forall k u D,
        p = (k, u, D) ->
        D_res = open_rec_dec k u D).
Proof.
  apply open_ind_typ_dec_rec_typ_dec.
Qed.

Theorem open_ind_typ_rec_typ :
  forall T T_res k u,
    open_ind_typ (k, u, T) T_res ->
    T_res = open_rec_typ k u T.
Proof.
  intros T T_res k u H.
  assert (H1: exists p, p = (k, u, T)).
  { exists (k, u, T). reflexivity. }
  destruct H1 as [p H1].
  apply (open_ind_typ_rec_typ' H).
  reflexivity.
Qed.

Theorem open_ind_dec_rec_dec :
  forall D D_res k u,
    open_ind_dec (k, u, D) D_res ->
    D_res = open_rec_dec k u D.
Proof.
  intros D D_res k u H.
  assert (H1: exists p, p = (k, u, D)).
  { exists (k, u, D). reflexivity. }
  destruct H1 as [p H1].
  apply (open_ind_dec_rec_dec' H).
  reflexivity.
Qed.

Theorem open_typ_rewrite :
    forall T T_res k u,
      T_res = open_rec_typ k u T <->
      open_ind_typ (k, u, T) T_res.
Proof.
  intros; split.
  - apply open_rec_typ_ind_typ.
  - apply open_ind_typ_rec_typ.
Qed.

Theorem open_typ_rewrite' :
    forall T T_res k u,
      open_rec_typ k u T = T_res <->
      open_ind_typ (k, u, T) T_res.
Proof.
  intros; split.
  - intros H. symmetry in H. apply open_rec_typ_ind_typ; assumption.
  - intros H. symmetry. apply open_ind_typ_rec_typ; assumption.
Qed.

Theorem open_dec_rewrite :
    forall D D_res k u,
      D_res = open_rec_dec k u D <->
      open_ind_dec (k, u, D) D_res.
Proof.
  intros; split.
  - apply open_rec_dec_ind_dec.
  - apply open_ind_dec_rec_dec.
Qed.

Theorem open_dec_rewrite' :
    forall D D_res k u,
      open_rec_dec k u D = D_res <->
      open_ind_dec (k, u, D) D_res.
Proof.
  intros; split.
  - intros H. symmetry in H. apply open_rec_dec_ind_dec; assumption.
  - intros H. symmetry. apply open_ind_dec_rec_dec; assumption.
Qed.
