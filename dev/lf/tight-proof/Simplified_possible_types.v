Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inductive_opens.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Some_lemmas.
Require Import Narrowing.
Require Import Has_member.
Require Import Tight_bound_completeness.
Require Import Misc_inversions.
Require Import Precise_flow.
Require Import Good_types.

(* ###################################################################### *)
(** ** Simplified Possible types *)

(*
Definition (Simplified Possible types)

For a variable x, environment G, the set SPT(G, x) of simplified possible types
of x defined as v in G is the smallest set SS such that:

If G |-! x:T then T in SS.
If {a:T} in SS and G |- T<:T' then {a:T'} in SS.
If {A:T..U} in SS, G |- T'<:T and G |- U<:U' then {A:T'..U'} in SS.
If all(x: S)T in SS, G |- S'<:S and G, x: S' |- T<:T' then all(x: S')T' in SS.
If S1 in SS and S2 in SS then (S1 & S2) in SS.
If S in SS and G |-! y: {A: S..S} then y.A in SS.
If S in SS then rec(x: S) in SS.
*)

Inductive s_possible_types: ctx -> var -> typ -> Prop :=
  (* Top *)
| s_pt_top : forall G x T,
  s_possible_types G x T ->
  s_possible_types G x typ_top   (* 8. Top in SPT *)
  (* Forall *)
| s_pt_all : forall L G x S T S' T',
  s_possible_types G x (typ_all S T) ->
  subtyp ty_general sub_general G S' S ->
  (forall y, y \notin L ->
   subtyp ty_general sub_general (G & y ~ S') (open_typ y T) (open_typ y T')) ->
  s_possible_types G x (typ_all S' T')
  (* And *)
| s_pt_and : forall G x S1 S2,
  s_possible_types G x S1 ->
  s_possible_types G x S2 ->
  s_possible_types G x (typ_and S1 S2) (* 5. S1, S2 in SPT -> S1 ^ S2 in SPT *)
  (* Tight Selection *)
| s_pt_sel : forall G x y A S,
  s_possible_types G x S ->
  ty_trm ty_precise sub_general G (trm_var y) (typ_rcd (dec_typ A S S)) ->
  s_possible_types G x (typ_sel y A) (* 6. S in SPT, G |-! y : {A : S .. S} -> y.A in SPT *)
  (* Recursive Types *)
| s_pt_bnd : forall G x S S',
  s_possible_types G x S ->
  S = open_typ x S' ->
  s_possible_types G x (typ_bnd S') (* 7. T is S -> rec(x:T) in SPT *)
  (* Precise typing *)
| s_pt_precise : forall G x T,
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) T ->
  s_possible_types G x T
  (* Term member subtyping *)
| s_pt_dec_trm : forall G x a T T',
  s_possible_types G x (typ_rcd (dec_trm a T)) ->
  subtyp ty_general sub_general G T T' ->
  s_possible_types G x (typ_rcd (dec_trm a T'))
  (* Type member subtyping *)
| s_pt_dec_typ : forall G x A T T' U' U,
  s_possible_types G x (typ_rcd (dec_typ A T U)) ->
  subtyp ty_general sub_general G T' T ->
  subtyp ty_general sub_general G U U' ->
  s_possible_types G x (typ_rcd (dec_typ A T' U'))
.

Definition binds_spt (G : ctx) (x : var) (T T' : typ) :=
    binds x T G /\ s_possible_types G x T'.

Hint Constructors s_possible_types.

Lemma spt_implies_bound :
  forall G x T,
    s_possible_types G x T ->
    exists S, binds x S G.
Proof.
  intros G x T H.
  induction H; try assumption.
  dependent induction H; try assumption.
  exists T. assumption.
Qed.

Lemma open_typ_bnd:
  forall x T0 T,
    open_typ x T0 = typ_bnd T ->
    exists T', T0 = typ_bnd T'.
Proof.
  intros. unfold open_typ in H.
  unfold open_rec_typ in H.
  induction T0; try solve [inversion H].
  exists T0. reflexivity.
Qed.

Lemma spt_empty_inv:
  forall x T,
    s_possible_types empty x T ->
    False.
Proof.
  intros x T H.
  apply spt_implies_bound in H.
  destruct H as [S H].
  false * binds_empty_inv.
Qed.

Lemma s_possible_types_closure_tight: forall G x T0 U0,
  good G ->
  s_possible_types G x T0 ->
  subtyp ty_general sub_tight G T0 U0 ->
  s_possible_types G x U0.
Proof.
  intros G x T0 U0 Hgd HT0 Hsub.
  dependent induction Hsub.
  - (* Top *) apply s_pt_top with T. assumption.
  - (* Bot *) dependent induction HT0.
    false. apply (good_ty_precise_bot Hgd H).
  - (* Refl *) assumption.
  - (* Trans *)
    apply IHHsub2; try assumption.
    apply IHHsub1; try assumption.
  - (* And left inv *) dependent induction HT0; auto.
    apply ty_precise_var_and_inv1 in H.
    auto.
  - (* And right inv *) dependent induction HT0; auto.
    apply ty_precise_var_and_inv2 in H.
    auto.
  - (* And *) specialize (IHHsub1 Hgd HT0).
    specialize (IHHsub2 Hgd HT0).
    auto.
  - (* Fld-<:-Fld *)
    eapply s_pt_dec_trm.
    + apply HT0.
    + apply tight_to_general_subtyping.
      assumption.
  - (* Typ-<:-Typ *) eapply s_pt_dec_typ.
    + apply HT0.
    + apply tight_to_general_subtyping. auto.
    + apply tight_to_general_subtyping. auto.
  - (* <:-Sel-tight *) eapply s_pt_sel; eauto.
  - (* Sel-<:-tight *) dependent induction HT0.
    + rewrite <- (good_unique_tight_bounds Hgd H H0).
      auto.
    + pose proof (typing_implies_bound H) as [T' Bis].
      pose proof (binds_good Bis Hgd) as Hgtyp.
      induction Hgtyp.
      * pose proof (precise_flow_lemma Bis H) as H1.
        pose proof (precise_flow_all_inv H1) as H2.
        inversion H2.
      * pose proof (precise_flow_lemma Bis H) as H2.
        pose proof (precise_flow_bnd_inv'' H1 H2) as [[U [H3 H4]] | [ls H3]]; inversion H3.
  - (* Forall *) apply tight_to_general_subtyping in Hsub.
    apply (s_pt_all _ HT0 Hsub H).
Qed.

Lemma s_possible_types_completeness_tight: forall G x T,
  good G ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) T ->
  s_possible_types G x T.
Proof.
  introv Hgd Htyp.
  dependent induction Htyp; auto; specialize (IHHtyp Hgd).
  - eapply s_pt_bnd; eauto.
  - dependent induction IHHtyp.
    + auto.
    + pose proof (precise_flow_lemma'' H) as [ T' [H1 H2]].
      apply pf_open in H2.
      apply precise_flow_lemma_rev in H2.
      auto.
  - eapply s_possible_types_closure_tight; eauto.
Qed.

Lemma s_possible_types_all_inv' : forall G x S T,
    good G ->
    s_possible_types G x (typ_all S T) ->
    (binds x (typ_all S T) G) \/
    (exists L S' T',
        subtyp ty_general sub_general G S S' ->
        (forall y, y \notin L ->
              subtyp ty_general sub_general (G & y ~ S') (open_typ y T') (open_typ y T)) ->
        s_possible_types G x (typ_all S' T')).
Proof.
  introv Hgd Hspt.
  dependent induction Hspt.
  - right.
    exists L S T.
    apply s_pt_all.
    eapply s_pt_all; eauto.
  - pose proof (typing_implies_bound H) as [T1 H1].
    pose proof (good_binds Hgd H1) as H2.
    pose proof (precise_flow_lemma H1 H) as H3.
    induction H2.
    + apply precise_flow_all_inv in H3.
      left. rewrite <- H3 in H1. auto.
    + pose proof (precise_flow_bnd_inv'' H0 H3) as [[U [H4 H5]] | [ls H4]].
      * false.
      * inversion H4.
Qed.

Lemma s_possible_types_all_inv : forall G x S T,
    good G ->
    s_possible_types G x (typ_all S T) ->
    (exists S' T', (binds x (typ_all S' T') G)).
Proof.
  introv Hgd Hspt.
  dependent induction Hspt.
  - auto.
  - pose proof (typing_implies_bound H) as [T1 H1].
    pose proof (good_binds Hgd H1) as H2.
    pose proof (precise_flow_lemma H1 H) as H3.
    induction H2.
    + apply precise_flow_all_inv in H3.
      rewrite <- H3 in H1. exists S T. auto.
    + pose proof (precise_flow_bnd_inv'' H0 H3) as [[U [H4 H5]] | [ls H4]].
      * false.
      * inversion H4.
Qed.

Lemma s_possible_types_bind_all_inv: forall G x S T,
    (forall T0,
        binds_spt G x (typ_all S T) T0 ->
        T0 = typ_top \/
        (exists S' T', T0 = typ_and S' T') \/
        (exists S' T', T0 = typ_all S' T') \/
        (exists y A, T0 = typ_sel y A) \/
        (exists T', T0 = typ_bnd T')
    ).
Proof.
  introv [Bis Hspt].
  dependent induction Hspt.
  - auto.
  - right. right. left. exists S' T'. reflexivity.
  - right. left. exists S1 S2. reflexivity.
  - right. right. right. left.
    exists y A. reflexivity.
  - right. right. right. right.
    exists S'. reflexivity.
  - pose proof (precise_flow_lemma Bis H) as Hpf.
    apply precise_flow_all_inv in Hpf.
    rewrite Hpf.
    right. right. left. exists S T. reflexivity.
  - specialize (IHHspt Bis).
    destruct IHHspt as [ Contra
                       | [ [S'' [T'' Contra]]
                         | [ [S'' [T'' Contra]]
                           | [ [y [A Contra]]
                             | [T'' Contra]]]]]; inversion Contra.
  - specialize (IHHspt Bis).
    destruct IHHspt as [ Contra
                       | [ [S'' [T'' Contra]]
                         | [ [S'' [T'' Contra]]
                           | [ [y [A' Contra]]
                             | [T'' Contra]]]]]; inversion Contra.
Qed.

Lemma s_possible_types_bind_all_rcd_inv: forall G x S T D,
    binds_spt G x (typ_all S T) (typ_rcd D) ->
    False.
Proof.
  introv Hbspt.
  pose proof (s_possible_types_bind_all_inv Hbspt) as H1.
  destruct H1 as [ Contra
                 | [ [S'' [T'' Contra]]
                   | [ [S'' [T'' Contra]]
                     | [ [y [A' Contra]]
                       | [T'' Contra]]]]]; inversion Contra.
Qed.

Lemma good_tight_ty_rcd_bnd : forall G x T' A S U,
    good G ->
    binds x T' G ->
    ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_rcd (dec_typ A S U)) ->
    exists T, T' = typ_bnd T.
Proof.
  introv Hgd Bis Hty.
  pose proof (good_binds Hgd Bis) as Hgt.
  pose proof (s_possible_types_completeness_tight Hgd Hty) as Hpt.
  dependent induction Hgt.
  - exfalso.
    apply (s_possible_types_bind_all_rcd_inv (conj Bis Hpt)).
  - exists T. reflexivity.
Qed.

Lemma good_general_to_tight: forall G0,
    good G0 ->
    (forall m1 m2 G t T,
        ty_trm m1 m2 G t T ->
        G = G0 ->
        m1 = ty_general ->
        m2 = sub_general ->
        ty_trm ty_general sub_tight G t T) /\
    (forall m1 m2 G S U,
        subtyp m1 m2 G S U ->
        G = G0 ->
        m1 = ty_general ->
        m2 = sub_general ->
        subtyp ty_general sub_tight G S U).
Proof.
  intros G0 Hgd.
  apply ts_mutind; intros; subst; eauto.
  - specialize (H (eq_refl _) (eq_refl _) (eq_refl _)).
    pose proof (typing_implies_bound t) as [T' H3].
    pose proof (good_tight_ty_rcd_bnd Hgd H3 H) as [T'' H4].
    rewrite H4 in H3.
    apply (good_tight_bound_completeness Hgd H3 H).
  - specialize (H (eq_refl _) (eq_refl _) (eq_refl _)).
    pose proof (typing_implies_bound t) as [T' H3].
    pose proof (good_tight_ty_rcd_bnd Hgd H3 H) as [T'' H4].
    rewrite H4 in H3.
    apply (good_tight_bound_completeness Hgd H3 H).
Qed.

Lemma good_general_to_tight_subtyping: forall G S U,
  good G ->
  subtyp ty_general sub_general G S U ->
  subtyp ty_general sub_tight G S U.
Proof.
  intros. apply* good_general_to_tight.
Qed.

Lemma good_general_to_tight_typing: forall G t T,
  good G ->
  ty_trm ty_general sub_general G t T ->
  ty_trm ty_general sub_tight G t T.
Proof.
  intros. apply* good_general_to_tight.
Qed.

Lemma s_possible_types_lemma :
  forall G U x,
    good G -> (* G good *)
    ty_trm ty_general sub_general G (trm_var (avar_f x)) U -> (* G |- x : U *)
    s_possible_types G x U (* U \in SPT(G,x) *).
Proof.
  introv Hgc Hty.
  dependent induction Hty.
  - (* Hty : G(x)=T *)
    auto.
  - (* Hty : G |- x : T^x *)
    pose proof (IHHty Hgc) as H.
    apply (s_pt_bnd T H).
    reflexivity.
  - (* Hty : G |- x : rec(y:T) *)
    pose proof (IHHty Hgc) as H1.
    inversions H1.
    + auto.
    + auto.
  - (* Hty : G |- x : T, G |- x : U *)
    specialize (IHHty1 Hgc).
    specialize (IHHty2 Hgc).
    auto.
  - (* Hty : G |- x : T, G |- T <: U *)
    specialize (IHHty Hgc).
    apply (good_general_to_tight_subtyping Hgc) in H0.
    apply (s_possible_types_closure_tight Hgc IHHty H0).
Qed.
