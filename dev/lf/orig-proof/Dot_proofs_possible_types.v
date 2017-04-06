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

(*
Definition (Possible types)

For a variable x, non-variable value v, environment G, the set Ts(G, x, v) of possible types of x defined as v in G is the smallest set SS such that:

If v = new(x: T)d then T in SS.
If v = new(x: T)d and {a = t} in d and G |- t: T' then {a: T'} in SS.
If v = new(x: T)d and {A = T'} in d and G |- S <: T', G |- T' <: U then {A: S..U} in SS.
If v = lambda(x: S)t and G, x: S |- t: T and G |- S' <: S and G, x: S' |- T <: T' then all(x: S')T' in SS.
If S1 in SS and S2 in SS then S1 & S2 in SS.
If S in SS and G |-! y: {A: S..S} then y.A in SS.
If S in SS then rec(x: S) in SS.
*)

Inductive possible_types: ctx -> var -> val -> typ -> Prop :=
| pt_top : forall G x v,
  possible_types G x v typ_top
| pt_new : forall G x T ds,
  possible_types G x (val_new T ds) (open_typ x T)
| pt_rcd_trm : forall G x T ds a t T',
  defs_has (open_defs x ds) (def_trm a t) ->
  ty_trm ty_general sub_general G t T' ->
  possible_types G x (val_new T ds) (typ_rcd (dec_trm a T'))
| pt_rcd_typ : forall G x T ds A T' S U,
  defs_has (open_defs x ds) (def_typ A T') ->
  subtyp ty_general sub_general G S T' ->
  subtyp ty_general sub_general G T' U ->
  possible_types G x (val_new T ds) (typ_rcd (dec_typ A S U))
| pt_lambda : forall L G x S t T S' T',
  (forall y, y \notin L ->
   ty_trm ty_general sub_general (G & y ~ S) (open_trm y t) (open_typ y T)) ->
  subtyp ty_general sub_general G S' S ->
  (forall y, y \notin L ->
   subtyp ty_general sub_general (G & y ~ S') (open_typ y T) (open_typ y T')) ->
  possible_types G x (val_lambda S t) (typ_all S' T')
| pt_and : forall G x v S1 S2,
  possible_types G x v S1 ->
  possible_types G x v S2 ->
  possible_types G x v (typ_and S1 S2)
| pt_sel : forall G x v y A S,
  possible_types G x v S ->
  ty_trm ty_precise sub_general G (trm_var y) (typ_rcd (dec_typ A S S)) ->
  possible_types G x v (typ_sel y A)
| pt_bnd : forall G x v S S',
  possible_types G x v S ->
  S = open_typ x S' ->
  possible_types G x v (typ_bnd S')
.

Lemma var_new_typing: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (open_typ x T).
Proof.
  intros.
  apply ty_rec_elim. apply ty_var. eapply wf_sto_val_new_in_G; eauto.
Qed.

Lemma ty_defs_has: forall G ds T d,
  ty_defs G ds T ->
  defs_has ds d ->
  record_type T ->
  exists D, ty_def G d D /\ record_sub T (typ_rcd D).
Proof.
  introv Hdefs Hhas Htype. generalize dependent d. generalize dependent ds.
  inversion Htype; subst. induction H; intros.
  - exists D. split. inversion Hdefs; subst. inversion Hhas; subst.
    case_if. inversions H1. assumption. apply rs_refl.
  - inversion Hdefs; subst.
    unfold defs_has in Hhas. unfold get_def in Hhas.
    case_if.
    + inversions Hhas.
      exists D. split. inversions Hdefs; subst. assumption.
      eapply rs_dropl. eapply rs_refl.
    + assert (exists D0, ty_def G d D0 /\ record_sub T (typ_rcd D0)) as A. {
        eapply IHrecord_typ; eauto.
        exists ls. eassumption.
      }
      destruct A as [D0 [A1 A2]].
      exists D0. split. apply A1. apply rs_drop. apply A2.
Qed.

Lemma new_ty_defs: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  ty_defs G (open_defs x ds) (open_typ x T).
Proof.
  introv Hwf Bis.
  lets Htyv: (val_new_typing Hwf Bis).
  inversion Htyv; subst.
  pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H3 y FrL).
  rewrite subst_intro_defs with (x:=y). rewrite subst_intro_typ with (x:=y).
  eapply subst_ty_defs. eapply H3.
  apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
  rewrite <- subst_intro_typ with (x:=y).
  eapply ty_rec_elim. apply ty_var. eapply wf_sto_val_new_in_G; eauto.
  eauto. eauto. eauto.
  assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
  specialize (H Heqm1). destruct H as [? Contra]. inversion Contra.
Qed.

Lemma pt_piece_rcd: forall G s x T ds d D,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  defs_has (open_defs x ds) d ->
  ty_def G d D ->
  possible_types G x (val_new T ds) (typ_rcd D).
Proof.
  introv Hwf Bis Hhas Hdef.
  inversion Hdef; subst; econstructor; eauto.
Qed.

Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
  record_has (typ_rcd D) D
| rh_andl : forall T D,
  record_has (typ_and T (typ_rcd D)) D
| rh_and : forall T D D',
  record_has T D' ->
  record_has (typ_and T D) D'.

Lemma defs_has_hasnt_neq: forall ds d1 d2,
  defs_has ds d1 ->
  defs_hasnt ds (label_of_def d2) ->
  label_of_def d1 <> label_of_def d2.
Proof.
  introv Hhas Hhasnt.
  unfold defs_has in Hhas.
  unfold defs_hasnt in Hhasnt.
  induction ds.
  - simpl in Hhas. inversion Hhas.
  - simpl in Hhasnt. simpl in Hhas. case_if; case_if.
    + inversions Hhas. assumption.
    + apply IHds; eauto.
Qed.

Lemma record_has_ty_defs: forall G T ds D,
  ty_defs G ds T ->
  record_has T D ->
  exists d, defs_has ds d /\ ty_def G d D.
Proof.
  introv Hdefs Hhas. induction Hdefs.
  - inversion Hhas; subst. exists d. split.
    unfold defs_has. simpl. rewrite If_l. reflexivity. reflexivity.
    assumption.
  - inversion Hhas; subst.
    + exists d. split.
      unfold defs_has. simpl. rewrite If_l. reflexivity. reflexivity.
      assumption.
    + specialize (IHHdefs H4). destruct IHHdefs as [d' [IH1 IH2]].
      exists d'. split.
      unfold defs_has. simpl. rewrite If_r. apply IH1.
      apply not_eq_sym. eapply defs_has_hasnt_neq; eauto.
      assumption.
Qed.

Lemma pt_rcd_has_piece: forall G s x T ds D,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  record_has (open_typ x T) D ->
  possible_types G x (val_new T ds) (typ_rcd D).
Proof.
  introv Hwf Bis Hhas.
  lets Hdefs: (new_ty_defs Hwf Bis).
  destruct (record_has_ty_defs Hdefs Hhas) as [d [A B]].
  eapply pt_piece_rcd; eauto.
Qed.

Lemma pt_rcd_trm_inversion: forall G s x v a T,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v (typ_rcd (dec_trm a T)) ->
  exists S ds t,
    v = val_new S ds /\
    defs_has (open_defs x ds) (def_trm a t) /\
    ty_trm ty_general sub_general G t T.
Proof.
  introv Hwf Bis Hp. inversion Hp; subst.
  - induction T0; simpl in H3; try solve [inversion H3].
    induction d; simpl in H3; try solve [inversion H3].
    unfold open_typ in H3. simpl in H3. inversions H3.
    lets Hty: (val_new_typing Hwf Bis). inversion Hty; subst.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H3 y FrL).
    unfold open_typ in H3. simpl in H3. inversion H3; subst.
    destruct ds; simpl in H; try solve [inversion H].
    destruct ds; simpl in H; try solve [inversion H].
    unfold open_defs in H. simpl in H. inversions H.
    destruct d0; simpl in H2; inversion H2; subst.
    inversion H2; subst.
    assert (ty_trm ty_general sub_general G (open_trm x t1) (open_typ x t0)) as A. {
      rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
      eapply subst_ty_trm. eapply H4.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto. eauto.
      simpl. rewrite <- subst_intro_typ with (x:=y).
      lets Htyv: (var_new_typing Hwf Bis). unfold open_typ in Htyv. simpl in Htyv.
      unfold open_typ. apply Htyv.
      eauto.
      apply notin_union_r1 in Fr. apply notin_union_r2 in Fr.
      unfold fv_defs in Fr. apply notin_union_r2 in Fr. apply Fr.
      eauto.
    }
    repeat eexists.
    unfold open_defs. simpl. unfold defs_has. simpl.
    rewrite If_l. reflexivity. reflexivity.
    eapply A.
    assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
  - repeat eexists. eassumption. assumption.
Qed.

Lemma pt_rcd_typ_inversion: forall G s x v A S U,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v (typ_rcd (dec_typ A S U)) ->
  exists T ds T',
    v = val_new T ds /\
    defs_has (open_defs x ds) (def_typ A T') /\
    subtyp ty_general sub_general G S T' /\
    subtyp ty_general sub_general G T' U.
Proof.
  introv Hwf Bis Hp. inversion Hp; subst.
  - induction T; simpl in H3; try solve [inversion H3].
    induction d; simpl in H3; try solve [inversion H3].
    unfold open_typ in H3. simpl in H3. inversions H3.
    lets Hty: (val_new_typing Hwf Bis). inversion Hty; subst.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H3 y FrL).
    unfold open_typ in H3. simpl in H3. inversion H3; subst.
    destruct ds; simpl in H; try solve [inversion H].
    destruct ds; simpl in H; try solve [inversion H].
    unfold open_defs in H. simpl in H. inversions H.
    destruct d0; simpl in H2; inversion H2; subst.
    inversion H2; subst.
    assert (t2 = t0). {
      eapply open_eq_typ; eauto.
      apply notin_union_r1 in Fr. apply notin_union_r1 in Fr.
      apply notin_union_r2 in Fr.
      unfold fv_defs in Fr. eauto.
    }
    assert (t2 = t1). {
      eapply open_eq_typ; eauto.
      apply notin_union_r1 in Fr. apply notin_union_r1 in Fr.
      apply notin_union_r2 in Fr.
      unfold fv_defs in Fr. eauto.
    }
    subst. subst. clear H5. clear H8.
    repeat eexists.
    unfold open_defs. simpl. unfold defs_has. simpl.
    rewrite If_l. reflexivity. reflexivity.
    eapply subtyp_refl. eapply subtyp_refl.
    assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
  - repeat eexists. eassumption. eassumption. eassumption.
Qed.

Lemma record_sub_and: forall T T1 T2,
  record_type T ->
  T = typ_and T1 T2 ->
  record_sub T T1 /\ record_sub T T2.
Proof.
  introv Htype Heq. subst.
  destruct Htype as [ls Htyp]. inversion Htyp; subst.
  split.
  - apply rs_drop. apply rs_refl.
  - eapply rs_dropl. apply rs_refl.
Qed.

Lemma record_sub_has: forall T1 T2 D,
  record_has T2 D ->
  record_sub T1 T2 ->
  record_has T1 D.
Proof.
  introv Hhas Hsub. induction Hsub.
  - assumption.
  - inversion Hhas; subst. apply rh_andl.
  - apply rh_and. apply IHHsub. apply Hhas.
  - inversion Hhas; subst.
    + apply rh_andl.
    + apply rh_and. apply IHHsub. assumption.
Qed.

Lemma pt_record_sub_has: forall G x v T1 T2,
  (forall D, record_has T1 D -> possible_types G x v (typ_rcd D)) ->
  record_sub T1 T2 ->
  (forall D, record_has T2 D -> possible_types G x v (typ_rcd D)).
Proof.
  introv HP Hsub. intros D Hhas. apply HP; eauto using record_sub_has.
Qed.

Lemma pt_has_record: forall G x v T,
  (forall D, record_has T D -> possible_types G x v (typ_rcd D)) ->
  record_type T ->
  possible_types G x v T.
Proof.
  introv HP Htype. destruct Htype as [ls Htyp]. induction Htyp.
  - apply HP; eauto. apply rh_one.
  - apply pt_and.
    + apply IHHtyp; eauto.
      intros D0 HH0. apply HP; eauto. apply rh_and; eauto.
    + apply HP; eauto. apply rh_andl.
Qed.

Lemma pt_has_sub: forall G x v T U,
  (forall D, record_has T D -> possible_types G x v (typ_rcd D)) ->
  record_type T ->
  record_sub T U ->
  possible_types G x v U.
Proof.
  introv HP Htype Hsub. induction Hsub.
  - apply pt_has_record; eauto.
  - apply HP; eauto. apply rh_andl.
  - apply IHHsub; eauto. eapply pt_record_sub_has; eauto.
    apply rs_drop. apply rs_refl.
    eapply record_type_sub_closed; eauto.
    apply rs_drop. apply rs_refl.
  - apply pt_and.
    + apply IHHsub; eauto. eapply pt_record_sub_has; eauto.
      apply rs_drop. apply rs_refl.
      eapply record_type_sub_closed; eauto.
      apply rs_drop. apply rs_refl.
    + apply HP; eauto. apply rh_andl.
Qed.

Lemma possible_types_closure_record: forall G s x T ds U,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  record_sub (open_typ x T) U ->
  possible_types G x (val_new T ds) U.
Proof.
  introv Hwf Bis Hsub.
  apply pt_has_sub with (T:=open_typ x T).
  intros D Hhas. eapply pt_rcd_has_piece; eauto.
  apply open_record_type. eapply record_new_typing; eauto. eapply val_new_typing; eauto.
  assumption.
Qed.

Lemma pt_and_inversion: forall G s x v T1 T2,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v (typ_and T1 T2) ->
  possible_types G x v T1 /\ possible_types G x v T2.
Proof.
  introv Hwf Bis Hp. dependent induction Hp.
  - assert (record_type (open_typ x0 T)) as Htype. {
      eapply open_record_type.
      eapply record_new_typing. eapply val_new_typing; eauto.
    }
    destruct (record_sub_and Htype x) as [Hsub1 Hsub2].
    split;
    eapply possible_types_closure_record; eauto.
  - split; assumption.
Qed.

(*
Lemma (Possible types closure)

If G ~ s and G |- x: T and s |- x = v then Ts(G, x, v) is closed wrt G |- _ <: _.

Let SS = Ts(G, x, v). We first show SS is closed wrt G |-# _ <: _.

Assume T0 in SS and G |- T0 <: U0.s We show U0 in SS by an induction on subtyping derivations of G |-# T0 <: U0.
*)

Lemma possible_types_closure_tight: forall G s x v T0 U0,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v T0 ->
  subtyp ty_general sub_tight G T0 U0 ->
  possible_types G x v U0.
Proof.
  introv Hwf Bis HT0 Hsub. dependent induction Hsub.
  - (* Top *) apply pt_top.
  - (* Bot *) inversion HT0; subst.
    lets Htype: (open_record_type x (record_new_typing (val_new_typing Hwf Bis))).
    destruct Htype as [ls Htyp]. rewrite H3 in Htyp. inversion Htyp.
  - (* Refl-<: *) assumption.
  - (* Trans-<: *)
    apply IHHsub2; try assumption; try reflexivity.
    apply IHHsub1; try assumption; try reflexivity.
  - (* And-<: *)
    apply pt_and_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [HT HU].
    assumption.
  - (* And-<: *)
    apply pt_and_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [HT HU].
    assumption.
  - (* <:-And *)
    apply pt_and. apply IHHsub1; try reflexivity; assumption. apply IHHsub2; try reflexivity; assumption.
  - (* Fld-<:-Fld *)
    apply pt_rcd_trm_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [S [ds [t [Heq [Hhas Hty]]]]].
    subst.
    eapply pt_rcd_trm.
    eassumption.
    apply ty_sub with (T:=T).
    intro Contra. inversion Contra.
    assumption.
    apply tight_to_general_subtyping. assumption.
  - (* Typ-<:-Typ *)
    apply pt_rcd_typ_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [T [ds [T' [Heq [Hhas [Hsub1' Hsub2']]]]]].
    subst.
    eapply pt_rcd_typ.
    eassumption.
    eapply subtyp_trans. eapply tight_to_general_subtyping. eassumption. eassumption.
    eapply subtyp_trans. eassumption. eapply tight_to_general_subtyping. eassumption.
  - (* <:-Sel-tight *)
    eapply pt_sel. eassumption. assumption.
  - (* Sel-<:-tight *)
    inversion HT0; subst.
    assert (record_type (open_typ x T0)) as B. {
      eapply record_type_new; eassumption.
    }
    rewrite H4 in B. destruct B as [? B]. inversion B.
    assert (T = S) as B. {
      eapply unique_tight_bounds; eauto.
    }
    subst. assumption.
  - (* All-<:-All *)
    inversion HT0; subst.
    assert (record_type (open_typ x T)) as B. {
      eapply record_type_new; eassumption.
    }
    rewrite H5 in B. destruct B as [? B]. inversion B.
    apply_fresh pt_lambda as y.
    eapply H3; eauto.
    eapply subtyp_trans. eapply tight_to_general_subtyping. eassumption. eassumption.
    eapply subtyp_trans.
    eapply narrow_subtyping. eapply H8; eauto.
    eapply subenv_last. eapply tight_to_general_subtyping. eapply Hsub.
    eapply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
    eapply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
    eapply H; eauto.
Qed.

(*
Lemma (Possible types completeness for values)

If `G ~ s` and `x = v in s` and  `G |-! v: T` then `T in Ts(G, x, v)`.
 *)

Lemma possible_types_completeness_for_values: forall G s x v T,
  wf_sto G s ->
  binds x v s ->
  ty_trm ty_precise sub_general G (trm_val v) T ->
  possible_types G x v T.
Proof.
  introv Hwf Bis Hty. destruct v as [S ds | S t].
  - apply new_intro_inversion in Hty. destruct Hty as [Heq Htype]. subst.
    eapply pt_bnd. eapply pt_new. reflexivity.
  - remember Hty as Hty'. clear HeqHty'. inversion Hty'; subst.
    + apply all_intro_inversion in Hty. destruct Hty as [T' Heq]. subst.
      apply_fresh pt_lambda as y.
      eapply H5; eauto.
      apply subtyp_refl.
      apply subtyp_refl.
    + assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
      specialize (H Heqm1). destruct H. inversion H.
Qed.

(*
Lemma (Possible types completeness)

If `G ~ s` and `x = v in s` and  `G |-# x: T` then `T in Ts(G, x, v)`.

Lemma (Possible types)

If `G ~ s` and `G |- x: T` then, for some value `v`,
`s(x) = v` and `T in Ts(G, x, v)`.
*)

Lemma possible_types_completeness_tight: forall G s x T,
  wf_sto G s ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) T ->
  exists v, binds x v s /\ possible_types G x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise sub_general G (trm_val v) T) as A. {
      destruct (ctx_binds_to_sto_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      eapply weaken_ty_trm. assumption. rewrite concat_assoc.
      eapply wf_sto_to_ok_G. eassumption.
    }
    destruct A as [v [Bis Hty]].
    exists v. split. apply Bis. eapply possible_types_completeness_for_values; eauto.
  - specialize (IHty_trm x Hwf).
    destruct IHty_trm as [v [Bis Hp]]; try reflexivity.
    exists v. split. assumption. eapply pt_bnd. eapply Hp. reflexivity.
  - specialize (IHty_trm x Hwf).
    destruct IHty_trm as [v [Bis Hp]]; try reflexivity.
    exists v. split. assumption. inversion Hp; subst.
    + lets Htype: (record_type_new Hwf Bis). rewrite H4 in Htype. inversion Htype. inversion H0.
    + assumption.
  - specialize (IHty_trm1 x Hwf). destruct IHty_trm1 as [v [Bis1 Hp1]]; try reflexivity.
    specialize (IHty_trm2 x Hwf). destruct IHty_trm2 as [v' [Bis2 Hp2]]; try reflexivity.
    unfold binds in Bis1. unfold binds in Bis2. rewrite Bis2 in Bis1. inversions Bis1.
    exists v. split. eauto. apply pt_and; assumption.
  - specialize (IHty_trm x Hwf). destruct IHty_trm as [v [Bis Hp]]; try reflexivity.
    exists v. split. apply Bis. eapply possible_types_closure_tight; eauto.
Qed.

Lemma tight_ty_rcd_typ__new: forall G s x A S U,
  wf_sto G s ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_rcd (dec_typ A S U)) ->
  exists T ds, binds x (val_new T ds) s.
Proof.
  introv Hwf Hty.
  destruct (possible_types_completeness_tight Hwf Hty) as [v [Bis Hpt]].
  inversion Hpt; subst; repeat eexists; eauto.
Qed.


Lemma general_to_tight: forall G0 s0,
  wf_sto G0 s0 ->
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
  intros G0 s0 Hwf.
  apply ts_mutind; intros; subst; eauto.
  - assert (exists S ds, binds x (val_new S ds) s0) as Bis. {
      eapply tight_ty_rcd_typ__new; eauto.
    }
    destruct Bis as [? [? Bis]].
    eapply proj2. eapply tight_bound_completeness; eauto.
  - assert (exists S ds, binds x (val_new S ds) s0) as Bis. {
      eapply tight_ty_rcd_typ__new; eauto.
    }
    destruct Bis as [? [? Bis]].
    eapply proj1. eapply tight_bound_completeness; eauto.
Qed.

Lemma general_to_tight_subtyping: forall G s S U,
   wf_sto G s ->
  subtyp ty_general sub_general G S U ->
  subtyp ty_general sub_tight G S U.
Proof.
  intros. apply* general_to_tight.
Qed.

Lemma possible_types_closure: forall G s x v S T,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v S ->
  subtyp ty_general sub_general G S T ->
  possible_types G x v T.
Proof.
  intros. eapply possible_types_closure_tight; eauto.
  eapply general_to_tight_subtyping; eauto.
Qed.

Lemma possible_types_completeness: forall G s x T,
  wf_sto G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) T ->
  exists v, binds x v s /\ possible_types G x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise sub_general G (trm_val v) T) as A. {
      destruct (ctx_binds_to_sto_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      eapply weaken_ty_trm. assumption. rewrite concat_assoc.
      eapply wf_sto_to_ok_G. eassumption.
    }
    destruct A as [v [Bis Hty]].
    exists v. split. apply Bis. eapply possible_types_completeness_for_values; eauto.
  - specialize (IHty_trm x Hwf).
    destruct IHty_trm as [v [Bis Hp]]; try reflexivity.
    exists v. split. assumption. eapply pt_bnd. eapply Hp. reflexivity.
  - specialize (IHty_trm x Hwf).
    destruct IHty_trm as [v [Bis Hp]]; try reflexivity.
    exists v. split. assumption. inversion Hp; subst.
    + lets Htype: (record_type_new Hwf Bis). rewrite H4 in Htype. inversion Htype. inversion H0.
    + assumption.
  - specialize (IHty_trm1 x Hwf). destruct IHty_trm1 as [v [Bis1 Hp1]]; try reflexivity.
    specialize (IHty_trm2 x Hwf). destruct IHty_trm2 as [v' [Bis2 Hp2]]; try reflexivity.
    unfold binds in Bis1. unfold binds in Bis2. rewrite Bis2 in Bis1. inversions Bis1.
    exists v. split. eauto. apply pt_and; assumption.
  - specialize (IHty_trm x Hwf). destruct IHty_trm as [v [Bis Hp]]; try reflexivity.
    exists v. split. apply Bis. eapply possible_types_closure; eauto.
Qed.

Lemma possible_types_lemma: forall G s x v T,
  wf_sto G s ->
  binds x v s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) T ->
  possible_types G x v T.
Proof.
  introv Hwf Bis Hty.
  lets A: (possible_types_completeness Hwf Hty).
  destruct A as [v' [Bis' Hp]].
  unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis. inversions Bis.
  assumption.
Qed.

Lemma ctx_binds_to_sto_binds_typing: forall G s x T,
  wf_sto G s ->
  binds x T G ->
  exists v, binds x v s /\ ty_trm ty_precise sub_general G (trm_val v) T.
Proof.
  introv Hwf Bi.
  lets A: (ctx_binds_to_sto_binds_raw Hwf Bi).
  destruct A as [G1 [G2 [v [HeqG [Bis Hty]]]]].
  exists v. split; eauto.
  subst. rewrite <- concat_assoc.
  apply weaken_ty_trm; eauto.
  rewrite concat_assoc.
  eapply wf_sto_to_ok_G; eauto.
Qed.

(*
Lemma (Canonical forms 1)
If G ~ s and G |- x: all(x: T)U then s(x) = lambda(x: T')t where G |- T <: T' and G, x: T |- t: U.
 *)
Lemma canonical_forms_1: forall G s x T U,
  wf_sto G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_all T U) ->
  (exists L T' t, binds x (val_lambda T' t) s /\ subtyp ty_general sub_general G T T' /\
  (forall y, y \notin L -> ty_trm ty_general sub_general (G & y ~ T) (open_trm y t) (open_typ y U))).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_sto_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  inversion Hp; subst.
  - lets Htype: (record_type_new Hwf Bis). rewrite H3 in Htype.
    destruct Htype as [ls Htyp]. inversion Htyp.
  - pick_fresh y. exists (dom G \u L). exists S0. exists t.
    split. apply Bis. split. assumption.
    intros y0 Fr0.
    eapply ty_sub.
    intros Contra. inversion Contra.
    eapply narrow_typing.
    eapply H1; eauto.
    apply subenv_last. apply H5.
    apply ok_push. eapply wf_sto_to_ok_G; eauto. eauto.
    apply ok_push. eapply wf_sto_to_ok_G; eauto. eauto.
    eapply H6; eauto.
Qed.

(*
Lemma (Canonical forms 2)

If G ~ s and G |- x: {a: T} then s(x) = new(x: S)d for some type S, definition d such that G |- d: S and d contains a definition {a = t} where G |- t: T.

*)
Lemma canonical_forms_2: forall G s x a T,
  wf_sto G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_rcd (dec_trm a T)) ->
  (exists S ds t, binds x (val_new S ds) s /\ ty_defs G (open_defs x ds) (open_typ x S) /\ defs_has (open_defs x ds) (def_trm a t) /\ ty_trm ty_general sub_general G t T).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_sto_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  apply pt_rcd_trm_inversion with (s:=s) in Hp; eauto.
  destruct Hp as [S' [ds [t' [Heq [Hdefs Htyd]]]]].
  subst.
  exists S' ds t'.
  split; try split; try split; try assumption.
  eapply new_ty_defs; eauto.
Qed.
