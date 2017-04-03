Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Some_lemmas.
Require Import Precise_flow.
Require Import Good_types.
Require Import General_to_tight.

Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
  record_has (typ_rcd D) D
| rh_andl : forall T D,
  record_has (typ_and T (typ_rcd D)) D
| rh_and : forall T D D',
  record_has T D' ->
  record_has (typ_and T D) D'.

Hint Constructors record_has.

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

Lemma record_sub_record_has:
  forall U D,
    record_sub U (typ_rcd D) ->
    record_has U D.
Proof.
  intros U D Hrs.
  dependent induction Hrs; auto.
Qed.

Lemma precise_flow_record_has: forall S G x D,
    record_type S ->
    precise_flow x G (typ_bnd S) (typ_rcd D) ->
    record_has (open_typ x S) D.
Proof.
  introv Hrec Hpf.
  pose proof (precise_flow_record_sub Hrec Hpf) as [Contra | H].
  - inversion Contra.
  - apply record_sub_record_has.
    auto.
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

Lemma corresponding_types_ty_trms: forall G s ds x S,
  wf_sto G s ->
  binds x (typ_bnd S) G ->
  binds x (val_new S ds) s ->
  (forall a T',
      ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_trm a T')) ->
      exists t, defs_has (open_defs x ds) (def_trm a t) /\
           ty_trm ty_general sub_general G t T').
Proof.
  intros G s ds x S Hwf Bi Bis a T' Hty.
  pose proof (new_ty_defs Hwf Bis) as Htds.
  pose proof (wf_good Hwf) as Hgd.
  pose proof (precise_flow_lemma Bi Hty) as Hpf.
  pose proof (good_typ_bnd_record Hgd Bi) as Hrec.
  pose proof (precise_flow_record_has Hrec Hpf) as Hrh.
  pose proof (record_has_ty_defs Htds Hrh) as [d [Hds Htd]].
  inversion Htd; subst.
  exists t. auto.
Qed.

Lemma ctx_binds_to_sto_binds_typing: forall G s x T,
  wf_sto G s ->
  binds x T G ->
  exists v, binds x v s /\ ty_trm ty_precise sub_general G (trm_val v) T.
Proof.
  introv Hwf Bi.
  lets A: (ctx_binds_to_sto_binds_raw Hwf Bi).
  destruct A as [G1 [G2 [v [HeqG [Bis Hty]]]]].
  exists v. split; auto.
  subst. rewrite <- concat_assoc.
  apply weaken_ty_trm; auto.
  rewrite concat_assoc.
  eapply wf_sto_to_ok_G; eauto.
Qed.

Lemma canonical_forms_2: forall G s x a T,
  wf_sto G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_rcd (dec_trm a T)) ->
  (exists S ds t, binds x (val_new S ds) s /\ ty_defs G (open_defs x ds) (open_typ x S) /\ defs_has (open_defs x ds) (def_trm a t) /\ ty_trm ty_general sub_general G t T).
Proof.
  introv Hwf Hty.
  pose proof (wf_good Hwf) as Hgd.
  pose proof (typing_implies_bound Hty) as [S Bi].
  pose proof (ctx_binds_to_sto_binds_typing Hwf Bi) as [v [Bis Htyv]].
  pose proof (general_to_tight_typing Hgd Hty) as Hty'.
  pose proof (tight_to_precise_trm_dec Hgd Hty') as [T' [Hpt Hsub]].
  assert (H: exists T, record_type T /\ S = (typ_bnd T)).
  { pose proof (good_binds Hgd Bi) as Hgt.
    induction Hgt.
    - pose proof (precise_flow_lemma Bi Hpt) as H.
      apply (precise_flow_all_inv) in H.
      inversion H.
    - exists T0. auto.
  }
  destruct H as [T0 [Hrt Hsubst]]; subst S; rename T0 into S.
  pose proof (corresponding_types Hwf Bi) as [[? [? [? [? [_ HS]]]]] | [T2 [ds [Hb [Hn HS]]]]];
  inversion HS.
  subst T2; clear HS.
  exists S ds.
  apply (binds_func Bis) in Hb. subst v.
  pose proof (new_ty_defs Hwf Bis) as Htd.
  pose proof (corresponding_types_ty_trms Hwf Bi Bis Hpt) as [t [H1 H2]].
  exists t. split; auto.
  split; auto.
  split; auto.
  apply tight_to_general in Hsub; auto.
  eapply ty_sub; eauto.
  intros Contra; inversion Contra.
Qed.
