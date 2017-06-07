Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Some_lemmas.
Require Import Inert_types.
Require Import General_to_tight.
Require Import Invertible_typing.

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
  G /- ds :: T ->
  record_has T D ->
  exists d, defs_has ds d /\ G /- d : D.
Proof.
  introv Hdefs Hhas. induction Hdefs.
  - inversion Hhas; subst. exists d. split.
    + unfold defs_has. simpl. rewrite If_l; reflexivity.
    + assumption.
  - inversion Hhas; subst.
    + destruct (IHHdefs H4) as [d' [H1 H2]]. 
      exists d'. split.
      * unfold defs_has. simpl. rewrite If_r. apply H1.
        apply not_eq_sym. eapply defs_has_hasnt_neq; eauto.
      * assumption.
    + exists d. split.
      * unfold defs_has. simpl. rewrite If_l; reflexivity.
      * inversions* H4. 
Qed.

Lemma new_ty_defs: forall G s x T ds,
  G ~~ s ->
  inert G ->
  binds x (val_new T ds) s ->
  G /- open_defs x ds :: open_typ x T.
Proof.
  introv Hwf Hg Bis.
  lets Htyv: (val_new_typing Hwf Hg Bis).
  inversion Htyv; subst.
  - pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H1 y FrL).
    rewrite subst_intro_defs with (x:=y) by auto.
    rewrite subst_intro_typ with (x:=y) by auto.
    eapply subst_ty_defs.
    + apply H1.
    + eauto.
    + auto.
    + rewrite <- subst_intro_typ with (x:=y) by auto.
      eapply ty_rec_elim. apply ty_var. eapply wf_sto_val_new_in_G; eauto.
Qed.

Lemma corresponding_types_ty_trms: forall G s ds x S,
  G ~~ s ->
  inert G ->
  binds x (typ_bnd S) G ->
  binds x (val_new S ds) s ->
  (forall a T',
      G |-! trm_var (avar_f x) : typ_rcd (dec_trm a T') ->
      exists t, defs_has (open_defs x ds) (def_trm a t) /\
           G |- t : T').
Proof.
  introv Hwf Hg Bi Bis Hty.
  pose proof (new_ty_defs Hwf Hg Bis) as Htds.
  destruct (precise_flow_lemma Hty) as [U Hpf]. 
  pose proof (inert_typ_bnd_record Hg Bi) as Hrec.
  pose proof (pf_binds Hpf). 
  pose proof (binds_func Bi H); subst.
  pose proof (precise_flow_record_has Hg Hpf) as Hrh.
  pose proof (record_has_ty_defs Htds Hrh) as [d [Hds Htd]].
  inversion Htd; subst.
  exists t. auto.
Qed.

Lemma canonical_forms_2: forall G s x a T,
  inert G ->
  G ~~ s ->
  G |- trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
  (exists S ds t, binds x (val_new S ds) s /\ defs_has (open_defs x ds) (def_trm a t) /\ G |- t : T).
Proof.
  introv Hg Hwf Hty.
  pose proof (typing_implies_bound Hty) as [S Bi].
  pose proof (general_to_tight_typing Hg Hty) as Hty'.
  pose proof (invertible_typing_lemma Hg Hty') as Hinv.
  pose proof (invertible_to_precise_trm_dec Hg Hinv) as [T' [Hx Hs]].
  pose proof (corresponding_types Hwf Hg Bi)
    as [[L [U [V [S1 [V1 [t [Hb [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [U [ds [Hb [Ht Heq]]]]].
  + assert (H: exists T, record_type T /\ S = (typ_bnd T)).
    { pose proof (binds_inert Bi Hg) as Hgt.
      induction Hgt.
      - destruct (precise_flow_lemma Hx) as [W H].
        lets Hpb: (pf_binds H). apply (binds_func Bi) in Hpb. subst.
        apply (precise_flow_all_inv) in H. inversion H.
      - exists T0. auto.
    }
    destruct H as [T0 [Hrt Hsubst]]; subst S; rename T0 into S.
    inversion Hsubst.
  + subst.
    exists U ds.
    pose proof (new_ty_defs Hwf Hg Hb) as Htd.
    pose proof (corresponding_types_ty_trms Hwf Hg Bi Hb Hx) as [t [H1 H2]].
    exists t.
    split; auto.
    split; auto.
    apply tight_to_general in Hs; auto.
    apply ty_sub with (T:=T'); auto.
Qed.
