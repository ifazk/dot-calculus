Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import Helper_lemmas.
Require Import Precise_types.
Require Import Substitution.
Require Import Invertible_typing.
Require Import General_to_tight.
Require Import Wellformed_store.

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
  inversions Htyv.
  pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H1 y FrL).
  rewrite subst_intro_defs with (x:=y) by auto.
  rewrite subst_intro_typ with (x:=y) by auto.
  eapply subst_ty_defs; eauto.
  rewrite <- subst_intro_typ with (x:=y) by auto.
  eapply ty_rec_elim. apply ty_var. eapply wf_sto_val_new_in_G; eauto.
Qed.

Lemma corresponding_types_ty_trms: forall G s ds x S a T',
  G ~~ s ->
  inert G ->
  binds x (typ_bnd S) G ->
  binds x (val_new S ds) s ->
  record_has (open_typ x S) (dec_trm a T') ->
  exists t, defs_has (open_defs x ds) (def_trm a t) /\
        G |- t : T'.
Proof.
  introv Hwf Hg Bi Bis Hr.
  pose proof (new_ty_defs Hwf Hg Bis) as Htds.
  pose proof (record_has_ty_defs Htds Hr) as [d [Hds Htd]].
  inversion Htd; subst.
  exists t. auto.
Qed.

Lemma var_typ_rcd_to_binds: forall G x a T,
    inert G ->
    G |- trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    (exists S T',
        binds x (typ_bnd S) G /\
        record_has (open_typ x S) (dec_trm a T') /\
        G |- T' <: T).
Proof.
  introv Hin Ht.
  destruct (typing_implies_bound Ht) as [S BiG].
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_trm_dec Hinv) as [T' [Htp Hs]].
  destruct (precise_flow_lemma Htp) as [U Pf].
  destruct (pf_inert_rcd_U Hin Pf) as [U' Hr]. subst.
  lets Hr': (precise_flow_record_has Hin Pf). apply pf_binds in Pf.
  exists U' T'. split. assumption. split. assumption. apply* tight_to_general.
Qed.

Lemma record_has_open: forall T D x,
    record_has T D ->
    record_has (open_typ x T) (open_dec x D).
Proof.
  introv Hr. induction Hr.
  constructor*.
  constructor*.
  unfolds open_typ. simpl. apply* rh_andr.
Qed.

Lemma val_mu_to_new: forall G v T U a x,
    inert G ->
    G |- trm_val v: typ_bnd T ->
    G |- trm_var (avar_f x) : open_typ x T ->
    record_has T (dec_trm a U) ->
    exists t ds,
      v = val_new T ds /\
      defs_has (open_defs x ds) (def_trm a t) /\
      G & x ~ open_typ x T |- t: (open_typ x U).
Proof.
  introv Hi Ht Hx Hr.
  lets Htt: (general_to_tight_typing Hi Ht).
  lets Hinv: (tight_to_invertible_v Hi Htt).
  lets Hp: (invertible_val_to_precise_rec Hinv).
  destruct (precise_bnd_inv Hp) as [ds Heq]. subst.
  inversions Hp. pick_fresh z. assert (z \notin L) as Hz by auto.
  specialize (H1 z Hz).
  apply record_has_open with (x:=z) in Hr.
  destruct (record_has_ty_defs H1 Hr) as [d [Hh Hd]]. inversions Hd. Admitted. (*
  exists t ds. split. reflexivity. split. rewrite subst_defs_has in Hh.
  eapply subst_ty_defs; eauto.
  rewrite <- subst_intro_typ with (x:=y) by auto.
  eapply ty_rec_elim. apply ty_var. eapply wf_sto_val_new_in_G; eauto.
  exists x t ds. split*.
Qed.*)

Lemma canonical_forms_2: forall G s x a T,
  inert G ->
  G ~~ s ->
  G |- trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
  (exists S ds t, binds x (val_new S ds) s /\ defs_has (open_defs x ds) (def_trm a t) /\ G |- t : T).
Proof.
  introv Hi Hwf Hty.
  destruct (var_typ_rcd_to_binds Hi Hty) as [S [T' [Bi [Hr Hs]]]].
  destruct (corresponding_types Hwf Hi Bi)
    as [[L [U [V [S1 [V1 [t [Hb [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [U [ds [Hb [Ht Heq]]]]].
  + inversions Heq.
  + subst. exists U ds.
    pose proof (new_ty_defs Hwf Hi Hb) as Htd. inversions Heq.
    pose proof (corresponding_types_ty_trms Hwf Hi Bi Hb Hr) as [t [H1 H2]].
    exists* t.
Qed.
