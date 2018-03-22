(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module proves the Lemmas about updated stores *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN LibExtra.
Require Import Definitions Binding
        RecordAndInertTypes PreciseTyping
        StronglyTypedStores CanonicalForms.


(** * Store updates *)
Lemma defs_update_typing: forall G ds U ds' a x T,
    defs_update ds a x ds' ->
    record_type U ->
    G /- ds :: U ->
    record_has U (dec_trm a T T) ->
    G ⊢ trm_var (avar_f x) : T ->
    G /- ds' :: U.
Proof.
  introv H; gen U T. induction H; intros.
  - inversions H0. inversions H7.
    inversions H1. eauto.
    constructor; eauto.
    inversions H7.
    assert (T1 = T) by (eapply (unique_rcd_trm H); eauto); subst.
    eauto.
  - inversions H1. inversions H.
    assert (record_type T0).
    { destruct H0 as [ls ?H]. inversions H0.
      exists ls0; auto. }
    inversion H2; subst T0 U D0.
    + constructor; eauto using defs_update_hasnt.
    + inversions H9. inversions H8; simpl in *.
      exfalso. eapply defs_update_hasnt_inv; eauto.
Qed.

Lemma sto_update_inert: forall G s s' x y a T,
    inert G ->
    strongly_typed G s ->
    G ⊢ trm_asn (avar_f x) a (avar_f y) : T ->
    sto_update s x a y s' ->
    strongly_typed G s'.
Proof.
  introv Hin Hst Hty Hsto.
  remember (trm_asn (avar_f x) a (avar_f y)) as t.
  induction Hty; inversions Heqt; eauto.
  pose proof (canonical_forms_obj Hin Hst Hty1) as [?S [?ds [?t [?H [?H ?H]]]]].
  unfold sto_update in Hsto.
  destruct Hsto as [?Hoks [?Hoks' [?Hdom [?Hbi [?T [?ds [?ds' [?H [?Hdefup ?Hbis']]]]]]]]].
  pose proof (binds_functional H2 H) as Hveq; inversions Hveq; clear H.
  unfold strongly_typed; repeat_split_right; auto.
  rewrite <- Hdom; apply Hst.
  destruct Hst as [?H [?H [?H ?H]]].
  intros. clear IHHty1 IHHty2 H3.
  pose proof (dom_to_binds H6) as [?T ?H].
  pose proof (H5 _ H6) as Htyv.
  rewrite H4 in H6.
  pose proof (dom_to_binds H6) as [?v ?H].
  pose proof (defs_update_open x Hdefup ds eq_refl) as [?ds' ?Hds'].
  destruct (var_decide x0 x).
  - subst. clear H7.
    eapply ty_val_obj_s; eauto.
    + pose proof (var_typ_rcd_to_binds Hin Hty1) as [?S [?T [?Hbi ?H]]].
      pose proof (binds_functional Hbi0 H3); subst T0; clear Hbi0.
      inversions Htyv. pose proof (binds_functional H9 H2); congruence.
      pose proof (binds_functional H2 H9). inversions H10.
      pose proof (binds_functional H3 H8). congruence.
    + inversions Htyv. pose proof (binds_functional H8 H2); congruence.
      pose proof (binds_functional H3 H7); subst; clear H7.
      pose proof (binds_functional H2 H8). inversions H7.
      pose proof (var_typ_rcd_to_binds Hin Hty1) as [?S [?T [?Hbi [?Hrh [?H ?H]]]]].
      pose proof (binds_functional H3 Hbi0). inversions H11.
      eapply defs_update_typing; eauto.
      pose proof (binds_inert H3 Hin). inversions H11.
      apply open_record_type; auto.
      rewrite H12; auto.
  - apply (Hbi _ _ n) in H7. rename n into Hneq.
    clear Hbis' H2 Hdefup.
    inversions Htyv; eauto.
Qed.

Lemma defs_update_exists: forall ds a t x,
  defs_has ds (def_trm a t) ->
  exists ds', defs_update ds a x ds'.
Proof.
  intros ds; induction ds; intros.
  - inversion H.
  - inversion H. cases_if.
    + inversions H1.
      exists (defs_cons ds (def_trm a (trm_var (avar_f x)))); constructor.
    + apply (IHds a t x) in H1.
      destruct H1 as [ds' ?H].
      exists (defs_cons ds' d). constructor; auto.
Qed.

Lemma sto_updateable: forall s x U ds a t y,
    ok s ->
    binds x (val_obj U (open_defs x ds)) s ->
    defs_has (open_defs x ds) (def_trm a t) ->
    exists s' ds',
      ok s' /\
      dom s = dom s' /\
      (forall z v, z <> x ->
              binds z v s ->
              binds z v s') /\
      defs_update (open_defs x ds) a y ds' /\
      binds x (val_obj U ds') s'.
Proof.
  intros s; induction s using env_ind; intros.
  - exfalso. apply (binds_empty_inv H0).
  - pose proof (defs_update_exists y H1) as [?ds' ?H].
    pose proof (binds_push_inv H0) as [[?H ?H] | [?H ?H]]; subst.
    + exists (s & x ~ val_obj U (ds')) ds'.
      repeat_split_right; auto.
      * destruct (ok_push_inv H); auto.
      * simpl_dom; auto.
      * intros.
        pose proof (binds_push_inv H4) as [[?H ?H] | [?H ?H]]; try congruence.
        auto.
    + assert (Hoks: ok s) by auto.
      pose proof (IHs x0 _ _ _ _ y Hoks H4 H1) as
          [?s' [?ds' [?Hoks' [?Hdeq [?H [?H ?H]]]]]].
      exists (s' & x ~ v) (ds'0). repeat_split_right; auto.
      * apply ok_push; auto.
        pose proof (ok_push_inv H) as [_ ?H].
        rewrite <- Hdeq; auto.
      * simpl_dom. rewrite Hdeq; auto.
      * intros.
        pose proof (binds_push_inv H9) as [[?H ?H] | [?H ?H]]; subst; auto.
Qed.

Lemma sto_update_exists: forall G s x y a S T,
    inert G ->
    strongly_typed G s ->
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a S T) ->
    G ⊢ trm_var (avar_f y) : S ->
    exists s', sto_update s x a y s'.
Proof.
  introv Hin Hst Hty HTy.
  pose proof (canonical_forms_obj).
  pose proof (canonical_forms_obj Hin Hst Hty) as [?S [?ds [?t [?Hbi [?Hdef _]]]]].
  unfold strongly_typed in Hst.
  destruct Hst as [?H [Hok ?H]].
  pose proof (sto_updateable ds y Hok Hbi Hdef) as [?s' [?ds' [?H ?H]]]; destruct_all.
  exists s'; unfold sto_update; repeat_split_right; auto.
  exists S0 (open_defs x ds) ds'; repeat_split_right; auto.
Qed.
