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

Lemma record_has_ty_defs: forall G S T ds D,
  G, S /- ds :: T ->
  record_has T D ->
  exists d, defs_has ds d /\ G, S /- d : D.
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

Lemma new_ty_defs: forall G S sta sto x T ds,
  well_formed G S sta sto ->
  inert G ->
  binds x (val_new T ds) sta ->
  G, S /- open_defs x ds :: open_typ x T.
Proof.
  introv Hwf Hin Bis.
  lets Htyv: (val_new_typing Hwf Hin Bis).
  inversion Htyv; subst.
  - pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H2 y FrL).
    rewrite subst_intro_defs with (x:=y) by auto.
    rewrite subst_intro_typ with (x:=y) by auto.
    eapply subst_ty_defs.
    + apply H2.
    + eauto.
    + auto.
    + auto.
    + rewrite <- subst_intro_typ with (x:=y) by auto.
      eapply ty_rec_elim. apply ty_var. eapply wf_stack_val_new_in_G; eauto.
Qed.

Lemma corresponding_types_ty_trms: forall G S sta sto ds x V,
  well_formed G S sta sto ->
  inert G ->
  binds x (typ_bnd V) G ->
  binds x (val_new V ds) sta ->
  (forall a T',
      G, S |-! trm_var (avar_f x) : typ_rcd (dec_trm a T') ->
      exists t, defs_has (open_defs x ds) (def_trm a t) /\
           G, S |- t : T').
Proof.
  introv Hwf Hin Bi Bis Hty.
  pose proof (new_ty_defs Hwf Hin Bis) as Htds.
  destruct (precise_flow_lemma Hty) as [U Hpf]. 
  pose proof (inert_typ_bnd_record Hin Bi) as Hrec.
  pose proof (pf_binds Hpf). 
  pose proof (binds_func Bi H); subst.
  pose proof (precise_flow_record_has Hin Hpf) as Hrh.
  pose proof (record_has_ty_defs Htds Hrh) as [d [Hds Htd]].
  inversion Htd; subst.
  exists t. auto.
Qed.

Lemma canonical_forms_2: forall G S sta sto x a T,
  well_formed G S sta sto ->
  inert G ->
  G, S |- trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
  (exists V ds t, 
      binds x (val_new V ds) sta /\ 
      defs_has (open_defs x ds) (def_trm a t) /\ 
      G, S |- t : T).
Proof.
  introv Hwf Hin Hty.
  pose proof (typing_implies_bound Hty) as [V Bi].
  pose proof (general_to_tight_typing Hin Hty) as Hty'.
  pose proof (invertible_typing_lemma Hin Hty') as Hinv.
  pose proof (invertible_to_precise_trm_dec Hin Hinv) as [T' [Hx Hs]].
  pose proof (corresponding_types Hwf Hin Bi)
    as [[L [U [W [S1 [W1 [t [Hb [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [[U [ds [Hb [Ht Heq]]]] | [U [U' [l [Hb [Ht [Heq [Hs1 Hs2]]]]]]]]].
  + assert (H: exists T, record_type T /\ V = (typ_bnd T)).
    { pose proof (binds_inert Bi Hin) as Hgt.
      induction Hgt.
      - destruct (precise_flow_lemma Hx) as [W' H].
        lets Hpb: (pf_binds H). apply (binds_func Bi) in Hpb. subst.
        apply precise_flow_all_inv in H. inversion H.
      - exists T0. auto.
      - inversion Heq.
      - inversion Heq.
    }
    destruct H as [T0 [Hrt Hsubst]]; subst V; rename T0 into V.
    inversion Hsubst.
  + subst.
    exists U ds.
    pose proof (new_ty_defs Hwf Hin Hb) as Htd.
    pose proof (corresponding_types_ty_trms Hwf Hin Bi Hb Hx) as [t [H1 H2]].
    exists t.
    split; auto.
    split; auto.
    apply tight_to_general in Hs; auto.
    apply ty_sub with (T:=T'); auto.
  + assert (H: exists T, record_type T /\ V = (typ_bnd T)).
    { pose proof (binds_inert Bi Hin) as Hgt.
      induction Hgt.
      - destruct Heq as [Heq | Heq]; inversion Heq.
      - exists T0. auto.
      - pose proof (precise_flow_lemma Hx) as [W' H].
        lets Hpb: (pf_binds H). apply (binds_func Bi) in Hpb. subst.
        apply (precise_flow_ref_inv) in H.
        inversion H.
      - destruct Heq as [Heq | Heq].
        + pose proof (precise_flow_lemma Hx) as [W' H].
          lets Hpb: (pf_binds H). apply (binds_func Bi) in Hpb. subst.
          apply (precise_flow_nref_inv) in H. inversion H.
        + inversion Heq.
    }
    destruct Heq as [Heq | Heq]; 
      destruct H as [T0 [Hrt Hsubst]]; subst V; rename T0 into V; 
      inversion Hsubst.
Qed.
