Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Narrowing.
Require Import Some_lemmas.
Require Import Canonical_forms1.
Require Import Canonical_forms2.
Require Import Inert_types.
Require Import General_to_tight.
Require Import Invertible_typing.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Proofs *)

(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.

Lemma preservation: forall G s t s' t' T,
    G ~~ s ->
    inert G ->
    t / s => t' / s' ->
    G |- t : T ->
    exists G', inert G' /\
          G & G' ~~ s' /\
          G & G' |- t' : T.
Proof.
  introv Hwf Hin Hred Ht.
  gen t'.
  dependent induction Ht; intros; try solve [inversions Hred].
  - pose proof (canonical_forms_1 Hwf Hin Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    inversions Hred. 
    apply (binds_func H4) in Bis. inversions Bis.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y); auto. 
    rewrite subst_intro_trm with (x:=y); auto.
    eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ. 
  - pose proof (canonical_forms_2 Hin Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    inversions Hred.
    apply (binds_func H1) in Bis. inversions Bis.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    rewrite <- (defs_has_inv Has H5). assumption.
  - destruct t.
    + inversions Hred; try solve [inversion H6].
      pick_fresh y. 
      exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
      rewrite subst_intro_trm with (x:=y); auto.
      rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
      eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ.
    + inversions Hred; try solve [inversion H6].
      pose proof (wf_sto_notin_dom Hwf H6).
      pose proof (val_typing Ht) as [V [Hv Hs]].
      pick_fresh y. assert (y \notin L) by auto.
      specialize (H y H2).
      exists (x ~ V). repeat split. 
      * rewrite <- concat_empty_l. constructor~.
        apply (precise_inert_typ Hv).
      * constructor~. 
        apply (precise_to_general Hv).
      * rewrite subst_intro_trm with (x:=y); auto.
        rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
        eapply subst_ty_trm; eauto. 
        { eapply weaken_rules; eauto. }
        { apply~ fv_ctx_types_push. }
        { rewrite~ subst_fresh_typ. 
          pose proof (ty_var (binds_tail x V G)).
          apply (ty_sub H3). apply (weaken_subtyp Hs); eauto. 
        }
    + inversions Hred. 
      specialize (IHHt Hwf Hin t0' H6) as [G' [Hin' [Hwf' Ht']]].
      exists G'. repeat split; auto.
      apply_fresh ty_let as z; eauto. 
      eapply weaken_rules; eauto.
    + inversions Hred. 
      specialize (IHHt Hwf Hin t0' H6) as [G' [Hin' [Hwf' Ht']]].
      exists G'. repeat split; auto.
      apply_fresh ty_let as z; eauto. 
      eapply weaken_rules; eauto.
    + inversions Hred. 
      specialize (IHHt Hwf Hin t0' H6) as [G' [Hin' [Hwf' Ht']]].
      exists G'. repeat split; auto.
      apply_fresh ty_let as z; eauto. 
      eapply weaken_rules; eauto.
  - specialize (IHHt Hwf Hin t' Hred) as [G' [Hin' [Hwf' Ht']]].
    exists G'. repeat split; auto.
    apply weaken_subtyp with (G2:=G') in H.
    + apply (ty_sub Ht' H).
    + eauto.
Qed.

Lemma progress: forall G t s T,
    G ~~ s ->
    inert G ->
    G |- t : T ->
    (normal_form t \/ exists t' s', t / s => t' / s').
Proof.
  introv Hwf Hin Ht. dependent induction Ht; try solve [left; auto].
  - pose proof (canonical_forms_1 Hwf Hin Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    right. exists (open_trm z t) s.
    eapply red_app; eauto.
  - pose proof (canonical_forms_2 Hin Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    right. exists t s.
    eapply red_sel; eauto.
  - right. destruct t.
    + pose proof (var_typing_implies_avar_f Ht) as [x A]. subst.
      exists (open_trm x u) s.
      apply red_let_var.
    + pick_fresh x.
      exists (open_trm x u) (s & x ~ v).
      eapply red_let; auto.
    + specialize (IHHt Hwf Hin) as [IH | [t' [s' Hred]]].
      * inversion IH.
      * exists (trm_let t' u) s'.
        apply~ red_let_tgt.
    + specialize (IHHt Hwf Hin) as [IH | [t' [s' Hred]]].
      * inversion IH.
      * exists (trm_let t' u) s'.
        apply~ red_let_tgt.
    + specialize (IHHt Hwf Hin) as [IH | [t' [s' Hred]]].
      * inversion IH.
      * exists (trm_let t' u) s'.
        apply~ red_let_tgt.
  - specialize (IHHt Hwf Hin) as [IH | [t' [s' Hred]]].
    + left. assumption.
    + right. exists t' s'. assumption.
Qed.

Lemma safety: forall G s t T,
    G ~~ s ->
    inert G ->
    G |- t : T ->
    (normal_form t \/ (exists s' t' G' G'', t / s => t' / s' /\ G' = G & G'' /\ G' |- t' : T /\ G' ~~ s' /\ inert G')).
Proof.
  introv Hwf Hg H. dependent induction H; try solve [left; eauto].
  - (* All-E *) right.
    lets C: (canonical_forms_1 Hwf Hg H).
    destruct C as [L [T' [t [Bis [Hsub Hty]]]]].
    exists s (open_trm z t) G (@empty typ).
    split.
    apply red_app with (T:=T'). assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
    eapply subst_ty_trm. eapply Hty.
    apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
    rewrite subst_fresh_typ.
    assumption. 
    eauto. eauto. eauto. eauto.
  - (* Fld-E *) right.
    pose proof (canonical_forms_2 Hg Hwf H) as [S [ds [t [Bis [Has Ty]]]]].
    exists s t G (@empty typ).
    split.
    + apply red_sel with (T:=S) (ds:=ds); assumption.
    + split.
      * rewrite concat_empty_r. reflexivity.
      * split*.
  - (* Let *) right.
    destruct t.
    + (* var *)
      pose proof (var_typing_implies_avar_f H) as [x A]. subst a.
      exists s (open_trm x u) G (@empty typ).
      split.
      apply red_let_var.
      split.
      rewrite concat_empty_r. reflexivity.
      split.
      pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H0 y FrL).
      rewrite subst_intro_trm with (x:=y).
      rewrite <- subst_fresh_typ with (x:=y) (y:=x).
      eapply subst_ty_trm. eapply H0.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
      rewrite subst_fresh_typ. assumption. eauto. eauto. eauto. eauto.
    + pick_fresh x. assert (x \notin L) as FrL by auto. specialize (H0 x FrL).
      lets Hv: (val_typing H). destruct Hv as [V [Hv Hs]].
      exists (s & x ~ v) (open_trm x u) (G & x ~ V) (x ~ V).
      split.
      apply red_let. eauto.
      split. reflexivity. split. eapply narrow_typing. eapply H0. apply* subenv_last.
      apply* ok_push. split. apply* wf_sto_push. apply* precise_to_general.
      constructor*. apply* precise_inert_typ.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3 [Hwf' Hi']]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3 [Hwf' Hi]]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3 [Hwf' Hi]]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto.
    right. destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3 [Hwf' Hi]]]]]]]].
    exists s' t' G' G''.
    split; try split; try split; try assumption.
    apply ty_sub with (T:=T).
    assumption.
    rewrite IH2. apply weaken_subtyp. assumption.
    rewrite <- IH2. eapply wf_sto_to_ok_G. eassumption. split*.
Qed.
