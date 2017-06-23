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
Require Import Invertible.

(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_path (p_var x))
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.

Lemma avar_b_typ_false: forall G b T,
    G |- trm_path (p_var (avar_b b)): T -> False.
Proof.
  introv Ht. dependent induction Ht.
  false (IHHt _ eq_refl).
  false (IHHt2 _ eq_refl).
  false (IHHt _ eq_refl).
Qed.

Lemma paths_equiv_typing: forall T G p p' U,
    inert G ->
    precise_flow p G T U ->
    precise_flow p' G T U ->
    G |-# open_typ_p p T <: open_typ_p p' T.
Proof.
  intro. induction T; introv Hi Hp1 Hp2; auto; lets His: (pf_inert_sngl_T Hi Hp1);
           inversions His; try inversions H.
  - Admitted.

Lemma paths_equiv_typing_bnd: forall G p p' T,
    inert G ->
    G |-! trm_path p: typ_bnd T ->
    G |-! trm_path p': typ_bnd T ->
    G |-# open_typ_p p T <: open_typ_p p' T.
Proof.
  introv Hi Hp Hp'.
  assert (record_type T) as Hr. {
    destruct (precise_flow_lemma Hp) as [U Pf].
    apply* pf_inert_rcd_bnd_U.
  }
  gen p p'. induction T; intros p1 Hp1 p2 Hp2; auto.
  - destruct d as [A S U | a m t]. assert (S = U) as Ht01 by admit. subst.
    unfold open_typ_p. simpl. eapply subtyp_typ_t.
    apply ty_rec_elim_p in Hp1. apply ty_rec_elim_p in Hp2. Abort.

Lemma safety: forall G s t T,
    G ~~ s ->
    inert G ->
    G |- t : T ->
        (normal_form t \/
         (exists s' t' G' G'',
             t / s ⇒ t' / s'
           /\ G' = G & G''
           /\ G' |- t' : T
           /\ G' ~~ s'
           /\ inert G')).
Proof.
  introv Hwf Hi H. dependent induction H; try solve [left; eauto].
  - (* All-E *) right.
    lets C: (canonical_forms_1 Hwf Hi H).
    destruct C as [L [T' [t [Bis [Hsub Hty]]]]].
    exists s (t |^ z) G (@empty typ).
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
    apply ty_sub with (T:=S).
    assumption. apply subtyp_refl.
    eauto. eauto. eauto. split*.
  - (* Fld-E *) right.
    destruct p as [[b | x] | p].
    + false* avar_b_typ_false.
    + pose proof (canonical_forms_2 Hi Hwf H) as [S [ds [t [Bis [Has Ty]]]]].
      exists s (trm_let t (trm_path (p_var (avar_b 0)))) G (@empty typ). split. apply* red_sel.
      split. rewrite* concat_empty_r. split. apply ty_let with (T:=T) (L:=dom G); auto.
      introv Hx. unfold open_trm. simpl. case_if. auto. split*.
    + exists s (trm_let (trm_path (p_sel p t))
                   (trm_path (p_sel (p_var (avar_b 0)) a))) G (@empty typ).
      split. apply red_path. split. rewrite* concat_empty_r. split.
      apply ty_let with (L:=dom G) (T:=typ_rcd {a [gen] T}). assumption. introv Hx.
      unfold open_trm. simpl. case_if. constructor. constructor. auto. split*.
  - (* Let *) right.
    destruct t.
    + lets Hv: (val_typing H).
      destruct Hv as [T' [Htyp Hsub]].
      pick_fresh x. assert (x \notin L) as FrL by auto. specialize (H0 x FrL).
      exists (s & x ~ v) (u |^ x) (G & x ~ T') (x ~ T').
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
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3 [Hwf' Hi']]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf Hi). destruct IHty_trm as [IH | IH]; auto. inversions IH.
      * assert (exists y, x = avar_f y) as A. {
          eapply var_typing_implies_avar_f. eassumption.
        }
        destruct A as [y A]. subst.
        exists s (u |^ y) G (@empty typ).
        split.
        apply red_let_var.
        split.
        rewrite concat_empty_r. reflexivity.
        split.
        pick_fresh z. assert (z \notin L) as FrL by auto. specialize (H0 z FrL).
        rewrite subst_intro_trm with (x:=z).
        rewrite <- subst_fresh_typ with (x:=z) (y:=y).
        eapply subst_ty_trm. eapply H0.
        apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
        rewrite subst_fresh_typ. assumption. eauto. eauto. eauto. split*.
      * destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3 [Hwf' Hi']]]]]]]].
        exists s' (trm_let t' u) G' G''.
        split. apply red_let_tgt. assumption.
        split. assumption. split.
        apply ty_let with (L:=L \u dom G') (T:=T); eauto.
        intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
        rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
        rewrite IH2.
        rewrite <- IH2. eauto.
  - (* ty_rec_elim *)
    specialize (IHty_trm Hwf Hi).
    destruct IHty_trm as [Hn | [s' [t' [G' [G'' [Hb [Heq [Ht [Hwf' Hi']]]]]]]]]; auto.
    right. exists s' t' G' G''. split. assumption. split. assumption. split; auto.
    inversion Hb.
    * inversions H0. inversions H9. inversions H11.
      destruct (canonical_forms_2 Hi Hwf H7) as [V [ds' [t' [Hb' [Hds Ht']]]]].
      apply (general_to_tight_typing Hi) in H7. apply (general_to_tight_norm Hi) in H9.
      apply (invertible_lemma Hi) in H7; auto.
      destruct (invertible_to_precise_trm_dec Hi H7) as [U' [m' [Hp [Heq _]]]].
      specialize (Heq eq_refl). destruct Heq. subst.
      lets Hxm: (ty_fld_elim_p Hp H8).
      apply (binds_func H2) in Hb'. inversions Hb'.
      unfolds defs_has. simpls. rewrite Hds in H3. inversions H3.
      apply (general_to_tight_typing Hi) in H.
      assert (G |-# p_sel (p_var (avar_f x)) m \||/) as Hn. {
        apply precise_to_tight in Hp. destruct Hp as [Hp _].
        apply* norm_path_t.
      }
      apply (invertible_lemma Hi H) in Hn. inversions Hn.
      destruct (precise_flow_lemma Hxm) as [T1 Pf1].
      destruct (precise_flow_lemma H0) as [T2 Pf2].
      lets Heq: (pf_inert_bnd_U Hi Pf2). subst.
      apply (p_bound_unique Hi Pf1) in Pf2. subst. inversions H8. inversions H1.
      + apply (pf_inert_lambda_U Hi) in Pf1. inversion Pf1.
      + apply (pf_inert_bnd_U Hi) in Pf1. inversions Pf1.
        apply ty_let with (L:=dom(G & G'')) (T:=typ_bnd T0). apply* weaken_ty_trm.
        intros y Hy. unfold open_trm. simpl. case_if.
        assert (G & G'' & y ~ typ_bnd T0 |-! trm_path (p_var (avar_f y)): typ_bnd T0)
          as Hty by auto.
        assert (G & G'' & y ~ typ_bnd T0 |-!
                            trm_path (p_sel (p_var (avar_f x)) m) : typ_bnd T0) as Hxm'. {
          apply wf_sto_to_ok_G in Hwf'.
          apply weaken_ty_trm_p; auto. apply weaken_ty_trm_p; assumption.
        }
        assert (inert (G & G'' & y ~ typ_bnd T0)) as Hi'' by auto. admit. (*
        lets Hpet: (paths_equiv_typing Hi'' Hty Hxm').
        apply ty_sub with (T:=open_typ_p (p_var (avar_f y)) T0).
        apply ty_rec_elim. constructor*. apply* norm_var. apply tight_to_general in Hpet.
        apply Hpet. *)
      + apply (pf_sngl_U Hi) in Pf1. inversions Pf1.
    * inversions H2.
  - (* ty_and *)
    right.
(*
    specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto.
    right. destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
    exists s' t' G' G''.
    split; try split; try split; try assumption.
    apply ty_sub with (T:=T).
    assumption.
    rewrite IH2. apply weaken_subtyp. assumption. *) admit.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto.
    right. destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
    exists s' t' G' G''.
    split; try split; try split; try assumption.
    apply ty_sub with (T:=T).
    assumption.
    rewrite IH2. apply weaken_subtyp. assumption. subst*.
Qed.
