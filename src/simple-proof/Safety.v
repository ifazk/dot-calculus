Set Implicit Arguments.

Require Import LibMap LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Narrowing.
Require Import Some_lemmas.
Require Import Invertible_typing.
Require Import Canonical_forms1.
Require Import Canonical_forms2.
Require Import Canonical_forms3.
Require Import Canonical_forms4.
Require Import Inert_types.
Require Import General_to_tight.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Proofs *)

(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.

(*
Let G |- t: T and G ~ s. Then either

- t is a normal form, or
- there exists a store s', term t' such that s | t -> s' | t', and for any such s', t' there exists an environment G'' such that, letting G' = G, G'' one has G' |- t': T and G' ~ s'.
The proof is by a induction on typing derivations of G |- t: T.
*)

Lemma safety: forall G S sta sto t T,
    well_formed G S sta sto ->
    inert G ->
    G, S |- t : T ->
    (normal_form t \/ 
     (exists sta' sto' t' G' G'' S' S'',
         t / sta / sto => t' / sta' / sto' /\ 
         G' = G & G'' /\ 
         S' = S & S'' /\
         G', S' |- t' : T /\ 
         well_formed G' S' sta' sto')).
Proof.
  introv Hwf Hin H. dependent induction H; try solve [left; eauto].
  - (* All-E *) 
    right.
    lets C: (canonical_forms_1 Hwf Hin H).
    destruct C as [L [T' [t [Bis [Hsub Hty]]]]].
    exists sta sto (open_trm z t) G (@empty typ). exists S (@empty typ).
    repeat split.
    + apply red_app with (T:=T'). assumption.
    + rewrite concat_empty_r. reflexivity.
    + rewrite concat_empty_r. reflexivity.
    + pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
      rewrite subst_intro_typ with (x:=y); auto. rewrite subst_intro_trm with (x:=y); auto.
      eapply subst_ty_trm; auto.
      * eapply Hty.
      * apply* ok_push. 
      * rewrite* subst_fresh_typ.
    + assumption. 
  - (* Fld-E *) right.
    pose proof (canonical_forms_2 Hwf Hin H) as [V [ds [t [Bis [Has Ty]]]]].
    exists sta sto t G (@empty typ). exists S (@empty typ).
    split.
    + apply red_sel with (T:=V) (ds:=ds); assumption.
    + repeat split.
      * rewrite concat_empty_r. reflexivity.
      * rewrite concat_empty_r. reflexivity.
      * assumption.
      * assumption.
  - (* Let *) right.
    destruct t.
    + (* var *)
      assert (exists x, a = avar_f x) as A. {
        eapply var_typing_implies_avar_f. eassumption.
      }
      destruct A as [x A]. subst a.
      exists sta sto (open_trm x u) G (@empty typ). exists S (@empty typ).
      repeat split.
      * apply red_let_var.
      * rewrite concat_empty_r. reflexivity.
      * rewrite concat_empty_r. reflexivity.
      * pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H0 y FrL).
        rewrite subst_intro_trm with (x:=y); auto.
        rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
        eapply subst_ty_trm; auto. eapply H0.
        apply* ok_push.
        rewrite* subst_fresh_typ. 
      * assumption.
    + lets Hv: (val_typing H).
      destruct Hv as [T' [Htyp Hsub]].
      pick_fresh x. assert (x \notin L) as FrL by auto. specialize (H0 x FrL).
      exists (sta & x ~ v) sto (open_trm x u) (G & x ~ T) (x ~ T). exists S (@empty typ).
      repeat split.
      * apply* red_let. 
      * rewrite concat_empty_r. reflexivity. 
      * assumption. 
      * apply* well_formed_push_stack.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G''. exists S' S''.
      repeat split. 
      * apply red_let_tgt. assumption.
      * assumption. 
      * assumption.
      * apply ty_let with (L:=L \u dom G') (T:=T); eauto. intros.
        rewrite IH3. apply weaken_ty_trm_sigma. 
        rewrite IH2. eapply (proj41 weaken_rules_ctx). 
        apply H0. auto. reflexivity.
        rewrite <- IH2. apply ok_push. eapply wf_to_ok_G. eassumption. eauto.
        eapply wf_to_ok_S. subst. eauto.
      * rewrite IH2. rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G''. exists S' S''.
      repeat split. 
      * apply red_let_tgt. assumption.
      * assumption. 
      * assumption.
      * apply ty_let with (L:=L \u dom G') (T:=T); eauto. intros.
        rewrite IH3. apply weaken_ty_trm_sigma.
        rewrite IH2. eapply (proj41 weaken_rules_ctx). apply H0. auto. 
        reflexivity.
        rewrite <- IH2. apply ok_push. eapply wf_to_ok_G. eassumption. 
        eauto. eapply wf_to_ok_S. subst. eauto.
      * rewrite IH2. rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G''. exists S' S''.
      repeat split. 
      * apply red_let_tgt. assumption.
      * assumption. 
      * assumption. 
      * apply ty_let with (L:=L \u dom G') (T:=T); eauto. intros. 
        rewrite IH3. apply weaken_ty_trm_sigma.
        rewrite IH2. eapply (proj41 weaken_rules_ctx). apply H0. auto. 
        reflexivity.
        rewrite <- IH2. apply ok_push. eapply wf_to_ok_G. eassumption. 
        eauto. eapply wf_to_ok_S. subst. eauto.
      * assumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G''. exists S' S''.
      repeat split. 
      * apply red_let_tgt. assumption.
      * assumption. 
      * assumption. 
      * apply ty_let with (L:=L \u dom G') (T:=T); eauto. intros. 
        rewrite IH3. apply weaken_ty_trm_sigma.
        rewrite IH2. eapply (proj41 weaken_rules_ctx). apply H0. auto. 
        reflexivity.
        rewrite <- IH2. apply ok_push. eapply wf_to_ok_G. eassumption. 
        eauto. eapply wf_to_ok_S. subst. eauto.
      * assumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G''. exists S' S''.
      repeat split. 
      * apply red_let_tgt. assumption.
      * assumption. 
      * assumption. 
      * apply ty_let with (L:=L \u dom G') (T:=T); eauto. intros. 
        rewrite IH3. apply weaken_ty_trm_sigma.
        rewrite IH2. eapply (proj41 weaken_rules_ctx). apply H0. auto. 
        reflexivity.
        rewrite <- IH2. apply ok_push. eapply wf_to_ok_G. eassumption. 
        eauto. eapply wf_to_ok_S. subst. eauto.
      * assumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G''. exists S' S''.
      repeat split. 
      * apply red_let_tgt. assumption.
      * assumption. 
      * assumption. 
      * apply ty_let with (L:=L \u dom G') (T:=T); eauto. intros. 
        rewrite IH3. apply weaken_ty_trm_sigma.
        rewrite IH2. eapply (proj41 weaken_rules_ctx). apply H0. auto. 
        reflexivity.
        rewrite <- IH2. apply ok_push. eapply wf_to_ok_G. eassumption. 
        eauto. eapply wf_to_ok_S. subst. eauto.
      * assumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G''. exists S' S''.
      repeat split. 
      * apply red_let_tgt. assumption.
      * assumption. 
      * assumption. 
      * apply ty_let with (L:=L \u dom G') (T:=T); eauto. intros. 
        rewrite IH3. apply weaken_ty_trm_sigma.
        rewrite IH2. eapply (proj41 weaken_rules_ctx). apply H0. auto. 
        reflexivity.
        rewrite <- IH2. apply ok_push. eapply wf_to_ok_G. eassumption. 
        eauto. eapply wf_to_ok_S. subst. eauto.
      * assumption.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto.
    right. destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]]].
    exists sta' sto' t' G' G''. exists S' S''.
    split; try split; try split; try split; try split; try assumption.
    apply ty_sub with (T:=T).
    assumption.
    rewrite IH3. apply weaken_subtyp_sigma.
    rewrite IH2. apply weaken_subtyp_ctx. assumption.
    rewrite <- IH2. eapply wf_to_ok_G. eassumption.
    rewrite <- IH3. eapply wf_to_ok_S. eassumption.
  - (* asg *)
    right.
    pose proof (canonical_forms_4 Hin Hwf H) as [l [BiLoc [Hty BiSto]]].
    pick_fresh z. 
    exists (sta & z ~ (val_loc l)) (sto[l := (Some y)]) (open_trm z (trm_var (avar_b 0))) (G & z ~ (typ_ref T)) (z ~ (typ_ref T)). exists S (@empty typ).
    split. 
    + apply red_asgn. 
      * assumption.
      * destruct BiSto as [BiSto | [y' [BiSto _]]].
        { 
          lets Hbd: (LibMap.binds_def sto l None). unfold bindsM in BiSto. 
          rewrite Hbd in BiSto.
          destruct BiSto as [His Hsto]. assumption.
        } 
        { 
          lets Hbd: (LibMap.binds_def sto l (Some y')). unfold bindsM in BiSto. 
          rewrite Hbd in BiSto.
          destruct BiSto as [His Hsto]. assumption.
        }
      * auto.
    + repeat split.
      * rewrite concat_empty_r. reflexivity.
      * unfold open_trm. simpl. case_if. 
        assert (binds z (typ_ref T) (G & z ~ (typ_ref T))) by auto.
        apply* ty_var.
      * apply well_formed_push_loc_stack with (y:=y). 
        {
          apply (general_to_tight_typing Hin) in H.
          apply (general_to_tight_typing Hin) in Hty.
          pose proof (precise_nref_subtyping Hwf Hin BiLoc H Hty) as [U [Htp [Hs1 Hs2]]].
          apply well_formed_update_store with (T:=U); try reflexivity.
          - assumption. 
          - inversion* Htp.
          - apply (ty_sub H0 Hs1).
        }
        { auto. }
        { auto. }
        { apply binds_update_eq. }
        { assumption. }
  - (* ref *)
    right. pick_fresh l.
    exists sta (sto[l := None]) (trm_val (val_loc l)) G (@empty typ). exists (S & l ~ T) (l ~ T).
    split. 
    + apply* red_ref.
      assert (l # S) as HS by auto.
      apply (wf_notin_dom Hwf HS).
    + repeat split. 
      * rewrite concat_empty_r. reflexivity.
      * apply* ty_loc. 
      * apply* well_formed_new_store.
  - (* deref *)
    right. pose proof (canonical_forms_3 Hin Hwf H) as [l [y [BiLoc [_ [BiVal Htyval]]]]].
    exists sta sto (trm_var (avar_f y)) G (@empty typ). exists S (@empty typ).
    split. 
    + apply red_deref with (l:=l); assumption. 
    + repeat split. 
      * rewrite concat_empty_r. reflexivity.
      * rewrite concat_empty_r. reflexivity.
      * assumption. 
      * assumption.
  - (* nderef *)
    right. pose proof (canonical_forms_4 Hin Hwf H) as [l [BiLoc [Hty BiSto]]].
    destruct BiSto as [BiSto | [y' [BiSto Hy']]]. 
    {
      exists sta sto (trm_var (avar_f y)) G (@empty typ). exists S (@empty typ).
      split. 
      - apply red_nderef_notin with (l:=l); assumption.
      - repeat split. 
        + rewrite concat_empty_r. reflexivity.
        + rewrite concat_empty_r. reflexivity.
        + assumption. 
        + assumption.
    }
    {
      exists sta sto (trm_var (avar_f y')) G (@empty typ). exists S (@empty typ).
      split.
      - apply red_nderef_in with (l:=l); assumption.
      - repeat split.
        + rewrite concat_empty_r. reflexivity.
        + rewrite concat_empty_r. reflexivity.
        + assumption. 
        + assumption.
    }
Qed.