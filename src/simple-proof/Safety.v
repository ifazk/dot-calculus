Set Implicit Arguments.

Require Import LibMap LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Narrowing.
Require Import Some_lemmas.
Require Import Canonical_forms1.
Require Import Canonical_forms2.
Require Import Canonical_forms3.
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
    pose proof (canonical_forms_4 Hin Hwf H) as [[l [BiLoc [Hty BiSto]]] | Hx'].
    {
      exists sta (sto[l := (Some y)]) (trm_let (trm_val (val_loc l)) (trm_var (avar_b 0))) G (@empty typ). exists S (@empty typ).
      split. 
      - apply red_asgn.
        + assumption.
        + lets Hbd: (LibMap.binds_def sto l None). unfold bindsM in BiSto. 
          rewrite Hbd in BiSto.
          destruct BiSto as [His Hsto]. assumption.
      - repeat split.
        * rewrite concat_empty_r. reflexivity.
        * rewrite concat_empty_r. reflexivity.
        * admit. (* Open with some x, and add x to G? *)
        * (* todo maybe change canon forms to add binds l T S? *)
          assumption.
          (* First use well_formed_update_store, then use well_formed_push_loc_stack *)
        * pose proof (general_to_tight Hg) as [A _].
          pose proof (A G S (trm_var (avar_f x)) (typ_ref T) H eq_refl).
          pose proof (A G S (trm_val (val_loc l)) (typ_ref T) Hty eq_refl).
          destruct (precise_ref_subtyping Hg BiLoc H1 H2 Hwf) as [U [HU [Hs1 Hs2]]].
          apply wt_store_update with (T:=U); try assumption.
          apply (ref_binds_typ HU). apply ty_sub with (T:=T); assumption.
    }
    { 
      exists sta (sto[l := y]) (trm_var (avar_f y)) G (@empty typ). exists S (@empty typ).
      split.
      + apply red_asgn with (l:=l).
        * assumption.
        * lets Hbd: (LibMap.binds_def sto l y'). unfold bindsM in BiSto. rewrite Hbd in BiSto.
          destruct BiSto as [His Hsto]. assumption.
      + repeat split.
        * rewrite concat_empty_r. reflexivity.
        * rewrite concat_empty_r. reflexivity.
        * assumption.
        * assumption.
        * pose proof (general_to_tight Hg) as [A _].
          pose proof (A G S (trm_var (avar_f x)) (typ_ref T) H eq_refl).
          pose proof (A G S (trm_val (val_loc l)) (typ_ref T) Hty eq_refl).
          destruct (precise_ref_subtyping Hg BiLoc H1 H2 Hwf) as [U [HU [Hs1 Hs2]]].
          apply wt_store_update with (T:=U); try assumption.
          apply (ref_binds_typ HU). apply ty_sub with (T:=T); assumption.
    }
  - (* ref *)
    right. pick_fresh l.
    exists sta (sto[l:=x]) (trm_val (val_loc l)) G (@empty typ). exists (S & l ~ T) (l ~ T).
    split. apply* red_ref_var.
    assert (l # S) as HS by auto.
    apply (wt_notin_dom Hwt HS).
    split. rewrite concat_empty_r. reflexivity.
    split. reflexivity.
    split. constructor. auto.
    split. constructor. assumption. auto.
    apply wt_store_new. assumption. auto.
    assumption. 
  - (* deref *)
    right.
    lets C: (canonical_forms_3 Hg Hwf Hwt H).
    destruct C as [l [y [BiLoc [_ [BiVal Htyval]]]]].
    exists sta sto (trm_var (avar_f y)) G (@empty typ). exists S (@empty typ).
    split. apply red_deref with (l:=l). assumption. assumption.
    split. rewrite concat_empty_r. reflexivity.
    split. rewrite concat_empty_r. reflexivity.
    split. assumption. split. assumption. assumption.
Qed.
