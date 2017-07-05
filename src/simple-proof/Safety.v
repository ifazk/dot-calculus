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

(* Typing for the evaluation context / term pair with an empty typing context. Internally, a typing context representing the types of variables in the stack is used. *)
Inductive ty_ec_trm: ctx -> ec -> trm -> typ -> Prop :=
| ty_e_hole : forall G s t T,
    G ~~ s ->
    inert G ->
    G |- t : T ->
    ty_ec_trm G (e_hole s) t T
| ty_e_term : forall L G s u t T U,
    G ~~ s ->
    inert G ->
    G |- t : T ->
    (forall x, x \notin L -> G & x ~ T |- (open_trm x u) : U) ->
    ty_ec_trm G (e_term s u) t U.

Lemma app_empty_inv: forall e s,
    app_ec (e_hole empty) e (e_hole s) ->
    e = e_hole s.
Proof.
  intros. inversions H. rewrite concat_empty_l. reflexivity.
Qed.

(* Lemma test_bnd: forall G x t T, *)
(*     inert G -> *)
(*     G |- trm_sel (avar_f x) t : T -> *)
(*     exists T', G |- trm_var (avar_f x) : typ_bnd T'. *)
(* Proof. *)
(*   introv Hin Ht. apply (general_to_tight_typing Hin) in Ht. *)
(*   inversions Ht. *)
(*   - apply (invertible_typing_lemma Hin) in H3. *)
(*     dependent induction H3. *)
(*     + admit. *)
(*     + eapply IHty_trm_inv; auto. *)
(*   - admit. *)
(* Qed. *)

Lemma term_to_hole: forall s u t t',
    red_ec (e_term s u) t (e_term s u) t' ->
    red_ec (e_hole s) t (e_hole s) t'.
Proof.
  intros. dependent induction H.
  - eapply red_ec_apply; eauto. 
  - eapply red_ec_project; eauto.
  - induction u; inversions x.
    eapply IHu2; eauto.
Qed.

Lemma preservation_hole: forall G s t e' t' T,
    red_ec (e_hole s) t e' t' ->
    G ~~ s ->
    inert G ->
    G |- t : T ->
    exists G', ty_ec_trm (G & G') e' t' T.
Proof. 
  introv Hred Hwf Hin Ht. 
  dependent induction Ht; try solve [inversion Hred].
  - admit.
  - admit.
  - inversions Hred.
    exists (@empty typ). rewrite concat_empty_r.
    eapply ty_e_term; eauto.
  - specialize (IHHt Hred Hwf Hin) as [G' IHHt].
    exists G'. inversions IHHt.
    + eapply ty_e_hole; eauto.
      apply weaken_subtyp with (G2:=G') in H; eauto.
    + apply_fresh ty_e_term as z; eauto; intros. assert (z \notin L) by auto.
      specialize (H3 z H4).
      apply weaken_subtyp with (G2:=(G' & z ~ T0)) in H; rewrite concat_assoc in *; eauto.
Qed.

(* Lemma let_type: forall G t u T, *)
(*     inert G -> *)
(*     G |- trm_let t u : T -> *)
(*     exists T', G |- t : T'. *)
(* Proof. *)
(*   introv Hin Ht. dependent induction Ht; eauto. *)
(* Qed. *)

(* Lemma let_open: forall L G t u T, *)
(*     inert G -> *)
(*     G |- trm_let t u : T -> *)
(*     exists T', (forall x, x \notin L -> G & x ~ T' |- (open_trm x u) : T). *)
(* Proof. *)
(*   introv Hin Ht. dependent induction Ht; eauto. *)
(* Qed. *)

Lemma preservation'': forall G e t e' t' T,
    red_ec e t e' t' ->
    ty_ec_trm G e t T ->
    exists G', ty_ec_trm (G & G') e' t' T.
Proof.
  introv Hred Ht.
  inversions Ht.
  { 
    eapply preservation_hole; eauto.
  }
  {
    rename H into Hwf. rename H0 into Hin.
    rename H1 into Ht1. rename H2 into Ht2.
    destruct t.
    - inversions Hred.
      pick_fresh y.
      exists (@empty typ). rewrite concat_empty_r.
      apply ty_e_hole; auto.
      rewrite subst_intro_trm with (x:=y); auto.
      rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
      eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ.
    - inversions Hred.
      pose proof (wf_sto_notin_dom Hwf H4).
      pose proof (val_typing Ht1) as [V [Hv Hs]].
      pick_fresh y. assert (y \notin L) by auto.
      specialize (Ht2 y H0).
      exists (x ~ V).
      apply ty_e_hole.
      * constructor~.
        apply (precise_to_general Hv).
      * constructor~.
        apply (precise_inert_typ Hv).
      * rewrite subst_intro_trm with (x:=y); auto.
        rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
        eapply subst_ty_trm; eauto.
        { eapply weaken_rules; eauto. }
        { apply~ fv_ctx_types_push. }
        {
          rewrite~ subst_fresh_typ.
          pose proof (ty_var (binds_tail x V G)).
          apply (ty_sub H1). apply (weaken_subtyp Hs); eauto.
        }
    - inversion Hred. rewrite <- H3 in Hred. apply term_to_hole in Hred. subst.
      pose proof (preservation_hole Hred Hwf Hin Ht1) as [G' Ht].
      inversions Ht.
      exists G'.
      eapply ty_e_term with (L:=L \u (dom G) \u (dom G')); eauto. intros. 
      assert (x0 \notin L) by auto.
      specialize (Ht2 x0 H3).
      eapply (proj41 weaken_rules); eauto.
    - inversion Hred. rewrite <- H1 in Hred. apply term_to_hole in Hred. subst.
      pose proof (preservation_hole Hred Hwf Hin Ht1) as [G' Ht].
      inversions Ht.
      exists G'.
      eapply ty_e_term with (L:=L \u (dom G) \u (dom G')); eauto. intros. 
      assert (x0 \notin L) by auto.
      specialize (Ht2 x0 H2).
      eapply (proj41 weaken_rules); eauto.
    - (* lemma for type of t1 *)
      inversions Hred.
      (* rename t' into t1. rename u into t3. *)
      (* rename T into T3. rename T0 into T2. *)
      (* pose proof (let_type Hin Ht1) as [T1 Ht']. *)
      exists (@empty typ). rewrite concat_empty_r.
      gen L.
      dependent induction Ht1; intros.
      + eapply ty_e_term with (L:=L); eauto. intros.
        unfold open_trm. simpl. specialize (H x H1).
        apply_fresh ty_let as z; eauto. admit.
      + eapply IHHt1 with (L:=L \u (dom G)); eauto. intros. 
        assert (x \notin L) by auto.
        specialize (Ht2 x H1).
        eapply narrow_typing; eauto. apply~ subenv_last.
  }
Qed.

Lemma open_1_test: forall G t y n T,
    G |- t : T ->
    n > 0 ->
    t = (open_rec_trm n y t).
    (* G & x ~ U |- open_trm x (open_rec_trm 1 y u) : T. *)
Proof.
  intros. gen G T y. induction t; intros.
  - destruct a.
    + simpl. case_if~. subst.
      apply var_typing_implies_avar_f in H. destruct H. inversion H.
    + reflexivity.
  - destruct v. 
    + simpl. dependent induction H; eauto. admit.
    + simpl. dependent induction H; eauto. admit.
  - destruct a. 
    + simpl. case_if~. subst. dependent induction H; eauto. 
    + reflexivity.
  - destruct a; destruct a0.
    + simpl. 
      repeat case_if; subst; dependent induction H; eauto; case_if. 
    + simpl. case_if; subst; dependent induction H; eauto; case_if. 
    + simpl. case_if; subst; dependent induction H; eauto; case_if. 
    + reflexivity.
  - simpl. dependent induction H; eauto.
    replace (trm_let t1 t2) with (trm_let (open_rec_trm 1 y t1) t2).
    + simpl. admit.
    + specialize (IHt1 _ _ H y). rewrite <- IHt1. reflexivity.
Qed.

(* Lemma preservation': forall G e t e' t' T, *)
(*     G ~~ (ec_sto e) -> *)
(*     inert G -> *)
(*     red_ec e t e' t' -> *)
(*     G |- t : T -> *)
(*     exists G', inert G' /\ *)
(*           G & G' ~~ (ec_sto e') /\ *)
(*           G & G' |- t' : T. *)
(* Proof. *)
(*   introv Hwf Hin Hred Ht. gen t'. *)
(*   dependent induction Ht; intros. *)
(*   - dependent induction Hred. *)
(*     +  *)
(*     + inversions Hred. admit. *)
(*     + dependent induction Hred. *)
(*       * admit. *)
(*       *  *)
(*   (* - admit. *) *)
(*   (* - admit.  *) *)
(*   (* - inversions Hred. *) *)
(* Admitted. *)
            

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
        { 
          rewrite~ subst_fresh_typ. 
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

Lemma app_hole_empty_hole: forall s,
    app_ec (e_hole s) (e_hole empty) (e_hole s).
Proof.
  intros. replace (app_ec (e_hole s) (e_hole empty) (e_hole s)) with (app_ec (e_hole s) (e_hole empty) (e_hole (s & empty))).
  - apply app_hole_hole. admit.
  - rewrite concat_empty_r. reflexivity.
Qed.

Lemma app_hole_empty_term: forall s t,
    app_ec (e_hole s) (e_term empty t) (e_term s t).
Proof.
  intros. 
  replace (e_term s t) with (e_term (s & empty) t).
  - apply app_hole_term. admit.
  - rewrite concat_empty_r. reflexivity.
Qed.

Lemma progress'': forall G e t T,
    ty_ec_trm G e t T ->
    (normal_form t \/ exists e' t', red_ec e t e' t').
Proof.
  intros. destruct e.
  {
    inversions H. rename H1 into Hwf. rename H2 into Hin. rename H4 into Ht.
    dependent induction Ht; try solve [left; auto].
    - admit.
    - admit.
    - right. exists (e_term s u) t.
      apply red_ec_hole_to_term.
      (* destruct t. *)
      (* + pose proof (var_typing_implies_avar_f Ht) as [x A]. subst. *)
      (*   exists (e_term s u) (trm_var (avar_f x)). *)
      (*   apply red_ec_hole_to_term. *)
      (* + pick_fresh x. *)
      (*   exists (e_term s u) (trm_val v). *)
      (*   apply red_ec_hole_to_term. *)
      (* + specialize (IHHt Hwf Hin) as [IH | [e' [t' Hred]]]. *)
      (*   * inversion IH. *)
      (*   * exists (e_term s u) (trm_sel a t). *)
      (*     apply red_ec_hole_to_term.  *)
      (* + specialize (IHHt Hwf Hin) as [IH | [e' [t' Hred]]]. *)
      (*   * inversion IH. *)
      (*   * exists (e_term s u) (trm_app a a0). *)
      (*     apply red_ec_hole_to_term.  *)
      (* + specialize (IHHt Hwf Hin) as [IH | [e' [t' Hred]]]. *)
      (*   * inversion IH. *)
      (*   * exists (e_term s u) (trm_let t1 t2). *)
      (*     apply red_ec_hole_to_term.  *)
    - specialize (IHHt Hwf Hin) as [IH | [t' [s' Hred]]].
      + left. assumption.
      + right. exists t' s'. assumption.
  }
  {
    inversions H. 
    rename H2 into Hwf. rename H3 into Hin. rename H5 into Ht. clear H8.
    dependent induction Ht; try solve [left; auto].
    - right. admit.
    - right. admit.
    - right. exists (e_term s (trm_let u t0)) t.
      eapply red_ec_let_let.
      (* destruct t. *)
      (* + pose proof (var_typing_implies_avar_f Ht) as [x A]. subst. *)
      (*   pose proof (app_hole_empty_term s t0). *)
      (*   pose proof (app_hole_empty_term s (trm_let u t0)). *)
      (*   exists (e_term s (trm_let u t0)) (trm_var (avar_f x)). *)
      (*   eapply (red_ec_term (red_ec_let_let (trm_var (avar_f x)) u t0) H1 H2). *)
      (* + pick_fresh x. *)
      (*   pose proof (app_hole_empty_term s t0). *)
      (*   pose proof (app_hole_empty_term s (trm_let u t0)). *)
      (*   exists (e_term s (trm_let u t0)) (trm_val v). *)
      (*   eapply (red_ec_term (red_ec_let_let (trm_val v) u t0) H1 H2). *)
      (* + specialize (IHHt Hwf Hin) as [IH | [e' [t' Hred]]]. *)
      (*   * inversion IH. *)
      (*   * exists (e_term s (trm_let u t0)) (trm_sel a t). *)
      (*     pose proof (app_hole_empty_term s t0). *)
      (*     pose proof (app_hole_empty_term s (trm_let u t0)). *)
      (*     apply (red_ec_term (red_ec_let_let (trm_sel a t) u t0) H1 H2). *)
      (* + specialize (IHHt Hwf Hin) as [IH | [e' [t' Hred]]]. *)
      (*   * inversion IH. *)
      (*   * exists (e_term s (trm_let u t0)) (trm_app a a0). *)
      (*     pose proof (app_hole_empty_term s t0). *)
      (*     pose proof (app_hole_empty_term s (trm_let u t0)). *)
      (*     eapply (red_ec_term (red_ec_let_let (trm_app a a0) u t0) H1 H2). *)
      (* + specialize (IHHt Hwf Hin) as [IH | [e' [t' Hred]]]. *)
      (*   * inversion IH. *)
      (*   * exists (e_term s (trm_let u t0)) (trm_let t1 t2). *)
      (*     pose proof (app_hole_empty_term s t0). *)
      (*     pose proof (app_hole_empty_term s (trm_let u t0)). *)
      (*     eapply (red_ec_term (red_ec_let_let (trm_let t1 t2) u t0) H1 H2). *)
    - specialize (IHHt Hwf Hin) as [IH | [t' [s' Hred]]].
      + left. assumption.
      + right. exists t' s'. assumption.
  }
Qed.


Lemma progress': forall G t e T,
    G ~~ (ec_sto e) ->
    inert G ->
    G |- t : T ->
    (normal_form t \/ exists e' t', red_ec e t e' t').
Proof.
  introv Hwf Hin Ht. dependent induction Ht; try solve [left; auto].
  - right. admit.
  - right. admit.
  - right. destruct t.
    + pose proof (var_typing_implies_avar_f Ht) as [x A]. subst.
      destruct e.
      {
        exists (e_term s u) (trm_var (avar_f x)).
        apply red_ec_hole_to_term.
      }
      {
        pose proof (app_hole_empty_term s t).
        pose proof (app_hole_empty_term s (trm_let u t)).
        exists (e_term s (trm_let u t)) (trm_var (avar_f x)).
        eapply (red_ec_term (red_ec_let_let (trm_var (avar_f x)) u t) H1 H2).
      } 
    + pick_fresh x.
      destruct e.
      {
        exists (e_term s u) (trm_val v).
        apply red_ec_hole_to_term.
      }
      {
        pose proof (app_hole_empty_term s t).
        pose proof (app_hole_empty_term s (trm_let u t)).
        exists (e_term s (trm_let u t)) (trm_val v).
        eapply (red_ec_term (red_ec_let_let (trm_val v) u t) H1 H2).
      }
    + specialize (IHHt Hwf Hin) as [IH | [e' [t' Hred]]].
      * inversion IH.
      * destruct e.
        { 
          exists (e_term s u) (trm_sel a t).
          apply red_ec_hole_to_term. 
        }
        {
          exists (e_term s (trm_let u t0)) (trm_sel a t).
          (* TODO: change to lemma *)
          pose proof (app_hole_empty_term s t0).
          pose proof (app_hole_empty_term s (trm_let u t0)).
          apply (red_ec_term (red_ec_let_let (trm_sel a t) u t0) H1 H2).
        } 
    + specialize (IHHt Hwf Hin) as [IH | [e' [t' Hred]]].
      * inversion IH.
      * destruct e.
        { 
          exists (e_term s u) (trm_app a a0).
          apply red_ec_hole_to_term. 
        }
        {
          exists (e_term s (trm_let u t)) (trm_app a a0).
          pose proof (app_hole_empty_term s t).
          pose proof (app_hole_empty_term s (trm_let u t)).
          eapply (red_ec_term (red_ec_let_let (trm_app a a0) u t) H1 H2).
        } 
    + specialize (IHHt Hwf Hin) as [IH | [e' [t' Hred]]].
      * inversion IH.
      * destruct e.
        {
          exists (e_term s u) (trm_let t1 t2).
          apply red_ec_hole_to_term. 
        }
        {
          exists (e_term s (trm_let u t)) (trm_let t1 t2).
          pose proof (app_hole_empty_term s t).
          pose proof (app_hole_empty_term s (trm_let u t)).
          eapply (red_ec_term (red_ec_let_let (trm_let t1 t2) u t) H1 H2).
        } 
  - specialize (IHHt Hwf Hin) as [IH | [t' [s' Hred]]].
    + left. assumption.
    + right. exists t' s'. assumption.
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
