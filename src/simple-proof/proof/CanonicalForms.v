(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module proves the Canonical Forms Lemmas, which allow us
    to retrieve the shape of a value given its type. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN LibExtra.
Require Import Definitions RecordAndInertTypes PreciseTyping TightTyping InvertibleTyping
        GeneralToTight Subenvironments Weakening Narrowing Substitution StronglyTypedStores.

(** * Simple Implications of Typing *)

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma typing_implies_bound: forall G x T,
  G ⊢ trm_var (avar_f x) : T ->
  exists S, binds x S G.
Proof.
  introv Ht. dependent induction Ht; eauto.
Qed.

(** * Functions under Inert Contexts *)
(** This lemma corresponds to Lemma 3.7 ([forall] to [G(x)]) in the paper.

    [inert G]            #<br>#
    [G ⊢ x: forall(T)U]       #<br>#
    [――――――――――――――-]    #<br>#
    [exists T', U',]          #<br>#
    [G(x) = forall(T')U']     #<br>#
    [G ⊢ T <: T']        #<br>#
    [forall fresh y, G, y: T ⊢ U'^y <: U^y] *)
Lemma var_typ_all_to_binds: forall G x T U,
    inert G ->
    G ⊢ trm_var (avar_f x) : typ_all T U ->
    (exists L T' U',
        binds x (typ_all T' U') G /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_all (inert_ok Hin) Hinv) as [T' [U' [V' [L [Htp [Hs1 Hs2]]]]]].
  exists L T' U'. repeat split.
  - apply* inert_precise_all_inv.
  - apply~ tight_to_general.
  - assumption.
Qed.

(** This lemma corresponds to Lemma 3.8 ([forall] to [lambda]) in the paper.

    [inert G]                       #<br>#
    [G ⊢ v: forall(T)U]                  #<br>#
    [――――――――――――]                  #<br>#
    [exists T', t,]                       #<br>#
    [v = lambda(T')t]              #<br>#
    [G ⊢ T <: T']                   #<br>#
    [forall fresh y, G, y: T ⊢ t^y: U^y] *)
Lemma val_typ_all_to_lambda: forall G v x t T U,
    inert G ->
    trm_val x v t ->
    G ⊢ t : typ_all T U ->
    (exists L T' t',
        v = val_fun T' t' /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_trm y t') : open_typ y U)).
Proof.
  introv Hin Htv Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible_forall Hin Htv Htt).
  destruct (invertible_val_to_precise_lambda Hin Hinv) as [L [T' [U' [Htp [Hs1 Hs2]]]]].
  inversions Htp.
  exists (L0 \u L \u (dom G)) T' t0. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H3 y HL0).
  eapply ty_sub; eauto. eapply narrow_typing in H3; eauto.
Qed.

(** * Objects under Inert Contexts *)
(** This lemma corresponds to Lemma 3.9 ([mu] to [G(x)]) in the paper.

    [inert G]                    #<br>#
    [G ⊢ x: {a: T}]              #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [exists S, T', G(x) = mu(S)]       #<br>#
    [S^x = ... /\ {a: T'} /\ ...]  #<br>#
    [G ⊢ T' <: T]                *)
Lemma var_typ_rcd_to_binds: forall G x a T U,
    inert G ->
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T U) ->
    (exists S T',
        binds x (typ_bnd S) G /\
        record_has (open_typ x S) (dec_trm a T' T') /\
        G ⊢ T <: T' /\
        G ⊢ T' <: U).
Proof.
  introv Hin Ht.
  destruct (typing_implies_bound Ht) as [S BiG].
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_trm_dec Hinv) as [S' [T' [U' [Htp [Hs1 Hs2]]]]].
  destruct (pf_dec_trm_inv Hin Htp).
  destruct (pf_inert_rcd_U Hin Htp) as [?U' Hr]. subst.
  lets Hr': (precise_flow_record_has Hin Htp). apply pf_binds in Htp.
  exists U'0 S'. repeat_split_right; try assumption; apply* tight_to_general.
Qed.

(** This lemma corresponds to Lemma 3.10 ([mu] to [nu]) in the paper.

    [inert G]                  #<br>#
    [G ⊢ v: mu(T)]             #<br>#
    [G ⊢ x: T^x]               #<br>#
    [T = ... /\ {a: U} /\ ...  ] #<br>#
    [――――――――――――――――――――――――] #<br>#
    [exists t, ds, v = nu(T)ds     ] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: U] *)
Lemma val_mu_to_new: forall G v t S T U a x,
    inert G ->
    x # G ->
    trm_val x v t ->
    G ⊢ t: typ_bnd T ->
    G ⊢ trm_var (avar_f x) : open_typ x T ->
    record_has (open_typ x T) (dec_trm a S U) ->
    exists t' ds,
      v = val_obj T ds /\
      defs_has ds (def_trm a t') /\
      G ⊢ t': U.
Proof.
  introv Hi HxG Htv Ht Hx Hr.
  lets Htt: (general_to_tight_typing Hi Ht).
  lets Hinv: (tight_to_invertible_v Hi HxG Htv Htt).
  inversions Hinv. inversions H.
  pick_fresh z. assert (z \notin L) as Hz by auto.
  specialize (H1 z Hz).
  assert (Hds: G /- open_defs x ds :: open_typ x T)
    by (destruct_notin; eapply renaming_def; eauto).
  destruct (record_has_ty_defs Hds Hr) as [d [Hh Hd]]. inversions Hd.
  exists t0 (open_defs x ds). split*.
Qed.

Lemma strong_mu_to_new: forall G s x T,
    inert G ->
    ty_val_s G s x ->
    binds x (typ_bnd T) G ->
    exists ds, binds x (val_obj T (open_defs x ds)) s /\
               G /- open_defs x ds :: open_typ x T.
Proof.
  introv Hi Hts Bi.
  inversions Hts.
  - pose proof (binds_functional Bi H); subst T0; clear H.
    pose proof (general_to_tight_typing Hi H1).
    pose proof (tight_to_invertible_fun Hi (trm_val_fun x _ _) H).
    inversions H2. inversions H3.
  - pose proof (binds_functional Bi H). inversions H1.
    exists ds; split; auto.
Qed.

(** * Canonical Forms for Functions

    [inert G]            #<br>#
    [s: G]               #<br>#
    [G ⊢ x: forall(T)U]       #<br>#
    [――――――――――――――――――] #<br>#
    [s(x) = lambda(T')t] #<br>#
    [G ⊢ T <: T']        #<br>#
    [G, x: T ⊢ t: U]          *)
Lemma canonical_forms_fun: forall G s x T U,
  inert G ->
  strongly_typed G s ->
  G ⊢ trm_var (avar_f x) : typ_all T U ->
  (exists L T' t, binds x (val_fun T' t) s /\ G ⊢ T <: T' /\
  (forall y, y \notin L -> G & y ~ T ⊢ open_trm y t : open_typ y U)).
Proof.
  introv Hin Hst Hty.
  destruct (var_typ_all_to_binds Hin Hty) as [L [S [T' [BiG [Hs1 Hs2]]]]].
  pose proof (corresponding_types Hst BiG).
  inversions H.
  - pose proof (binds_functional BiG H0). subst T0.
    destruct (val_typ_all_to_lambda Hin (trm_val_fun x _ _) H2)
      as [L' [S' [t' [Heq [Hs1' Hs2']]]]].
    exists (L \u L' \u (dom G)) S' t'. inversions Heq.
    repeat_split_right; eauto.
    intros.
    assert (HL: y \notin L) by auto.
    assert (HL': y \notin L') by auto.
    specialize (Hs2 y HL).
    specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    eapply ty_sub; eauto.
  - pose proof (binds_functional BiG H0). congruence.
Qed.

(** * Canonical Forms for Objects

    [inert G]            #<br>#
    [s: G]               #<br>#
    [G ⊢ x: {a:T}]       #<br>#
    [――――――――――――――――――] #<br>#
    [exists S, ds, t,] #<br>#
    [s(x) = nu(S)ds] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: T] *)
Lemma canonical_forms_obj: forall G s x a S T,
  inert G ->
  strongly_typed G s ->
  G ⊢ trm_var (avar_f x) : (typ_rcd (dec_trm a S T)) ->
  (exists S ds t, binds x (val_obj S (open_defs x ds)) s /\
                  defs_has (open_defs x ds) (def_trm a t) /\
                  G ⊢ t : T).
Proof.
  introv Hi Hst Hty.
  destruct (var_typ_rcd_to_binds Hi Hty) as [?S [?T' [?H [?H [?H ?H]]]]].
  pose proof (corresponding_types Hst H) as Hts.
  destruct (strong_mu_to_new Hi Hts H) as [?ds [?Bis ?]].
  pose proof (record_has_ty_defs H3 H0) as [?d [? ?]].
  inversions H5.
  exists S0 ds t. repeat_split_right; eauto.
Qed.

(** * Store updates *)
Lemma inert_dec_sub : forall G x a S T,
    inert G ->
    G ⊢ trm_var (avar_f x) : (typ_rcd (dec_trm a S T)) ->
    G ⊢ S <: T.
Proof.
  introv Hin Hty.
  pose proof (var_typ_rcd_to_binds Hin Hty) as [?S [?T [_ [_ [?H ?H]]]]].
  eapply subtyp_trans; eauto.
Qed.

Require Import StoreUpdate.

Lemma def_update_typing: forall G a t y S T,
    G /- def_trm a t : dec_trm a T T ->
    G ⊢ S <: T ->
    G ⊢ trm_var (avar_f y) : S ->
    G /- def_trm a (trm_var (avar_f y)) : dec_trm a T T.
Proof.
  eauto.
Qed.

Lemma defs_update_hasnt: forall ds a x ds' l,
    defs_update ds a x ds' ->
    defs_hasnt ds l ->
    defs_hasnt ds' l.
Proof.
  introv H; gen l; induction H; intros.
  - unfold defs_hasnt; simpl.
    inversion H; cases_if.
    auto.
  - unfold defs_hasnt; simpl.
    assert (label_of_def d <> l).
    { inversion H0. cases_if. auto. }
    cases_if.
    assert (defs_hasnt ds l).
    { inversion H0. cases_if. auto. }
    apply IHdefs_update; auto.
Qed.

Lemma defs_update_hasnt_inv: forall ds a x ds',
    defs_update ds a x ds' ->
    defs_hasnt ds (label_trm a) -> False.
Proof.
  introv H. induction H; intros.
  - inversion H; cases_if; congruence.
  - assert (defs_hasnt ds (label_trm a)).
    { inversion H0; cases_if. }
    auto.
Qed.

Lemma defs_update_hasnt_inv_update: forall ds a x ds',
    defs_update ds a x ds' ->
    defs_hasnt ds' (label_trm a) -> False.
Proof.
  introv H. induction H; intros.
  - inversion H; cases_if; congruence.
  - assert (defs_hasnt ds' (label_trm a)).
    { inversion H0; cases_if. }
    auto.
Qed.

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
