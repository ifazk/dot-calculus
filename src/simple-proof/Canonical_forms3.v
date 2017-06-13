Set Implicit Arguments.

Require Import LibMap LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Some_lemmas.
Require Import Inert_types.
Require Import General_to_tight.
Require Import Invertible_typing.

(* Lemma sigma_binds_to_store_binds_raw: forall sto G S l T, *)
(*   G, S |~ sto -> *)
(*   binds l T S -> *)
(*   exists S1 S2, *)
(*     S = S1 & (l ~ T) & S2 /\ *)
(*     exists x, *)
(*       bindsM l (Some x) sto /\ *)
(*       G, S |- trm_var (avar_f x) : T. *)
(* Proof. *)
(*   introv Wt. generalize l T. induction Wt; introv Bi. *)
(*   + false* binds_empty_inv. *)
(*   + lets OkS: (wt_store_to_ok_S Wt). *)
(*     apply IHWt in Bi; clear IHWt. *)
(*     destruct Bi as [S1 [S2 [HS [v0 [HBi Hty]]]]]. *)
(*     exists S1 S2. *)
(*     split. assumption. *)
(*     lets Hdec: (classicT (l1 = l0)). destruct Hdec as [Hdec | Hdec]. *)
(*     - subst l1. exists x. split. *)
(*       * apply binds_update_eq. *)
(*       * assert (binds l0 T1 S) as Hbi. { *)
(*           subst S. apply binds_middle_eq. *)
(*           apply ok_middle_inv in OkS. destruct OkS as [_ Hl]. assumption. *)
(*         } *)
(*         subst S. apply binds_middle_eq_inv in H. *)
(*         subst. assumption. assumption. *)
(*     - exists v0. split. *)
(*       * apply binds_update_neq; assumption. *)
(*       * assumption. *)
(*   + lets OkS: (wt_store_to_ok_S Wt). *)
(*     lets Hdec: (classicT (l1 = l0)). destruct Hdec as [Hdec | Hdec]. *)
(*     - subst l1. exists S (@empty typ). *)
(*       apply binds_push_eq_inv in Bi. subst T1. *)
(*       split. *)
(*       rewrite concat_empty_r. reflexivity. *)
(*       exists x. split. *)
(*       * apply binds_update_eq. *)
(*       * apply weaken_ty_trm_sigma. *)
(*         assumption. *)
(*         constructor; assumption. *)
(*     - apply binds_push_neq_inv in Bi; try assumption. *)
(*       destruct (IHWt l1 T1 Bi) as [S1 [S2 [HS [v0 [HBiM Hty]]]]]. *)
(*       exists S1 (S2 & l0 ~ T0). split. *)
(*       subst S. rewrite concat_assoc. reflexivity. *)
(*       exists v0. split. *)
(*       apply binds_update_neq; assumption. *)
(*       apply weaken_ty_trm_sigma. assumption. constructor; assumption. *)
(*   + destruct (IHWt l0 T1 Bi) as [S1 [S2 [HS [v [HBi Hty]]]]]. *)
(*     exists S1 S2. split. *)
(*     assumption. *)
(*     exists v. split. assumption. apply weaken_ty_trm_ctx. *)
(*     assumption. constructor. apply wt_store_to_ok_G in Wt. assumption. assumption. *)
(* Qed. *)

(* Lemma sigma_binds_to_store_binds_typing: forall G S sto l T, *)
(*   G, S |~ sto -> *)
(*   binds l T S -> *)
(*   exists x, *)
(*     bindsM l (Some x) sto /\ *)
(*     G, S |- trm_var (avar_f x) : T. *)
(* Proof. *)
(*   introv Hwf Bi. *)
(*   lets A: (sigma_binds_to_store_binds_raw Hwf Bi). *)
(*   destruct A as [S1 [S2 [HeqG [x [Bis Hty]]]]]. *)
(*   exists x. split; eauto. *)
(* Qed. *)

Lemma ref_binds_typ: forall G S l T,
  G, S |-! trm_val (val_loc l) : typ_nref T ->
  binds l T S.
Proof.
  introv Hty.
  inversion Hty. assumption.
Qed.

Lemma loc_ref: forall G S v T,
    inert G ->
    G, S |-# (trm_val v) : typ_ref T ->
    False.
Proof.
  introv Hin H. pose proof (invertible_typing_lemma_v Hin H). dependent induction H0. inversions H0.
Qed.

Lemma binds_bindsM: forall G S sta sto l x T,
    inert G ->
    well_formed G S sta sto ->
    binds l T S ->
    bindsM l (Some x) sto ->
    G, S |- trm_var (avar_f x) : T.
Proof.
  introv Hin Hwf HS Hsto. induction Hwf.
  - false* binds_empty_inv.
  - pose proof (inert_ok Hin) as OkG. 
    assert (Hin': inert G). {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H2) as [_ [_ ?]]. subst. assumption.
    }
    apply* weaken_ty_trm_ctx. 
  - pose proof (inert_ok Hin) as OkG. 
    assert (Hin': inert G). {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H3) as [_ [_ ?]]. subst. assumption.
    }
    apply* weaken_ty_trm_ctx. 
  - destruct (classicT (l = l0)); subst.
    + apply binds_update_eq_inv in Hsto. inversion Hsto.
    + pose proof (binds_update_neq_inv Hsto n). 
      pose proof (binds_push_neq_inv HS n).
      apply* weaken_ty_trm_sigma. 
  - destruct (classicT (l = l0)); subst.
    + pose proof (binds_update_eq_inv Hsto) as Hsto'. inversions Hsto'.
      apply (binds_func HS) in H. subst*.
    + pose proof (binds_update_neq_inv Hsto n). apply* IHHwf.
Qed.

Lemma bindsM_empty: forall x l,
    bindsM l x emptyM -> False.
Proof.
  intros. unfold bindsM in H. 
  rewrite binds_def with (H:=(prove_Inhab None)) in H. destruct H.
  rewrite LibMap.dom_empty in H.
  rewrite in_empty_eq in H. false.
Qed.

Lemma test_bindsM: forall G S sta sto l x,
    inert G ->
    well_formed G S sta sto ->
    bindsM l x sto ->
    l # S ->
    False.
Proof.
  introv Hin Hwf Hb Hnotin. 
  induction Hwf.
  - false* bindsM_empty.
  - assert (inert G). {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H2) as [_ [_ ?]]. subst. assumption.
    }
    apply* IHHwf.
  - assert (inert G). {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H3) as [_ [_ ?]]. subst. assumption.
    }
    apply* IHHwf.
  - destruct (classicT (l = l0)).
    + subst. false (fresh_push_eq_inv Hnotin).
    + pose proof (binds_update_neq_inv Hb n).
      apply* IHHwf.
  - destruct (classicT (l = l0)).
    + subst. false (binds_fresh_inv H Hnotin).
    + pose proof (binds_update_neq_inv Hb n).
      apply* IHHwf.
Qed.

Lemma test_binds_l_notin_ref: forall G S sta sto l x T,
    inert G ->
    well_formed G S sta sto ->
    l # S ->
    binds x (typ_ref T) G ->
    binds x (val_loc l) sta ->
    False.
Proof.
  introv Hin Hwf Hnotin HG Hsta. dependent induction Hwf.
  - false* binds_empty_inv.
  - assert (Hin': inert G). {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H2) as [_ [_ ?]]. subst. assumption.
    }
    destruct (classicT (x = x0)).
    + subst. 
      apply binds_push_eq_inv in HG. subst. 
      apply binds_push_eq_inv in Hsta. subst.
      apply (general_to_tight_typing Hin') in H1. 
      false* loc_ref.
    + pose proof (binds_push_neq_inv HG n) as HG'.
      pose proof (binds_push_neq_inv Hsta n) as Hsta'.
      apply* IHHwf.
  - assert (Hin': inert G). {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H3) as [_ [_ ?]]. subst. assumption.
    }
    destruct (classicT (x = x0)).
    + subst. clear IHHwf.
      apply binds_push_eq_inv in HG. inversions HG. 
      apply binds_push_eq_inv in Hsta. inversions Hsta. 
      false (test_bindsM Hin' Hwf H1 Hnotin).
    + pose proof (binds_push_neq_inv HG n) as HG'.
      pose proof (binds_push_neq_inv Hsta n) as Hsta'.
      apply* IHHwf.
  - destruct (classicT (l = l0)).
    + subst. false (fresh_push_eq_inv Hnotin).
    + apply* IHHwf. 
  - destruct (classicT (l = l0)).
    + subst. false (binds_fresh_inv H Hnotin).
    + apply* IHHwf.
Qed.

Lemma test: forall G S sta sto x l T T',
    inert G ->
    well_formed G S sta sto ->
    binds x (typ_ref T) G ->
    binds l T' S ->
    binds x (val_loc l) sta ->
    exists y,
      bindsM l (Some y) sto /\
      G, S |- trm_var (avar_f y) : T'.
Proof.
  introv Hin Hwf HG HS Hsta. induction Hwf.
  - false* binds_empty_inv.
  - assert (Hin': inert G). {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H2) as [_ [_ ?]]. subst. assumption.
    }
    destruct (classicT (x = x0)).
    + subst. clear IHHwf. apply binds_push_eq_inv in HG. subst.
      apply (general_to_tight_typing Hin') in H1.
      false (loc_ref Hin' H1).
    + pose proof (binds_push_neq_inv HG n) as HG'.
      pose proof (binds_push_neq_inv Hsta n) as Hsta'.
      specialize (IHHwf Hin' HG' HS Hsta').
      destruct IHHwf as [y [Bi Ht]].
      exists y. split. 
      * assumption.
      * apply* weaken_ty_trm_ctx.
  - assert (Hin': inert G). {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H3) as [_ [_ ?]]. subst. assumption.
    }
    destruct (classicT (x = x0)).
    + subst. clear IHHwf.
      apply binds_push_eq_inv in HG. inversions HG. 
      apply binds_push_eq_inv in Hsta. inversions Hsta. 
      pose proof (binds_bindsM Hin' Hwf HS H1).
      exists y. split.
      * assumption.
      * apply* weaken_ty_trm_ctx.
    + pose proof (binds_push_neq_inv HG n) as HG'.
      pose proof (binds_push_neq_inv Hsta n) as Hsta'.
      specialize (IHHwf Hin' HG' HS Hsta').
      destruct IHHwf as [y' [Bi Ht]].
      exists y'. split. 
      * assumption.
      * apply* weaken_ty_trm_ctx.
  - destruct (classicT (l = l0)).
    + subst. apply binds_push_eq_inv in HS. subst. 
      false (test_binds_l_notin_ref Hin Hwf H HG Hsta).
    + pose proof (binds_push_neq_inv HS n) as HS'. 
      specialize (IHHwf Hin HG HS' Hsta).
      destruct IHHwf as [y [Bi Ht]]. exists y. split.
      * apply* binds_update_neq.
      * apply* weaken_ty_trm_sigma.
  - destruct (classicT (l = l0)).
    + subst. exists x0. split. 
      * apply binds_update_eq.
      * apply (binds_func HS) in H. subst. assumption.
    + specialize (IHHwf Hin HG HS Hsta).
      destruct IHHwf as [y [Bi Ht]]. exists y. split.
      * apply* binds_update_neq.
      * assumption.
Qed.

Lemma test_asdf: forall G S l T T',
    inert G ->
    G, S |- trm_val (val_loc l) : typ_nref T ->
    G, S |- trm_val (val_loc l) : typ_nref T' ->
    G, S |- T <: T' /\ G, S |- T' <: T.
Proof.
  introv Hin HT HT'. 
  apply (general_to_tight_typing Hin) in HT.
  apply (general_to_tight_typing Hin) in HT'.
  apply (invertible_typing_lemma_v Hin) in HT.
  apply (invertible_typing_lemma_v Hin) in HT'.
  dependent induction HT.
  - inversions H. dependent induction HT'.
    + inversions H. apply (binds_func H5) in H4. subst*.
    + pose proof (IHHT' T0 l Hin eq_refl eq_refl H4) as [Hs1 Hs2].
      apply (proj22 tight_to_general) in H.
      apply (proj22 tight_to_general) in H0.
      split; eapply subtyp_trans; eauto.      
  - pose proof (IHHT l T0 Hin eq_refl eq_refl HT') as [Hs1 Hs2].
    apply (proj22 tight_to_general) in H.
    apply (proj22 tight_to_general) in H0.
    split; eapply subtyp_trans; eauto.
Qed.  

Lemma test_invariant: forall G S sta sto x l T T',
    inert G ->
    well_formed G S sta sto ->
    binds x (typ_ref T) G ->
    binds l T' S ->
    binds x (val_loc l) sta ->
    G, S |- T <: T' /\ G, S |- T' <: T.
Proof.
  introv Hin Hwf HG HS Hsta. induction Hwf.
  - false* binds_empty_inv.
  - assert (Hin': inert G). {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H2) as [_ [_ ?]]. subst. assumption.
    }
    destruct (classicT (x = x0)).
    + subst. clear IHHwf. 
      apply binds_push_eq_inv in HG. subst.
      apply (general_to_tight_typing Hin') in H1.
      false (loc_ref Hin' H1).
    + pose proof (binds_push_neq_inv HG n) as HG'.
      pose proof (binds_push_neq_inv Hsta n) as Hsta'.
      specialize (IHHwf Hin' HG' HS Hsta'). destruct IHHwf as [Hs1 Hs2].
      split; apply* weaken_subtyp_ctx.
  - assert (Hin': inert G). {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H3) as [_ [_ ?]]. subst. assumption.
    }
    destruct (classicT (x = x0)).
    + subst. clear IHHwf.
      apply binds_push_eq_inv in HG. inversions HG. 
      apply binds_push_eq_inv in Hsta. inversions Hsta. 
      apply ty_loc with (G:=G) in HS.
      (* pose proof (binds_bindsM Hin' Hwf HS H1). *)
      pose proof (test_asdf Hin' H2 HS) as [Hs1 Hs2].
      split; apply* weaken_subtyp_ctx.
    + pose proof (binds_push_neq_inv HG n) as HG'.
      pose proof (binds_push_neq_inv Hsta n) as Hsta'.
      specialize (IHHwf Hin' HG' HS Hsta').
      destruct IHHwf as [Hs1 Hs2].
      split; apply* weaken_subtyp_ctx.
  - destruct (classicT (l = l0)).
    + subst. apply binds_push_eq_inv in HS. subst. 
      false (test_binds_l_notin_ref Hin Hwf H HG Hsta).
    + pose proof (binds_push_neq_inv HS n) as HS'. 
      specialize (IHHwf Hin HG HS' Hsta).
      destruct IHHwf as [Hs1 Hs2]. 
      split; apply* weaken_subtyp_sigma.
  - destruct (classicT (l = l0)).
    + apply* IHHwf.
    + specialize (IHHwf Hin HG HS Hsta).
      destruct IHHwf as [Hs1 Hs2].
      split*.
Qed.

Lemma canonical_forms_4: forall G S sta sto x T,
  inert G ->
  well_formed G S sta sto ->
  G, S |- trm_var (avar_f x) : typ_nref T ->
  (exists l,
      binds x (val_loc l) sta /\
      G, S |- trm_val (val_loc l) : typ_nref T /\
      bindsM l None sto) \/
  exists y, G, S |- trm_var (avar_f y) : typ_ref T.

Admitted.

Lemma canonical_forms_3: forall G S sta sto x T,
  inert G ->
  well_formed G S sta sto ->
  G, S |- trm_var (avar_f x) : typ_ref T ->
  exists l y,
    binds x (val_loc l) sta /\
    G, S |- trm_val (val_loc l) : typ_nref T /\
    bindsM l (Some y) sto /\
    G, S |- trm_var (avar_f y) : T.
Proof.
  introv Hin Hwf Hty.
  pose proof (typing_implies_bound Hty) as [V Bi].
  pose proof (general_to_tight_typing Hin Hty) as Hty'.
  pose proof (invertible_typing_lemma Hin Hty') as Hinv.
  pose proof (invertible_to_precise_typ_ref Hin Hinv) as [T' [Hx [Hs1 Hs2]]].
  pose proof (corresponding_types Hwf Hin Bi)
    as [[L [U [W [S1 [W1 [t [Hb [Ht [Heq _]]]]]]]]] | [[U [ds [Hb [Ht Heq]]]] | [U [U' [l [Hb [Ht [Heq [Hs1' Hs2']]]]]]]]].
  - assert (H: exists T, record_type T /\ V = (typ_bnd T)).
    { pose proof (binds_inert Bi Hin) as HinT.
      induction HinT.
      - destruct (precise_flow_lemma Hx) as [W' H].
        pose proof (pf_binds H). apply (binds_func Bi) in H0.
        apply pf_inert_ref_U in H. subst. inversion H0. assumption.
      - exists T0. auto.
      - inversion Heq. 
      - inversion Heq.
    }
    destruct H as [T0 [Hrt Hsubst]]; subst V; rename T0 into V.
    inversion Hsubst.
  - pose proof (binds_inert Bi Hin) as Hgt.
    induction Hgt.
    + inversion Heq.
    + pose proof (precise_flow_lemma Hx) as [W' H'].
      pose proof (pf_binds H'). apply (binds_func Bi) in H0.
      apply pf_inert_ref_U in H'. subst. inversion H0. assumption.
    + inversion Heq.
    + inversion Heq.
  - subst. 
    remember Ht as Ht'. inversions Ht'. 
    destruct Heq; subst.
    {
      pose proof (precise_flow_lemma Hx).
      destruct H as [V Hpf]. pose proof (pf_inert_ref_U Hin Hpf). subst.
      apply pf_binds in Hpf. apply (binds_func Hpf) in Bi. 
      inversion Bi.
    } 
    {
      pose proof (test Hin Hwf Bi H3 Hb) as [y [Biy Hy]].
      pose proof (inert_precise_ref_inv Hin Hx) as Bi'.
      pose proof (test_invariant Hin Hwf Bi' H3 Hb) as [Hs1'' Hs2''].
      apply (proj22 tight_to_general) in Hs1.
      apply (proj22 tight_to_general) in Hs2.
      pose proof (subtyp_trans Hs2'' Hs1) as HsTU.
      pose proof (subtyp_trans Hs2 Hs1'') as HsUT.
      exists l y. repeat split; try assumption.
      - apply precise_to_general in Ht.
        pose proof (subtyp_nref HsTU HsUT).
        apply (ty_sub Ht H).
      - apply (ty_sub Hy HsTU).
    }      
Qed.
