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

Lemma loc_typing_invariant: forall G S l T T',
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

Lemma wf_ref_invariant: forall G S sta sto x l T T',
    inert G ->
    G, S |~ sta, sto ->
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
      false (inert_loc_ref Hin' H1).
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
      pose proof (loc_typing_invariant Hin' H2 HS) as [Hs1 Hs2].
      split; apply* weaken_subtyp_ctx.
    + pose proof (binds_push_neq_inv HG n) as HG'.
      pose proof (binds_push_neq_inv Hsta n) as Hsta'.
      specialize (IHHwf Hin' HG' HS Hsta').
      destruct IHHwf as [Hs1 Hs2].
      split; apply* weaken_subtyp_ctx.
  - destruct (classicT (l = l0)).
    + subst. apply binds_push_eq_inv in HS. subst. 
      false (wf_binds_ref_notin Hin Hwf H HG Hsta).
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

Lemma canonical_forms_3: forall G S sta sto x T,
  inert G ->
  G, S |~ sta, sto ->
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
      pose proof (wf_binds_sto_Some Hin Hwf Bi H3 Hb) as [y [Biy Hy]].
      pose proof (inert_precise_ref_inv Hin Hx) as Bi'.
      pose proof (wf_ref_invariant Hin Hwf Bi' H3 Hb) as [Hs1'' Hs2''].
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
