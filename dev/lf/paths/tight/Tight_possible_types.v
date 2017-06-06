Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inert_types.
Require Import Some_lemmas.
Require Import Narrowing.

(* ****************************************** *)
(* Invertable to precise *)

Lemma tpt_to_precise_typ_dec: forall G p A S U,
    inert G ->
    norm_t G p ->
    G |-## p : typ_rcd { A >: S <: U } ->
    exists T,
      G |-! trm_path p : typ_rcd { A >: T <: T } /\
      G |-# T <: U /\
      G |-# S <: T.
Proof.
  introv HG Hn Ht.
  dependent induction Ht.
  - lets Hp: (precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHt A T U0 HG Hn eq_refl). destruct IHHt as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.

Lemma tpt_to_precise_trm_dec: forall G p a m T,
    inert G ->
    norm_t G p ->
    G |-## p : typ_rcd { a [m] T } ->
    exists T' m',
      G |-! trm_path p : typ_rcd { a [m'] T' } /\
      (m = strong -> m' = strong /\ T = T') /\
      G |-# T' <: T.
Proof.
  introv Hi Hn Ht. dependent induction Ht.
  - (* t_pt_precise *)
    exists T m. auto.
  - (* t_pt_dec_trm *)
    specialize (IHHt _ _ _ Hi Hn eq_refl). destruct IHHt as [V [m [Hp [Eq Hs]]]].
    exists V m. split*. split. intros F. inversion F. apply* subtyp_trans_t.
  - (* t_pt_dec_trm_strong *)
    specialize (IHHt _ _ _ Hi Hn eq_refl). destruct IHHt as [V [m [Hp [Eq Hs]]]].
    specialize (Eq eq_refl). destruct Eq as [Eq1 Eq2]. subst.
    exists V strong. split*.
Qed.

Lemma tpt_to_precise_typ_all: forall G p S T,
    inert G ->
    norm_t G p ->
    G |-## p : typ_all S T ->
    exists S' T' L,
      G |-! trm_path p : typ_all S' T' /\
      G |-# S <: S' /\
      (forall y,
          y \notin L ->
              G & y ~ S |- T' ||^ y <: T ||^ y).
Proof.
  introv Hi Hn Ht. dependent induction Ht.
  - exists S T (dom G); auto.
  - specialize (IHHt _ _ Hi Hn eq_refl).
    destruct IHHt as [S' [T' [L' [Hpt [HSsub HTsub]]]]].
    exists S' T' (dom G \u L \u L').
    split; auto.
    assert (Hsub2 : G |-# typ_all S0 T0 <: typ_all S T) by (apply* subtyp_all_t). split.
    + eapply subtyp_trans_t; eauto.
    + intros y Fr.
      assert (Hok: ok (G & y ~ S)) by auto using ok_push, inert_ok.
      apply tight_to_general in H; auto.
      assert (Hnarrow: G & y ~ S |- T' ||^ y <: T0 ||^ y).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.

Lemma invertable_to_tight: forall G p T,
    G |-## p : T ->
    G |-# trm_path p : T.
Proof.
  introv Hi. induction Hi; eauto. apply* precise_to_tight.
Qed.

Lemma tpt_sub_closure: forall G p T U,
  inert G ->
  G |-## p : T ->
  G |-# T <: U ->
  G |-## p : U.
Proof.
  introv Hi HT Hsub.
  dependent induction Hsub; eauto.
  - inversions HT. false* precise_bot_false.
  - inversion* HT.
  - inversion* HT.
  - inversions HT.
    + false *precise_psel_false.
    + pose proof (inert_unique_tight_bounds Hi H H6). subst. assumption.
Qed.

Lemma tpt_lemma :
  (forall G t T, G |-# t: T -> forall p,
    t = trm_path p ->
    inert G ->
    norm_t G p ->
    G |-## p: T) /\
  (forall G p, norm_t G p ->
    inert G ->
    norm_p G p).
Proof.
  apply ts_mutind_t; intros; try (inversions H);  eauto.
  - admit.
  - inversions H0. specialize (H _ eq_refl H1). admit.
  - inversions H1. specialize (H0 H2). specialize (H _ eq_refl H2 n).
    apply tpt_to_precise_trm_dec in H; auto.
    destruct H as [T' [m' [Hp [Heq  Hsx]]]]. specialize (Heq eq_refl). subst.
    assert (norm_p G (p_sel p a)) as Hnp by admit. inversions Hnp. Abort.


Lemma tpt_lemma_var : forall G U x,
    inert G ->
    G |-# trm_path (p_var (avar_f x)) : U ->
    G |-## p_var (avar_f x) : U.
Proof.
  introv Hi Ht. dependent induction Ht; auto; specialize (IHHt _ Hi eq_refl).
  - inversions IHHt; auto. rewrite* <- open_var_path_typ_eq.
  - apply* tpt_sub_closure.
Qed.

Lemma tpt_lemma_paths:
  (forall G t T, G |-# t: T -> forall p a,
    t = trm_path (p_sel p a) ->
    inert G ->
    norm_t G (p_sel p a) ->
    exists U U',
      G |-## p: typ_rcd {a [strong] U } /\
      inert_typ U /\
      precise_flow (p_sel p a) G U U' /\
      G |-# U' <: T) /\
  (forall G p, norm_t G p ->
    inert G ->
    norm_p G p).
Proof.
  apply ts_mutind_t; intros; try solve [inversion H]; eauto.
  - inversions H1.
  - inversions H0. apply (tpt_lemma_var H1) in t.
    admit.
  - inversions H1. destruct p0 as [x | q]. destruct x as [b | x].
    * inversions n.
    * apply (tpt_lemma_var H2) in t.
      destruct (tpt_to_precise_trm_dec H2 n t) as [U [m [Hp [Heq Hs]]]].
      specialize (Heq eq_refl). destruct Heq as [Eq1 Eq2]. subst. clear H Hs.
      specialize (H0 H2). inversions H0. lets Hb: (binds_inert H4 H2).
      destruct (precise_flow_lemma Hp) as [V Pf].
      apply pf_fld in Pf; auto.
      exists U U. split*. split. admit. split*.
      apply* norm_var_p. admit. Abort.

Lemma tight_possible_types_lemma_paths: forall G p a U,
    inert G ->
    norm_t G (p_sel p a) ->
    G |-# trm_path (p_sel p a) : U ->
    exists T, G |-## p : typ_rcd { a [strong] T } /\ G |-# T <: U.
Proof.
  introv Hi Hn Ht. dependent induction Ht.
  - (* ty_fld_elim_var_t *)
    inversions Hn. apply tpt_lemma_var in H1; auto.
    apply tpt_lemma_var in Ht; auto.
    destruct (tpt_to_precise_trm_dec Hi H4 Ht) as [T' [m [Hpx [_ Hsx]]]].
    destruct (tpt_to_precise_trm_dec Hi H4 H1) as [U' [m' [Hpx' [Heq Hsx']]]].
    specialize (Heq eq_refl). destruct Heq. subst. lets Hu: (p_rcd_unique Hi Hpx Hpx').
    destruct Hu; subst. exists U'; split*.
  - (* ty_fld_elim_path_t *)
    destruct p as [v | p]. destruct v.
    * inversions Hn. inversions H5.
    * lets Htl: (tpt_lemma_var Hi Ht). exists* T.
    * specialize (IHHt _ _ Hi H eq_refl). destruct IHHt as [U [Tpt Hs]].
      apply tpt_to_precise_trm_dec in Tpt; auto.
      destruct Tpt as [T' [m' [Hp [Heq  Hsx]]]]. specialize (Heq eq_refl). subst.
Abort.

Lemma tight_possible_types_lemma_paths: forall G p a U,
    inert G ->
    norm_t G (p_sel p a) ->
    G |-# trm_path (p_sel p a) : U ->
    exists T, G |-! trm_path p : typ_rcd { a [strong] T } /\ G |-# T <: U.
Proof.
  introv Hi Hn Ht. dependent induction Ht.
  - inversions Hn. apply tpt_lemma_var in H1; auto.
    apply tpt_lemma_var in Ht; auto.
    destruct (tpt_to_precise_trm_dec Hi H4 Ht) as [T' [m [Hpx [_ Hsx]]]].
    destruct (tpt_to_precise_trm_dec Hi H4 H1) as [U' [m' [Hpx' [Heq Hsx']]]].
    specialize (Heq eq_refl). subst. lets Hu: (p_rcd_unique Hi Hpx Hpx').
    destruct Hu; subst. exists U'; split*.
  Abort.
