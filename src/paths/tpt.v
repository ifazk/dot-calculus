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
  - inversions H.
Qed.

Lemma tpt_to_precise_trm_dec: forall G p a m T,
    inert G ->
    norm_t G p ->
    G |-## p : typ_rcd { a [m] T } ->
    exists T' m',
      G |-! trm_path p : typ_rcd { a [m'] T' } /\
      (m = strong -> m' = strong) /\
      G |-# T' <: T.
Proof.
  introv Hi Hn Ht. dependent induction Ht.
  - (* t_pt_precise *)
    exists T m. auto.
  - (* t_pt_dec_trm *)
    specialize (IHHt _ _ _ Hi Hn eq_refl). destruct IHHt as [V [m [Hp [Eq Hs]]]].
    exists V m. split*.
  - (* t_pt_dec_trm_strong *)
    specialize (IHHt _ _ _ Hi Hn eq_refl). destruct IHHt as [V [m [Hp [Eq Hs]]]].
    specialize (Eq eq_refl). subst.
    exists V strong. split*.
  - inversions H.
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
  - admit.
Qed.

Lemma invertable_to_tight: forall G p T,
    G |-## p : T ->
    norm_t G p ->
    G |-# trm_path p : T.
Proof.
  introv Hi Hn. induction Hi; eauto.
  apply* precise_to_tight.
  inversions Hn. specialize (IHHi H5). apply ty_fld_elim_path_t in IHHi; auto.
Qed.

Lemma tight_possible_types_closure_tight: forall G p T U,
  inert G ->
  G |-## p : T ->
  G |-# T <: U ->
  G |-## p : U.
Proof.
  introv Hi HT Hsub.
  dependent induction Hsub; eauto.
  - inversions HT. false* precise_bot_false. inversions H0.
  - inversion* HT. inversions H0.
  - inversion* HT. inversions H0.
  - inversions HT.
    + false *precise_psel_false.
    + pose proof (inert_unique_tight_bounds Hi H H6). subst. assumption.
    + inversions H2.
Qed.

Lemma tight_possible_types_lemma : forall G U p,
    inert G ->
    G |-# trm_path p : U ->
    norm_t G p ->
    G |-## p : U.
Proof.
  introv Hi Hty Hn. gen U.
  induction p; introv Ht.
  - dependent induction Ht; auto. specialize (IHHt _ Hi Hn eq_refl).
    inversions IHHt. apply ty_rec_elim_p in H. apply* t_pt_precise.
    rewrite <- open_var_path_typ_eq. assumption.
    specialize (IHHt _ Hi Hn eq_refl). apply* tight_possible_types_closure_tight.
  -

    inversions Hn. specialize (IHp H4).
    lets Hp1: (IHp _ H1); clear H1. apply tpt_to_precise_trm_dec in Hp1; auto.
    destruct Hp1 as [T [m [Hp [Heq Hs]]]]. specialize (Heq eq_refl). subst.
    inversions Ht.
    * (* ty_fld_elim_var_t *)
specialize (IHp _ H5). apply tpt_to_precise_trm_dec in IHp; auto.
      destruct IHp as [T' [m' [Hp' [_ Hs']]]]. destruct (p_rcd_unique Hi Hp Hp') as [Hm HT].
      subst. apply ty_fld_elim_p in Hp. apply t_pt_precise in Hp.
      apply* tight_possible_types_closure_tight.
      apply precise_to_general in Hp. destruct (typing_implies_bound Hp). apply* norm_var_p.
      admit.
    * (* ty_fld_elim_path_t *)
    * (* ty_rec_elim_t *)
    * (* ty_and_intro_t *)
    * (* ty_sub_t *)

Lemma tight_possible_types_lemma_var : forall G U x,
    inert G ->
    G |-# trm_path (p_var (avar_f x)) : U ->
    G |-## p_var (avar_f x) : U.
Proof. Admitted.

Lemma tight_possible_types_lemma_paths: forall G p a U,
    inert G ->
    norm_t G (p_sel p a) ->
    G |-# trm_path (p_sel p a) : U ->
    exists T, G |-## p : typ_rcd { a [strong] T } /\ G |-# T <: U.
Proof.
  introv Hi Hn Ht. dependent induction Ht.
  - (* ty_fld_elim_var_t *)
    inversions Hn. apply tight_possible_types_lemma_var in H1; auto.
    apply tight_possible_types_lemma_var in Ht; auto.
    destruct (tpt_to_precise_trm_dec Hi H4 Ht) as [T' [m [Hpx [_ Hsx]]]].
    destruct (tpt_to_precise_trm_dec Hi H4 H1) as [U' [m' [Hpx' [Heq Hsx']]]].
    specialize (Heq eq_refl). subst. lets Hu: (p_rcd_unique Hi Hpx Hpx').
    destruct Hu; subst. exists U'; split*.
  - (* ty_fld_elim_path_t *)
    destruct p as [v | p]. destruct v.
    * inversions Hn. inversions H5.
    * lets Htl: (tight_possible_types_lemma_var Hi Ht). exists* T.
    * specialize (IHHt _ _ Hi H eq_refl). destruct IHHt as [U [Tpt Hs]].
      apply t_pt_bnd in Tpt.
      apply t_pt_fld_elim in Tpt


      apply tpt_to_precise_trm_dec in Tpt; auto.
      destruct Tpt as [T' [m' [Hp [Heq  Hsx]]]]. specialize (Heq eq_refl). subst.




Lemma tight_possible_types_lemma : forall G U p,
    inert G ->
    G |-# trm_path p : U ->
    norm_t G p ->
    G |-## p : U.
Proof.
  introv Hi Hty Hn. gen U.
  induction p; introv Ht.
  - admit.
  - inversions Hn. specialize (IHp H4).
    lets Hp1: (IHp _ H1); clear H1. apply tpt_to_precise_trm_dec in Hp1; auto.
    destruct Hp1 as [T [m [Hp [Heq Hs]]]]. specialize (Heq eq_refl). subst.
    inversions Ht.
    * (* ty_fld_elim_var_t *)
specialize (IHp _ H5). apply tpt_to_precise_trm_dec in IHp; auto.
      destruct IHp as [T' [m' [Hp' [_ Hs']]]]. destruct (p_rcd_unique Hi Hp Hp') as [Hm HT].
      subst. apply ty_fld_elim_p in Hp. apply t_pt_precise in Hp.
      apply* tight_possible_types_closure_tight.
      apply precise_to_general in Hp. destruct (typing_implies_bound Hp). apply* norm_var_p.
      admit.
    * (* ty_fld_elim_path_t *)
    * (* ty_rec_elim_t *)
    * (* ty_and_intro_t *)
    * (* ty_sub_t *)

  dependent induction Hty; auto.
  - (* ty_fld_elim_var_t *)
    inversions Hn.
    specialize (IHHty (p_var (avar_f x )) Hi eq_refl H4).
    destruct (tpt_to_precise_trm_dec Hi H4 IHHty) as [V [m [Hp [_ Hs]]]].
admit.
  - specialize (IHHty p0  Hi eq_refl H). inversions IHHty.
    * apply ty_fld_elim_p in H0; auto.
    specialize (IHHty _ Hgd eq_refl eq_refl eq_refl).
    eapply t_pt_bnd.
    apply IHHty.
    reflexivity.
  - specialize (IHHty _ Hgd eq_refl eq_refl eq_refl).
    inversion IHHty; subst; auto.
  - apply t_pt_and; auto.
  - eapply tight_possible_types_closure_tight; auto.
Qed.
