Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inert_types.
Require Import Some_lemmas.
Require Import Narrowing.

(* ****************************************** *)
(* Invertable to precise *)

Lemma invertible_to_precise_typ_dec: forall G p A S U,
    inert G ->
    G |-# p \||/ ->
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

Lemma invertible_to_precise_trm_dec: forall G p a m T,
    inert G ->
    G |-# p \||/ ->
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

Lemma invertible_to_precise_typ_all: forall G p S T,
    inert G ->
    G |-# p \||/ ->
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
  introv Hi. induction Hi; eauto.
  - apply* precise_to_tight.
  - apply tight_to_general in IHHi. apply typing_implies_bound in IHHi. destruct IHHi. apply* ty_sngl_intro_t.
  - admit.
Qed.

Lemma invertible_sub_closure: forall G p T U,
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
    + admit.
  - admit.
  - admit.
Qed.

Lemma normalizing_to_invertible: forall G p T,
    inert G ->
    G |-#n p: T ->
    G |-## p: T.
Proof.
  introv Hi Ht.
  dependent induction p; eauto.
  * admit. (*should be easy*)
  *
    dependent induction Ht; eauto.
  -
      inversions H.
      remember IHp as IHp2. clear HeqIHp2.
      specialize (IHp2 _ Hi Ht).
      (* Could we use H2 and IHp2 here to deduce U=T, since there is no subtyping
         inside "typ_rcd {_ [strong] _}" ? *)
    (*specialize (IHHt _ _ IHp). inversions IHHt. (*this breaks*) admit.*)
    - inversions IHHt. apply ty_rec_elim_p in H.
        apply* ty_path_i. rewrite* <- open_var_path_typ_eq.
    - apply* invertible_sub_closure.
Qed.

Lemma tight_to_normalizing_var: forall G x T,
    inert G ->
    G |-# trm_path (p_var (avar_f x)) : T ->
    G |-#n p_var (avar_f x): T.
Proof.
  introv Hi Ht. dependent induction Ht; eauto.
Qed.

Lemma tight_to_normalizing: forall G p T,
    inert G ->
    G |-# trm_path p: T ->
    G |-# p \||/ ->
    G |-#n p: T.
Proof.
  introv Hi Hp Hn. gen T. induction p.
  - destruct a as [b | x]. inversion Hn. intros. apply* tight_to_normalizing_var.
  - introv Ht. assert (G |-# p \||/) as Hnp by inversion* Hn.
    specialize (IHp Hnp). dependent induction Ht; eauto.
    destruct p as [[b | x] | p].
    * inversion Hnp.
    * apply tight_to_normalizing_var in Ht; auto.
      inversion Hn; subst.
      specialize (IHp _ H1).
      specialize (normalizing_to_invertible Hi Ht). intro.
      specialize (normalizing_to_invertible Hi IHp). intro.
      destruct (invertible_to_precise_trm_dec Hi Hnp H) as [T' [mT [PrecT modeT]]].
      destruct (invertible_to_precise_trm_dec Hi Hnp H0) as [U' [mU [PrecU modeU]]].
      (* From PrecT and PrecU, can we now discover some useful relationship between T' and U'? *)
      (*this breaks*)
Qed.

Lemma invertible_lemma_var : forall G U x,
    inert G ->
    G |-# trm_path (p_var (avar_f x)) : U ->
    G |-## p_var (avar_f x) : U.
Proof.
  introv Hi Ht. dependent induction Ht; auto; try (specialize (IHHt _ Hi eq_refl)).
  - inversions IHHt; auto. rewrite* <- open_var_path_typ_eq.
  - apply* ty_sngl_i.
  - apply* invertible_sub_closure.
Qed.

Lemma invertible_lemma :
  (forall G t T, G |-# t: T -> forall p,
    t = trm_path p ->
    inert G ->
    norm_t G t ->
    G |-## p: T) /\
  (forall G t, norm_t G t ->
    inert G ->
    norm_p G t).
Proof.
  apply ts_mutind_t; intros; try (inversions H);
    try solve [inversion H0 || inversion H1]; eauto.
  - inversions H0. inversions H2. specialize (H _ eq_refl H1 H8).
    apply invertible_to_precise_trm_dec in H; auto. destruct H as [V [m [Hp [_ Hs]]]].
    apply invertible_lemma_var in H5; auto. apply invertible_to_precise_trm_dec in H5; auto.
    destruct H5 as [T' [m' [Hp' [Heq Hs']]]]. specialize (Heq eq_refl). destruct Heq. subst.
    lets Hu: (p_rcd_unique H1 Hp' Hp). destruct Hu. subst.
    apply ty_fld_elim_p in Hp'; auto. apply t_pt_precise in Hp'. apply* invertible_sub_closure.
    apply precise_to_general in Hp'. apply typing_implies_bound in Hp'. destruct Hp'.
    apply* norm_path_p.
  - inversions H1. specialize (H0 H2).
    assert (G |-# p \||/) as Hp by (inversion* n).
    specialize (H _ eq_refl H2 Hp).
    apply invertible_to_precise_trm_dec in H; auto.
    destruct H as [T' [m' [Ht [Heq  Hsx]]]]. specialize (Heq eq_refl). destruct Heq. subst.
    inversions H0.
    destruct (p_rcd_unique H2 Ht H5) as [_ Heq]. subst.
    apply ty_fld_elim_p in H5; auto. apply* norm_path_p.
  - inversions H0. specialize (H _ eq_refl H1 H2). apply* t_pt_bnd.
  - inversions H0. specialize (H _ eq_refl H1 H2). inversions H. auto.
    rewrite* <- open_var_path_typ_eq.
  - subst. specialize (H _ eq_refl H1 H2). apply* invertible_sub_closure.
  - subst. specialize (H _ eq_refl H1 n). apply invertible_to_precise_trm_dec in H; auto.
    destruct H as [V [m [Hp [Heq Hs]]]]. specialize (Heq eq_refl). destruct Heq. subst.
    apply* norm_path_p.
 Qed.

Lemma invertible_lemma_typ: forall G p T,
    G |-# trm_path p: T ->
    inert G ->
    G |-# p \||/ ->
    G |-## p: T.
Proof. intros. apply* invertible_lemma. Qed.

Lemma tight_possible_types_closure_tight_v: forall G v T U,
  inert G ->
  tight_pt_v G v T ->
  G |-# T <: U ->
  G |-##v v : U.
Proof.
  introv Hgd HT Hsub.
  dependent induction Hsub; eauto; inversions HT; try solve [inversion H]; try assumption.
  - inversions H1.
  - lets Hb: (inert_unique_tight_bounds Hgd H H6). subst*.
Qed.

Lemma tight_possible_types_lemma_v : forall G v T,
    inert G ->
    G |-# trm_val v : T ->
    G |-##v v : T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty _ Hgd eq_refl).
  apply* tight_possible_types_closure_tight_v.
Qed.
