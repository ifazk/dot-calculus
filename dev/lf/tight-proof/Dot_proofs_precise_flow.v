Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Dot_definitions.
Require Import Dot_proofs_wellformed_store.
Require Import Dot_proofs_some_lemmas.

Inductive precise_flow : var -> ctx -> typ -> typ -> Prop :=
  | pf_bind : forall x G T,
      binds x T G ->
      precise_flow x G T T
  | pf_open : forall x G T U,
      precise_flow x G T (typ_bnd U) ->
      precise_flow x G T (open_typ x U)
  | pf_and1 : forall x G T U1 U2,
      precise_flow x G T (typ_and U1 U2) ->
      precise_flow x G T U1
  | pf_and2 : forall x G T U1 U2,
      precise_flow x G T (typ_and U1 U2) ->
      precise_flow x G T U2
.

Hint Constructors precise_flow.

Lemma precise_flow_lemma : forall T U G x,
    binds x T G ->
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) U ->
      precise_flow x G T U.
Proof.
  introv Bis Htyp.
  dependent induction Htyp.
  - rewrite (binds_func H Bis).
    constructor. assumption.
  - assert (H : precise_flow x G T (typ_bnd T0)).
    { apply IHHtyp; auto. }
    auto.
  - rename H into H1.
    assert (H : precise_flow x G T T0).
    { apply IHHtyp; auto. }
    dependent induction H0.
    + apply IHsubtyp2; auto.
      * apply ty_sub with S; auto.
      * intros. rewrite <- H0.
        inversion H2.
        rewrite <- H4.
        apply IHsubtyp1; auto.
    + econstructor; eauto.
    + apply pf_and2 with T0; auto.
Qed.

Lemma precise_flow_lemma' : forall U G x,
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) U ->
    exists T, precise_flow x G T U.
Proof.
  introv H.
  pose proof (typing_implies_bound H) as [T H1].
  exists T. apply precise_flow_lemma; auto.
Qed.

Lemma precise_flow_implies_bound : forall T U G x,
    precise_flow x G T U ->
    binds x T G.
Proof.
  introv H. induction H; auto.
Qed.

Lemma precise_flow_lemma'' : forall U G x,
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) U ->
    exists T, binds x T G /\ precise_flow x G T U.
Proof.
  introv H.
  pose proof (precise_flow_lemma' H) as [T Hpf].
  pose proof (precise_flow_implies_bound Hpf) as Bis.
  exists T. auto.
Qed.

Lemma precise_flow_lemma_rev : forall T U G x,
    precise_flow x G T U ->
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) U.
Proof.
  introv H.
  pose proof (precise_flow_implies_bound H) as H1.
  induction H.
  - auto.
  - auto.
  - pose proof (IHprecise_flow H1) as H2.
    eapply ty_sub.
    + intros H3. exists x. reflexivity.
    + eauto.
    + eauto.
  - pose proof (IHprecise_flow H1) as H2.
    eapply ty_sub.
    + intros H3. exists x. reflexivity.
    + eauto.
    + eauto.
Qed.

Lemma ty_precise_var_and_inv1 : forall x G T U,
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_and T U) ->
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) T.
Proof.
  introv H.
  destruct (precise_flow_lemma' H) as [T' Hpf].
  apply pf_and1 in Hpf.
  apply (precise_flow_lemma_rev Hpf).
Qed.

Lemma ty_precise_var_and_inv2 : forall x G T U,
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_and T U) ->
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) U.
Proof.
  introv H.
  destruct (precise_flow_lemma' H) as [T' Hpf].
  apply pf_and2 in Hpf.
  apply (precise_flow_lemma_rev Hpf).
Qed.

Lemma precise_flow_all_inv : forall x G S T U,
    precise_flow x G (typ_all S T) U ->
    U = (typ_all S T).
Proof.
  introv Hpf.
  dependent induction Hpf.
  - reflexivity.
  - inversion IHHpf.
  - inversion IHHpf.
  - inversion IHHpf.
Qed.

Lemma precise_flow_bnd_inv'' : forall x G T,
    record_type T ->
    (forall U, precise_flow x G (typ_bnd T) U ->
          (exists U', U = (typ_bnd U') /\ record_type U') \/ record_type U).
Proof.
  introv [ls Hrt].
  induction Hrt. intros U.
  - intros Hpf.
    dependent induction Hpf.
    + left. exists (typ_rcd D).
      split.
      * reflexivity.
      * exists \{ label_of_dec D}.
        constructor; auto.
    + destruct (IHHpf H) as [[U' [IH1 IH2]] | [ls IH]].
      * inversion IH1. right.
        apply open_record_type. auto.
      * inversion IH.
    + destruct (IHHpf H) as [[U' [IH1 IH2]] | [ls IH]].
      * inversion IH1.
      * inversion IH. right. exists ls0. auto.
    + destruct (IHHpf H) as [[U' [IH1 IH2]] | [ls IH]].
      * inversion IH1.
      * inversion IH. right. exists \{ l}.
        constructor; auto.
  - intros U Hpf.
    dependent induction Hpf.
    + left. exists (typ_and T (typ_rcd D)).
      split.
      * reflexivity.
      * remember (label_of_dec D) as l.
        exists (union ls \{l}).
        apply rt_cons; auto.
    + specialize (IHHpf H1 H T Hrt IHHrt (eq_refl _)).
      destruct IHHpf as [[U' [IH1 IH2]] | [ls' IH]].
      * assert (H2 : U'=U).
        { inversion IH1; auto. }
        rewrite H2 in IH2.
        right. apply open_record_type.
        assumption.
      * inversion IH.
    + specialize (IHHpf H1 H T Hrt IHHrt (eq_refl _)).
      destruct IHHpf as [[U' [IH1 IH2]] | [ls' IH]].
      * inversion IH1.
      * right. inversion IH.
        exists ls0. apply H3.
    + specialize (IHHpf H1 H T Hrt IHHrt (eq_refl _)).
      destruct IHHpf as [[U' [IH1 IH2]] | [ls' IH]].
      * inversion IH1.
      * right. inversion IH.
        exists \{ l}. constructor; auto.
Qed.

Lemma precise_flow_bnd_inv' : forall x G T U,
    record_type T ->
    precise_flow x G (typ_bnd T) (typ_bnd U) ->
    record_type U.
Proof.
  introv Hrt Hpf.
  pose proof (precise_flow_bnd_inv'' Hrt Hpf) as Hbnd.
  destruct Hbnd as [[U' [IH1 IH2]] | [ls contra]]; try solve [inversion contra].
  - inversion IH1. subst; auto.
Qed.

Lemma precise_flow_bnd_inv : forall x G T U,
    record_type T ->
    precise_flow x G (typ_bnd T) (typ_bnd U) ->
    (T = U).
Proof.
  introv Hrt Hpf.
  pose proof (precise_flow_bnd_inv'' Hrt Hpf) as Hbnd.
  dependent induction Hpf.
  - reflexivity.
  - pose proof (precise_flow_bnd_inv' Hrt Hpf).
    pose proof (open_record_type x0 H) as H1.
    rewrite x in H1.
    destruct H1 as [ls H1].
    inversion H1.
  - pose proof (precise_flow_bnd_inv'' Hrt Hpf) as H.
    destruct H as [[U' [H1 H2]] | [ls H]].
    + inversion H1.
    + inversion H.
      inversion H2.
  - pose proof (precise_flow_bnd_inv'' Hrt Hpf) as H.
    destruct H as [[U' [H1 H2]] | [ls H]].
    + inversion H1.
    + inversion H.
Qed.

Lemma record_dec_precise_and_inv : forall x G D T,
    record_dec D ->
    precise_flow x G (typ_bnd (typ_rcd D)) T ->
    (forall T1 T2, T = (typ_and T1 T2) ->
              False).
Proof.
  introv Hrec.
  assert (H: record_type (typ_rcd D)).
  { exists \{ (label_of_dec D)}. constructor; auto. }
  introv Hpf.
  dependent induction Hpf.
  - introv Heq. inversion Heq.
  - pose proof (precise_flow_bnd_inv H Hpf) as H1.
    rewrite <- H1. introv Heq. inversion Heq.
  - specialize (IHHpf Hrec H). false.
  - specialize (IHHpf Hrec H). false.
Qed.

Lemma record_dec_precise_open : forall x G D1 D2,
    record_dec D1 ->
    precise_flow x G (typ_bnd (typ_rcd D1)) (typ_rcd D2) ->
    open_dec x D1 = D2.
Proof.
  introv Hrec Hpf.
  assert (H: record_type (typ_rcd D1)).
  { exists \{ (label_of_dec D1)}. constructor; auto. }
  dependent induction Hpf.
  - pose proof (precise_flow_bnd_inv H Hpf) as H1.
    rewrite <- H1 in x.
    unfold open_typ in x.
    simpl in x. inversion x.
    unfold open_dec. reflexivity.
  - pose proof (record_dec_precise_and_inv Hrec Hpf) as H1.
    false.
  - pose proof (record_dec_precise_and_inv Hrec Hpf) as H1.
    false.
Qed.

Lemma record_typ_sub_and_inv1 : forall T,
    record_type T ->
    (forall U1 U2, record_sub T (typ_and U1 U2) ->
           record_sub T U1).
Proof.
  intros T [ls Hrt].
  induction Hrt.
  - intros U1 U2 Hrsub.
    inversion Hrsub.
  - intros U1 U2 Hrsub.
    inversion Hrsub.
    + constructor. constructor.
    + apply IHHrt in H5.
      apply rs_drop. auto.
    + apply rs_drop. auto.
Qed.

Lemma record_typ_sub_and_inv2 : forall T,
    record_type T ->
    (forall U1 U2, record_sub T (typ_and U1 U2) ->
           record_sub T U2).
Proof.
  intros T [ls Hrt].
  induction Hrt.
  - intros U1 U2 Hrsub.
    inversion Hrsub.
  - intros U1 U2 Hrsub.
    inversion Hrsub.
    + econstructor. constructor.
    + apply IHHrt in H5.
      apply rs_drop. auto.
    + eapply rs_dropl. eauto.
Qed.

Lemma precise_flow_record_sub : forall x G T,
    record_type T ->
    (forall T', precise_flow x G (typ_bnd T) T' ->
           (T' = typ_bnd T) \/ record_sub (open_typ x T) T').
Proof.
  introv Hrt.
  introv Hpf.
  dependent induction Hpf.
  - left. reflexivity.
  - destruct (IHHpf Hrt) as [IH | IH].
    + inversion IH.
      right. constructor.
    + right. apply (precise_flow_bnd_inv Hrt) in Hpf.
      rewrite Hpf. constructor.
  - destruct (IHHpf Hrt) as [IH | IH].
    + inversion IH.
    + right. eapply record_typ_sub_and_inv1.
      * apply open_record_type. auto.
      * eauto.
  - destruct (IHHpf Hrt) as [IH | IH].
    + inversion IH.
    + right. eapply record_typ_sub_and_inv2.
      * apply open_record_type. auto.
      * eauto.
Qed.

Lemma record_unique_tight_bounds : forall G x T A,
    record_type T ->
    ( forall T1 T2,
        precise_flow x G (typ_bnd T) (typ_rcd (dec_typ A T1 T1)) ->
        precise_flow x G (typ_bnd T) (typ_rcd (dec_typ A T2 T2)) ->
        T1 = T2).
Proof.
  introv Hrt Hpf1 Hpf2.
  pose proof (precise_flow_record_sub Hrt Hpf1) as [H1 | H1].
  inversion H1.
  pose proof (precise_flow_record_sub Hrt Hpf2) as [H2 | H2].
  inversion H2.
  apply open_record_type with (x:=x) in Hrt.
  eapply (unique_rcd_typ Hrt); eauto.
Qed.
