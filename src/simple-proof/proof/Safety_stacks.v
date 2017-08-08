Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Narrowing.
Require Import Helper_lemmas.
Require Import Precise_types.
Require Import Substitution.
Require Import Canonical_forms.
Require Import Safety.
Require Import Invertible_typing.
Require Import General_to_tight.

Reserved Notation "s1 '//' t1 '|->' s2 '//' t2" (at level 40, s2 at level 39).

Inductive sto_red : trm -> sto -> trm -> sto -> Prop :=
| red_sel : forall x m s t T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    s // trm_sel (avar_f x) m |-> s // t
| red_app : forall f a s T t,
    binds f (val_lambda T t) s ->
    s // trm_app (avar_f f) (avar_f a) |-> s // open_trm a t
| red_let : forall v t s x,
    x # s ->
    s // trm_let (trm_val v) t |-> s & x ~ v // open_trm x t
| red_let_var : forall t s x,
    s // trm_let (trm_var (avar_f x)) t |-> s // open_trm x t
| red_let_tgt : forall t0 t s t0' s',
    s // t0 |-> s' // t0' ->
    s // trm_let t0 t |-> s' // trm_let t0' t
where "s1 // t1 |-> s2 // t2" := (sto_red t1 s1 t2 s2).

Inductive sto_trm_typ : sto -> trm -> typ -> Prop :=
| sto_trm_typ_c : forall G s t T,
    inert G ->
    G ~~ s ->
    G |- t : T ->
    sto_trm_typ s t T.

Notation "'|-' s ',' t ':' T" := (sto_trm_typ s t T) (at level 40, t at level 59).

Inductive norm_form: trm -> Prop :=
| nf_var: forall x, norm_form (trm_var x)
| nf_val: forall v, norm_form (trm_val v).

Hint Constructors norm_form.

Lemma preservation: forall G s t s' t' T,
    G ~~ s ->
    inert G ->
    s // t |-> s' // t' ->
    G |- t : T ->
    exists G', inert G' /\
          G & G' ~~ s' /\
          G & G' |- t' : T.
Proof.
  introv Hwf Hin Hred Ht.
  gen t'.
  dependent induction Ht; intros; try solve [inversions Hred].
  - pose proof (canonical_forms_fun Hin Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    inversions Hred.
    apply (binds_func H4) in Bis. inversions Bis.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y); auto.
    rewrite subst_intro_trm with (x:=y); auto.
    eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ.
  - pose proof (canonical_forms_obj Hin Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
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
        { rewrite~ subst_fresh_typ.
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

Theorem preservation' : forall s s' t t' T,
    |- s, t : T ->
    s // t |-> s' // t' ->
    |- s', t' : T.
Proof.
  introv Ht Hr. destruct Ht as [* Hi Hwf Ht].
  lets Hp: (preservation Hwf Hi Hr Ht). destruct Hp as [G' [Hi' [Hwf' Ht']]].
  apply sto_trm_typ_c with (G:=G&G'); auto. admit.
Qed.

Lemma var_typing_implies_avar_f: forall G a T,
  G |- trm_var a : T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply IHty_trm; auto.
Qed.

Theorem progress: forall s t T,
    |- s, t : T ->
    norm_form t \/ exists s' t', s // t |-> s' // t'.
Proof.
  introv Ht. destruct Ht as [* Hin Hwf Ht].
  induction Ht; try solve [left; auto].
  - pose proof (canonical_forms_fun Hin Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    right. exists s (open_trm z t).
    eapply red_app; eauto.
  - pose proof (canonical_forms_obj Hin Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    right. exists s t.
    eapply red_sel; eauto.
  - right. destruct t.
    + pose proof (var_typing_implies_avar_f Ht) as [x A]. subst.
      exists s (open_trm x u). apply red_let_var.
    + pick_fresh x.
      exists (s & x ~ v) (open_trm x u).
      eapply red_let; auto.
    + specialize (IHHt Hin Hwf) as [IH | [s' [t' Hred]]].
      * inversion IH.
      * exists s' (trm_let t' u).
        apply~ red_let_tgt.
    + specialize (IHHt Hin Hwf) as [IH | [s' [t' Hred]]].
      * inversion IH.
      * exists s' (trm_let t' u).
        apply~ red_let_tgt.
    + specialize (IHHt Hin Hwf) as [IH | [s' [t' Hred]]].
      * inversion IH.
      * exists s' (trm_let t' u).
        apply~ red_let_tgt.
  - specialize (IHHt Hin Hwf) as [IH | [s' [t' Hred]]].
    + left. assumption.
    + right. exists s' t'. assumption.
Qed.
