Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions Weakening Narrowing Binding PreciseTypes Substitution CanonicalForms
        RecordAndInertTypes InvertibleTypes GeneralToTight.

Reserved Notation "s1 '//' t1 '|->' s2 '//' t2" (at level 40, s2 at level 39).

Inductive ec_red : trm -> ec -> trm -> ec -> Prop :=
| red_sel : forall x m e t T ds,
    binds x (val_new T ds) e ->
    defs_has (open_defs x ds) (def_trm m t) ->
    e // trm_sel (avar_f x) m |-> e // t
| red_app : forall f a e T t,
    binds f (val_lambda T t) e ->
    e // trm_app (avar_f f) (avar_f a) |-> e // open_trm a t
| red_let : forall v t s x,
    x # s ->
    s // trm_let (trm_val v) t |-> s & x ~ v // open_trm x t
| red_let_var : forall t e x,
    e // trm_let (trm_var (avar_f x)) t |-> e // open_trm x t
| red_let_tgt : forall t0 t e t0' e',
    e // t0 |-> e' // t0' ->
    e // trm_let t0 t |-> e' // trm_let t0' t
where "e1 // t1 |-> e2 // t2" := (ec_red t1 e1 t2 e2).

Inductive sto_trm_typ : ec -> trm -> typ -> Prop :=
| sto_trm_typ_c : forall G e t T,
    inert G ->
    well_typed G e ->
    G ⊢ t : T ->
    sto_trm_typ e t T.

Notation "'⊢' e ',' t ':' T" := (sto_trm_typ e t T) (at level 40, t at level 59).

Inductive norm_form: trm -> Prop :=
| nf_var: forall x, norm_form (trm_var x)
| nf_val: forall v, norm_form (trm_val v).

Hint Constructors norm_form.

(** If a value [v] has type [T], then [v] has a precise type [T']
    that is a subtype of [T].
    This lemma corresponds to Lemma 3.15 in the paper. *)
Lemma val_typing: forall G v T,
  G ⊢ trm_val v : T ->
  exists T', G ⊢! trm_val v : T' /\
        G ⊢ T' <: T.
Proof.
  intros G v T H. dependent induction H; eauto.
  destruct (IHty_trm _ eq_refl) as [T' [Hty Hsub]]. eauto.
Qed.

Lemma preservation_ty: forall G e t e' t' T,
    well_typed G e ->
    inert G ->
    e // t |-> e' // t' ->
    G ⊢ t : T ->
    exists G', inert G' /\
          well_typed (G & G') e' /\
          G & G' ⊢ t' : T.
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
      pose proof (well_typed_notin_dom Hwf H6).
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

Theorem preservation : forall e e' t t' T,
    ⊢ e, t : T ->
    e // t |-> e' // t' ->
    ⊢ e', t' : T.
Proof.
  introv Ht Hr. destruct Ht as [* Hi Hwf Ht].
  lets Hp: (preservation_ty Hwf Hi Hr Ht). destruct Hp as [G' [Hi' [Hwf' Ht']]].
  apply sto_trm_typ_c with (G:=G&G'); auto. apply* inert_concat.
Qed.

Theorem progress: forall e t T,
    ⊢ e, t : T ->
    norm_form t \/ exists e' t', e // t |-> e' // t'.
Proof.
  introv Ht. destruct Ht as [* Hin Hwf Ht].
  induction Ht; try solve [left; auto].
  - pose proof (canonical_forms_fun Hin Hwf Ht1) as [L [T' [t [Bis [Hsub Hty]]]]].
    right. exists e (open_trm z t).
    eapply red_app; eauto.
  - pose proof (canonical_forms_obj Hin Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    right. exists e t.
    eapply red_sel; eauto.
  - right. destruct t.
    + pose proof (var_typing_implies_avar_f Ht) as [x A]. subst.
      exists e (open_trm x u). apply red_let_var.
    + pick_fresh x.
      exists (e & x ~ v) (open_trm x u).
      eapply red_let; auto.
    + specialize (IHHt Hin Hwf) as [IH | [e' [t' Hred]]].
      * inversion IH.
      * exists e' (trm_let t' u).
        apply~ red_let_tgt.
    + specialize (IHHt Hin Hwf) as [IH | [e' [t' Hred]]].
      * inversion IH.
      * exists e' (trm_let t' u).
        apply~ red_let_tgt.
    + specialize (IHHt Hin Hwf) as [IH | [e' [t' Hred]]].
      * inversion IH.
      * exists e' (trm_let t' u).
        apply~ red_let_tgt.
  - specialize (IHHt Hin Hwf) as [IH | [e' [t' Hred]]].
    + left. assumption.
    + right. exists e' t'. assumption.
Qed.
