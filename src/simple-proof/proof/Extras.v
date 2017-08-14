Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Precise_types.
Require Import Substitution.
Require Import Renaming.

(* Let rule reverse *)
Lemma trm_let_inv : forall G x T t v U,
  ok (G & x ~ T) ->
  x \notin fv_ctx_types G ->
  x \notin fv_typ T ->
  x \notin fv_typ U ->
  x \notin fv_trm t -> (* usually comes from ec_trm *)
  (G & x ~ T) |- (open_trm x t) : U ->
  (G |- (trm_val v) : T) ->
  G |- trm_let (trm_val v) t : U.
Proof.
  intros.
  apply_fresh ty_let as z; eauto.
  assert (Hfz: z # G & x ~ T) by auto.
  pose proof ((proj1 (renaming_gen x z)) _ _ _ H4 H Hfz).
  destruct (ok_push_inv H) as [HokG Hfx].
  rewrite <- (rename_push T z H0 H1 Hfx).
  assert (subst_typ x z U = U) by (apply subst_fresh_typ; auto).
  rewrite <- H7.
  assert (subst_trm x z (open_trm x t) = open_trm z t).
  { rewrite subst_open_commut_trm. unfold subst_fvar; cases_if; f_equal.
    apply (proj1 (subst_fresh_trm_val_def_defs x z)); auto. }
  rewrite <- H8.
  apply H6.
Qed.

(* Congruence Preversvation Reverse *)
Lemma rev_cong_preservation: forall G s x v t T U,
    ty_ec_trm (G & x ~ T) (e_hole (s & (x ~ v))) (open_trm x t) U -> (* G,x:T |- (s,x:v), [t^x] : U *)
    x \notin fv_ctx_types G ->
    x \notin fv_typ T ->
    x \notin fv_typ U ->
    x \notin fv_trm t ->
    ty_ec_trm G (e_term s t) (trm_val v) U (* G |- s, let [v] t : U *).
Proof.
  introv Htet. inversions Htet.
  inversion H0. exfalso; eapply empty_push_inv; eauto.
  inversion H1. exfalso; eapply empty_push_inv; eauto.
  destruct (eq_push_inv H) as [? [? ?]];
    destruct (eq_push_inv H6) as [? [? ?]];
    destruct (eq_push_inv H7) as [? [? ?]];
    subst; clear H H6 H7 H9 H18.
  assert (Hin: inert G).
  { inversion H1. exfalso; eapply empty_push_inv; eauto.
    destruct (eq_push_inv H) as [? [? ?]]; subst; clear H; auto. }
  intros. apply_fresh ty_e_term as z; auto.
  apply H11.
  pose proof (inert_ok H0) as HokGx.
  assert (Hfz: z # G & x ~ T) by auto.
  rewrite <- (rename_push T z H H6 H5).
  assert (HSU: subst_typ x z U = U) by (apply subst_fresh_typ; auto).
  rewrite <- HSU.
  assert (HSzt: subst_trm x z (open_trm x t) = open_trm z t).
  { rewrite subst_open_commut_trm. unfold subst_fvar; cases_if; f_equal.
    apply (proj1 (subst_fresh_trm_val_def_defs x z)); auto. }
  rewrite <- HSzt.
  apply renaming_gen; auto.
Qed.

Lemma rev_cong_preservation_trm: forall G s t u U,
    ty_ec_trm G (e_term s u) t U ->
    ty_ec_trm G (e_hole s) (trm_let t u) U.
Proof.
  introv H.
  inversion H; subst.
  apply ty_e_hole; auto.
  eapply ty_let; eauto.
Qed.
