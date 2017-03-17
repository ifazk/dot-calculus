Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Dot_definitions.
Require Import Dot_proofs_weakening.
Require Import Dot_proofs_wellformed_store.
Require Import Dot_proofs_substitution.
Require Import Dot_proofs_some_lemmas.
Require Import Dot_proofs_narrowing.
Require Import Dot_proofs_has_member.
Require Import Dot_proofs_tight_bound_completeness.
Require Import Dot_proofs_misc_inversions.

(*
Lemma (Canonical forms 1)
If G ~ s and G |- x: all(x: T)U then s(x) = lambda(x: T')t where G |- T <: T' and G, x: T |- t: U.
 *)
Lemma canonical_forms_1: forall G s x T U,
  wf_sto G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_all T U) ->
  (exists L T' t, binds x (val_lambda T' t) s /\ subtyp ty_general sub_general G T T' /\
  (forall y, y \notin L -> ty_trm ty_general sub_general (G & y ~ T) (open_trm y t) (open_typ y U))).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_sto_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  inversion Hp; subst.
  - lets Htype: (record_type_new Hwf Bis). rewrite H3 in Htype.
    destruct Htype as [ls Htyp]. inversion Htyp.
  - pick_fresh y. exists (dom G \u L). exists S0. exists t.
    split. apply Bis. split. assumption.
    intros y0 Fr0.
    eapply ty_sub.
    intros Contra. inversion Contra.
    eapply narrow_typing.
    eapply H1; eauto.
    apply subenv_last. apply H5.
    apply ok_push. eapply wf_sto_to_ok_G; eauto. eauto.
    apply ok_push. eapply wf_sto_to_ok_G; eauto. eauto.
    eapply H6; eauto.
Qed.

(*
Lemma (Canonical forms 2)

If G ~ s and G |- x: {a: T} then s(x) = new(x: S)d for some type S, definition d such that G |- d: S and d contains a definition {a = t} where G |- t: T.

*)
Lemma canonical_forms_2: forall G s x a T,
  wf_sto G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_rcd (dec_trm a T)) ->
  (exists S ds t, binds x (val_new S ds) s /\ ty_defs G (open_defs x ds) (open_typ x S) /\ defs_has (open_defs x ds) (def_trm a t) /\ ty_trm ty_general sub_general G t T).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_sto_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  apply pt_rcd_trm_inversion with (s:=s) in Hp; eauto.
  destruct Hp as [S' [ds [t' [Heq [Hdefs Htyd]]]]].
  subst.
  exists S' ds t'.
  split; try split; try split; try assumption.
  eapply new_ty_defs; eauto.
Qed.
