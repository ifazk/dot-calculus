Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Some_lemmas.
Require Import Precise_flow.
Require Import Inert_types.
Require Import General_to_tight.

Lemma canonical_forms_3: forall G S sta sto x T,
  inert G ->
  wf_stack G S sta ->
  wt_store G S sto ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_ref T) ->
  exists l y,
    binds x (val_loc l) sta /\
    ty_trm ty_general sub_general G S (trm_val (val_loc l)) (typ_ref T) /\
    bindsM l y sto /\
    ty_trm ty_general sub_general G S (trm_var (avar_f y)) T.
Proof.
  Admitted.
(*   introv Hg Hwf Hwt Hty.  *)
(*   pose proof (typing_implies_bound Hty) as [V Bi]. *)
(*   (* pose proof (general_to_tight_typing Hg Hty) as Hty'. *) *)
(*   (* pose proof (tight_to_precise_trm_dec Hg Hty') as [T' [Hx Hs]]. *) *)
(*   pose proof (corresponding_types Hwf Hg Bi) *)
(*     as [[[L [U [W [S1 [W1 [t [Hb [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [U [ds [Hb [Ht Heq]]]]] | [U [l [Hb [Ht Heq]]]]]. *)
(*   - admit. *)
(*     (* assert (H: exists T, record_type T /\ V = (typ_bnd T)). *) *)
(*     (* { pose proof (inert_binds Hg Bi) as Hgt. *) *)
(*     (*   induction Hgt. *) *)
(*     (*   - pose proof (precise_flow_lemma Bi Hx) as H. *) *)
(*     (*     apply (precise_flow_all_inv) in H. *) *)
(*     (*     inversion H. *) *)
(*     (*   - exists T0. auto. *) *)
(*     (* } *) *)
(*     (* destruct H as [T0 [Hrt Hsubst]]; subst V; rename T0 into V. *) *)
(*     (* inversion Hsubst. *) *)
(*   - admit.  *)
(*   (* subst. *) *)
(*     (* exists U ds. *) *)
(*     (* pose proof (new_ty_defs Hwf Hg Hb) as Htd. *) *)
(*     (* pose proof (corresponding_types_ty_trms Hwf Hg Bi Hb Hx) as [t [H1 H2]]. *) *)
(*     (* exists t. *) *)
(*     (* split; auto. *) *)
(*     (* split; auto. *) *)
(*     (* apply tight_to_general in Hs; auto. *) *)
(*     (* apply ty_sub with (T:=T'); auto. *) *)
(*   - exists l x. subst. repeat split. *)
(*     + assumption. *)
(*     + admit. *)
(*     + unfold bindsM. simpl. *)
(*       assert (H: exists T, record_type T /\ V = (typ_bnd T)). *)
(*     { pose proof (inert_binds Hg Bi) as Hgt. *)
(*       induction Hgt. *)
(*       - (* pose proof (precise_flow_lemma Bi Hx) as H. *) *)
(*         apply (precise_flow_all_inv) in H. *)
(*         inversion H. *)
(*       - exists T0. auto. *)
(*     } *)
(*     destruct H as [T0 [Hrt Hsubst]]; subst V; rename T0 into V. *)
(*     inversion Hsubst. *)
(* Qed. *)
