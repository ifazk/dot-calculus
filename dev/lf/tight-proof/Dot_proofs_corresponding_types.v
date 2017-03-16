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
Require Import Dot_open_ind.
Require Import Dot_proofs_precise_flow.
Require Import Dot_proofs_good_types.
Require Import Dot_proofs_tight_possible_types.

(* ###################################################################### *)
(** ** Corresponding types *)

(* Lemma 1 *)
Lemma tight_to_precise_typ_dec: forall G s x A S U,
  wf_sto G s ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_rcd (dec_typ A S U)) ->
  exists T,
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_rcd (dec_typ A T T)) /\
    subtyp ty_general sub_tight G T U /\
    subtyp ty_general sub_tight G S T.
Proof.
  introv Hwf Ht.
  assert (good G) as HG by (apply* wf_good).
  lets Htp: (tight_possible_types_lemma HG Ht). clear Ht.
  dependent induction Htp.
  - lets Hp: (good_precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHtp Hwf HG). destruct IHHtp as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.
