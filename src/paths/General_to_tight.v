Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Narrowing.
Require Import Inert_types.
Require Import Some_lemmas.
Require Import Tight_possible_types.

(* Lemma 2 *)
Lemma tight_subtyping_sel: forall G p A S U,
    inert G ->
    G |-# p \||/ ->
    G |-# trm_path p : typ_rcd { A >: S <: U } ->
    G |-# typ_path p A <: U /\
    G |-# S <: typ_path p A.
Proof.
  introv Hi Hn Hty.
  lets Hp: (tpt_lemma_typ Hty Hi Hn).
  pose proof (tpt_to_precise_typ_dec Hi Hn Hp) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_t in Ht. apply subtyp_trans_t with (T:=T); auto. assumption.
  - apply subtyp_sel2_t in Ht. apply subtyp_trans_t with (T:=T); auto. assumption.
Qed.

(* Theorem 1 *)
Lemma general_to_tight: forall G0, inert G0 ->
  (forall G t T,
     G |- t : T ->
     G = G0 ->
     G |-# t : T) /\
  (forall G S U,
     G |- S <: U ->
     G = G0 ->
     G |-# S <: U) /\
  (forall G p,
      norm G p ->
      G = G0 ->
      norm_t G p).
Proof.
  intros G0 HG.
  apply ts_mutind; intros; subst; try solve [eapply tight_subtyping_sel; auto]; eauto.
Qed.

Lemma general_to_tight_typing: forall G t T,
  inert G ->
  G |- t : T ->
  G |-# t : T.
Proof.
  intros. apply* general_to_tight.
Qed.
