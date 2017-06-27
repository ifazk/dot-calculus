Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inert_types.
Require Import Invertible_typing.

Lemma sel_replacement: forall G x A S U,
    inert G ->
    G |-# trm_var (avar_f x) : typ_rcd (dec_typ A S U) ->
    (G |-# typ_sel (avar_f x) A <: U /\
     G |-# S <: typ_sel (avar_f x) A).
Proof.
  introv HG Hty.
  pose proof (invertible_typing_lemma HG Hty) as Hinv.
  pose proof (invertible_to_precise_typ_dec HG Hinv) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_t in Ht. apply subtyp_trans_t with (T:=T); auto.
  - apply subtyp_sel2_t in Ht. apply subtyp_trans_t with (T:=T); auto.
Qed.

Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall G t T,
     G |- t : T ->
     G = G0 ->
     G |-# t : T) /\
  (forall G S U,
     G |- S <: U ->
     G = G0 ->
     G |-# S <: U).
Proof.
  intros G0 HG.
  apply ts_mutind; intros; subst; try solve [eapply sel_replacement; auto]; eauto.
Qed.

Lemma general_to_tight_typing: forall G t T,
  inert G ->
  G |- t : T ->
  G |-# t : T.
Proof.
  intros. apply* general_to_tight.
Qed.
