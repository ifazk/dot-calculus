(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import RecordAndInertTypes.
Require Import PreciseTypes.
Require Import TightTypes.
Require Import InvertibleTypes.

(** * Sel-<: Premise
    This lemma corresponds to Lemma 3.5 in the paper.

    [inert G]                    #<br>#
    [G @@ S ⊢## x: {A: S..U}]        #<br>#
    [――――――――――――――――――――――――――――]   #<br>#
    [exists T. G @@ S ⊢## x: {A: T..T}]   #<br>#
    [G @@ S ⊢# T <: U]               #<br>#
    [G @@ S ⊢# S <: T]                    *)
Lemma sel_premise: forall G S x A U V,
  inert G ->
  G @@ S ⊢## x : typ_rcd (dec_typ A U V) ->
  exists T,
    G @@ S ⊢! trm_var (avar_f x) : typ_rcd (dec_typ A T T) /\
    G @@ S ⊢# T <: V /\
    G @@ S ⊢# U <: T.
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - lets Hp: (precise_dec_typ_inv HG H). subst.
    exists; split*.
  - specialize (IHHinv A T U0 HG eq_refl).
    destruct IHHinv as [? [Hx [Hs1 Hs2]]].
    exists; split*.
Qed.

(** * Sel-<: Replacement
    This lemma corresponds to Lemma 3.4 in the paper.

    [inert G]              #<br>#
    [G @@ S ⊢# x: {A: S..U}]   #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G @@ S ⊢# x.A <: U]       #<br>#
    [G @@ S ⊢# S <: x.A]            *)
Lemma sel_replacement: forall G S x A T U,
    inert G ->
    G @@ S ⊢# trm_var (avar_f x) : typ_rcd (dec_typ A T U) ->
    (G @@ S ⊢# typ_sel (avar_f x) A <: U /\
     G @@ S ⊢# T <: typ_sel (avar_f x) A).
Proof.
  introv HG Hty.
  pose proof (tight_to_invertible HG Hty) as Hinv.
  pose proof (sel_premise HG Hinv) as [? [Ht [Hs1 Hs2]]].
  split; eauto using subtyp_trans_t, subtyp_sel1_t, subtyp_sel2_t.
Qed.

(** * General to Tight [⊢ to @@ S ⊢#] *)
(** The following lemma corresponds to Theorem 3.3 in the paper.
    It says that in an inert environment, general typing ([ty_trm] [⊢]) can
    be reduced to tight typing ([ty_trm_t] [⊢#]).
    The proof is by mutual induction on the typing and subtyping judgements.

    [inert G]           #<br>#
    [G @@ S ⊢ t: T]          #<br>#
    [――――――――――――――]    #<br>#
    [G @@ S ⊢# t: T] #<br># #<br>#

    and                 #<br># #<br>#
    [inert G]           #<br>#
    [G @@ S ⊢ S <: U]        #<br>#
    [――――――――――――――――]  #<br>#
    [G @@ S ⊢# S <: U]         *)
Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall G S t T,
     G @@ S ⊢ t : T ->
     G = G0 ->
     G @@ S ⊢# t : T) /\
  (forall G S T U,
     G @@ S ⊢ T <: U ->
     G = G0 ->
     G @@ S ⊢# T <: U).
Proof.
  intros G0 HG.
  apply ts_mutind; intros; subst; try solve [eapply sel_replacement; auto]; eauto.
Qed.

(** The general-to-tight lemma, formulated for term typing. *)
Lemma general_to_tight_typing: forall G S t T,
  inert G ->
  G @@ S ⊢ t : T ->
  G @@ S ⊢# t : T.
Proof.
  intros. apply* general_to_tight.
Qed.
