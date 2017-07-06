(** printing |-     %\vdash%         #&vdash;#                     *)
(** printing /-     %\vdash%         #&vdash;#                     *)
(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** printing ->     %\rightarrow%    #&rarr;#                      *)
(** printing =>     %\Rightarrow%    #&rArr;#                      *)
(** printing ~~     %\~%             #~#                           *)
(** printing /\     %\wedge%         #&and;#                       *)
(** printing \/     %\vee%           #&or;#                        *)
(** printing forall %\forall%        #&forall;#                    *)
(** printing exists %\exists%        #&exist;#                     *)
(** printing lambda %\lambda%        #&lambda;#                    *)
(** printing mu     %\mu%            #&mu;#                        *)
(** printing nu     %\nu%            #&nu;#                        *)
(** printing Gamma  %\Gamma%         #&Gamma;#                     *)
(** printing Gamma' %\Gamma'%        #&Gamma;'#                    *)
(** printing Gamma1 %\Gamma_1%       #&Gamma;<sub>1</sub>#         *)
(** printing Gamma2 %\Gamma_2%       #&Gamma;<sub>2</sub>#         *)
(** printing Gamma3 %\Gamma_3%       #&Gamma;<sub>3</sub>#         *)
(** printing top    %\top%           #&#8868;#                     *)
(** printing bottom %\bot%           #&perp;#                      *)
(** printing <>     %\ne%            #&ne;#                        *)
(** printing notin  %\notin%         #&notin;#                     *)
(** printing isin   %\in%            #&isin;#                      *)
(** printing subG   %\prec:%         #&#8826;:#                    *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Precise_types.
Require Import Invertible_typing.

(** * Sel-<: Premise
    This lemma corresponds to Lemma 3.5 in the paper. *)

(** [inert Gamma]                    #<br># *)
(** [Gamma |-## x: {A: S..U}]               *)
(** ------------------------------          *)
(** [exists T. Gamma |-## x: {A: T..T}]   #<br># *)
(** [Gamma |-# T <: U]               #<br># *)
(** [Gamma |-# S <: T]                      *)
Lemma sel_premise: forall G x A S U,
  inert G ->
  G |-## x : typ_rcd (dec_typ A S U) ->
  exists T,
    G |-! trm_var (avar_f x) : typ_rcd (dec_typ A T T) /\
    G |-# T <: U /\
    G |-# S <: T.
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - lets Hp: (precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHinv A T U0 HG eq_refl).
    destruct IHHinv as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.

(** * Sel-<: Replacement *)
(** This lemma corresponds to Lemma 3.4 in the paper. *)

(** [inert Gamma]              #<br># *)
(** [Gamma |-# x: {A: S..U}]          *)
(** ------------------------          *)
(** [Gamma |-# x.A <: U]       #<br># *)
(** [Gamma |-# S <: x.A]            # *)
Lemma sel_replacement: forall G x A S U,
    inert G ->
    G |-# trm_var (avar_f x) : typ_rcd (dec_typ A S U) ->
    (G |-# typ_sel (avar_f x) A <: U /\
     G |-# S <: typ_sel (avar_f x) A).
Proof.
  introv HG Hty.
  pose proof (tight_to_invertible HG Hty) as Hinv.
  pose proof (sel_premise HG Hinv) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_t in Ht. apply subtyp_trans_t with (T:=T); auto.
  - apply subtyp_sel2_t in Ht. apply subtyp_trans_t with (T:=T); auto.
Qed.

(** * General to Tight [|- to |-#] *)
(** The following lemma corresponds to Theorem 3.3 in the paper.
    It says that in an inert environment, general typing ([ty_trm] [|-]) can
    be reduced to tight typing ([ty_trm_t] [|-#]).
    The proof is by mutual induction on the typing and subtyping judgements. *)

(** [inert Gamma]       #<br># *)
(** [Gamma |- t: T]             *)
(** ----------------           *)
(** [Gamma |-# t: T]    #<br># *)
(** and                 #<br># *)
(** [inert Gamma]       #<br># *)
(** [Gamma |- S <: U]           *)
(** ------------------         *)
(** [Gamma |-# S <: U]         *)
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

(** The general-to-tight lemma, formulated for term typing.
    This lemma corresponds to Theorem 3.3 in the paper. *)
Lemma general_to_tight_typing: forall G t T,
  inert G ->
  G |- t : T ->
  G |-# t : T.
Proof.
  intros. apply* general_to_tight.
Qed.
