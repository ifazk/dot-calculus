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
(** printing top    %\top%           #&#8868;#                     *)
(** printing bottom %\bot%           #&perp;#                      *)
(** printing <>     %\ne%            #&ne;#                        *)
(** printing notin  %\notin%         #&notin;#                     *)
(** printing isin   %\in%            #&isin;#                      *)
(** printing subG   %\prec:%         #&#8826;:#                    *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import Weakening.


(** [Gamma1] is a subenvironment of [Gamma2], denoted [Gamma1 subG Gamma2],
     if for each [x] s.t. [Gamma2(x)=T2],
    [Gamma1(x) = T1] and [Gamma1 |- T1 <: T2]. *)
Definition subenv(G1 G2: ctx) :=
  forall x T2, binds x T2 G2 ->
    binds x T2 G1 \/
    exists T1,
      binds x T1 G1 /\ G1 |- T1 <: T2.

(** [Gamma' subG Gamma]              #<br>#
    [ok(Gamma', x: T)]
    -----------------------
    [Gamma', x: T subG Gamma, x: T]  #<br>#
    Note: [ok(Gamma)] means that [Gamma]'s domain consists of distinct variables.
    [ok] is defined in [TLC.LibEnv.v]. *)
Lemma subenv_push: forall G G' x T,
  subenv G' G ->
  ok (G' & x ~ T) ->
  subenv (G' & x ~ T) (G & x ~ T).
Proof.
  intros.
  unfold subenv. intros xb Tb Bi. apply binds_push_inv in Bi.
  destruct Bi as [Bi | Bi].
  + destruct Bi as [Bi1 Bi2]. subst.
    left. eauto.
  + destruct Bi as [Bi1 Bi2].
    unfold subenv in H. specialize (H xb Tb Bi2). destruct H as [Bi' | Bi'].
    * left. eauto.
    * right. destruct Bi' as [T' [Bi1' Bi2']].
      exists T'. split. eauto. apply weaken_subtyp. assumption. eauto.
Qed.

(** [Gamma |- S <: U]              #<br>#
    [ok(Gamma, x: S)] (see [subenv_push])
    -----------------------
    [Gamma', x: T subG Gamma, x: T] *)
Lemma subenv_last: forall G x S U,
  G |- S <: U ->
  ok (G & x ~ S) ->
  subenv (G & x ~ S) (G & x ~ U).
Proof.
  intros. unfold subenv. intros y T Bi.
  apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
  - destruct Bi. subst. right. exists S. split; eauto using weaken_subtyp.
  - destruct Bi. left. eauto.
Qed.

(** * Narrowing Lemma *)
(** The narrowing lemma states that typing is preserved under subenvironments.
    The lemma corresponds to Lemma 3.11 in the paper.
    The proof is by mutual induction on term typing, definition typing,
    and subtyping. *)

(** [Gamma |- t: T]                 #<br>#
    [Gamma' subG Gamma]            #<br>#
    [ok Gamma']
    -------------------
    [Gamma' |- t: T]                #<br>#
    and                            #<br>#
    [Gamma |- d: D]                 #<br>#
    [Gamma' subG Gamma]            #<br>#
    [ok Gamma']
    -------------------
    [Gamma' |- d: D]                #<br>#
    and                            #<br>#
    [Gamma |- ds :: T]              #<br>#
    [Gamma' subG Gamma]            #<br>#
    [ok Gamma']
    -------------------
    [Gamma' |- ds :: T]             #<br>#
    and                            #<br>#
    [Gamma |- S <: U]               #<br>#
    [Gamma' subG Gamma]            #<br>#
    [ok Gamma']
    -------------------
    [Gamma' |- S <: U]              #<br>#

Note: for simplicity, the definition typing judgements and [ok] conditions
      are omitted from the paper formulation. *)
Lemma narrow_rules:
  (forall G t T, G |- t : T -> forall G',
    ok G' ->
    subenv G' G ->
    G' |- t : T)
/\ (forall G d D, G /- d : D -> forall G',
    ok G' ->
    subenv G' G ->
    G' /- d : D)
/\ (forall G ds T, G /- ds :: T -> forall G',
    ok G' ->
    subenv G' G ->
    G' /- ds :: T)
/\ (forall G S U, G |- S <: U -> forall G',
    ok G' ->
    subenv G' G ->
    G' |- S <: U).
Proof.
  apply rules_mutind; intros; eauto 4.
  - Case "ty_var".
    subst. unfold subenv in H0. specialize (H0 x T b).
    destruct H0.
    + eauto.
    + destruct H0 as [T' [Bi Hsub]].
      eapply ty_sub; eauto.
  - Case "ty_all_intro".
    subst.
    apply_fresh ty_all_intro as y; eauto using subenv_push.
  - Case "ty_new_intro".
    subst.
    apply_fresh ty_new_intro as y; eauto using subenv_push.
  - Case "ty_let".
    subst.
    apply_fresh ty_let as y; eauto using subenv_push.
  - Case "subtyp_all".
    subst.
    apply_fresh subtyp_all as y.
    + eauto.
    + assert (H5: ok (G' & y ~ S2)) by auto.
      eauto using subenv_push.
Qed.

(** The narrowing lemma, formulated only for term typing. *)
Lemma narrow_typing: forall G G' t T,
  G |- t : T ->
  subenv G' G -> ok G' ->
  G' |- t : T.
Proof.
  intros. apply* narrow_rules.
Qed.

(** The narrowing lemma, formulated only for subtyping. *)
Lemma narrow_subtyping: forall G G' S U,
  G |- S <: U ->
  subenv G' G -> ok G' ->
  G' |- S <: U.
Proof.
  intros. apply* narrow_rules.
Qed.
