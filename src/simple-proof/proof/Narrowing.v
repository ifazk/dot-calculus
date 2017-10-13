(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import Weakening.
Require Import Coq.Program.Equality.


(** [G1] is a subenvironment of [G2], denoted [G1 subG G2],
     if for each [x] s.t. [G2(x)=T2],
    [G1(x) = T1] and [G1 ⊢ T1 <: T2]. *)
Reserved Notation "G1 ⪯ G2" (at level 35).
Inductive subenv: ctx -> ctx -> Prop :=
| subenv_empty : empty ⪯ empty
| subenv_grow: forall G G' x T T',
    G ⪯ G' ->
    ok (G & x ~ T) ->
    ok (G' & x ~ T') ->
    G ⊢ T <: T' ->
    G & x ~ T ⪯ G' & x ~ T'
where "G1 ⪯ G2" := (subenv G1 G2).
Hint Constructors subenv.

Lemma subenv_refl : forall G, ok G -> G ⪯ G.
Proof.
  intros G H. induction H; auto.
Qed.
Hint Resolve subenv_refl.


(** [G' subG G]              #<br>#
    [ok(G', x: T)]               #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G', x: T subG G, x: T]  #<br>#
    Note: [ok(G)] means that [G]'s domain consists of distinct variables.
    [ok] is defined in [TLC.LibEnv.v]. *)
Lemma subenv_push : forall G1 G2 x T,
    G1 ⪯ G2 ->
    ok (G1 & x ~ T) -> ok (G2 & x ~ T) ->
    (G1 & x ~ T) ⪯ (G2 & x ~ T).
Proof.
  intros. induction H; intros; auto.
Qed.
Hint Resolve subenv_push.


(** [G ⊢ S <: U]                      #<br>#
    [ok(G, x: S)] (see [subenv_push]) #<br>#
    [――――――――――――――――――――――――――――――――――]  #<br>#
    [G', x: T subG G, x: T] *)
Lemma subenv_last: forall G x S U,
  G ⊢ S <: U ->
  ok (G & x ~ S) ->
  (G & x ~ S) ⪯ (G & x ~ U).
Proof.
  intros.
  inversion H0;
  match goal with
  | [ H : empty = _ |- _ ] => destruct (empty_push_inv H2)
  | [ H : _ & _ ~ _ = _ & _ ~ _ |- _ ] =>
    apply eq_push_inv in H; destruct_all; subst
  end;
  constructor; auto.
Qed.
Hint Resolve subenv_last.


Lemma subenv_implies_ok : forall G1 G2,
    G1 ⪯ G2 -> ok G1 /\ ok G2.
Proof.
  intros. inversion H; split; auto.
Qed.


(** * Narrowing Lemma *)
(** The narrowing lemma states that typing is preserved under subenvironments.
    The lemma corresponds to Lemma 3.11 in the paper.
    The proof is by mutual induction on term typing, definition typing,
    and subtyping. *)

(** [G ⊢ t: T]                 #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ t: T]

    and

    [G ⊢ d: D]                 #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ d: D]

    and

    [G ⊢ ds :: T]              #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ ds :: T]

    and

    [G ⊢ S <: U]               #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ S <: U]              #<br>#

Note: for simplicity, the definition typing judgements and [ok] conditions
      are omitted from the paper formulation. *)
Lemma narrow_rules:
  (forall G t T, G ⊢ t : T -> forall G',
    G' ⪯ G ->
    G' ⊢ t : T)
/\ (forall G d D, G /- d : D -> forall G',
    G' ⪯ G ->
    G' /- d : D)
/\ (forall G ds T, G /- ds :: T -> forall G',
    G' ⪯ G ->
    G' /- ds :: T)
/\ (forall G S U, G ⊢ S <: U -> forall G',
    G' ⪯ G ->
    G' ⊢ S <: U).
Proof.
  apply rules_mutind; intros; eauto 4;
    try solve [
          match goal with
          | [ H : _ ⪯ _ |- _ ] => destruct (subenv_implies_ok H)
          end;
          fresh_constructor].
  
  Case "ty_var".
  induction H; auto;
  match goal with
  | [ H : binds _ _ (_ & _) |- _ ] =>
    apply binds_push_inv in H; destruct_all; subst
  end;
  [ eapply ty_sub; [eauto 2 | apply weaken_subtyp; trivial]
  | apply weaken_ty_trm; auto].
Qed.


(** The narrowing lemma, formulated only for term typing. *)
Lemma narrow_typing: forall G G' t T,
  G ⊢ t : T ->
  G' ⪯ G -> 
  G' ⊢ t : T.
Proof.
  intros. apply* narrow_rules.
Qed.

(** The narrowing lemma, formulated only for subtyping. *)
Lemma narrow_subtyping: forall G G' S U,
  G ⊢ S <: U ->
  G' ⪯ G -> 
  G' ⊢ S <: U.
Proof.
  intros. apply* narrow_rules.
Qed.


Lemma subenv_trans : forall G1 G2 G3,
    G1 ⪯ G2 ->
    G2 ⪯ G3 ->
    G1 ⪯ G3.
Proof.
  introv H. gen G3. induction H; intros; auto.
  dependent induction H3.
  - apply empty_push_inv in x. contradiction.
  - rename x into He. apply eq_push_inv in He. destruct_all.
    subst.
    apply IHsubenv in H3.
    constructor; auto.
    apply narrow_subtyping with (G':=G) in H6; auto.
    eapply subtyp_trans; eauto.
Qed.
Hint Resolve subenv_trans.
