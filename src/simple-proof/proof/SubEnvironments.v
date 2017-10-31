(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import Coq.Program.Equality.

(** * Subenvironments [G1 ⪯ G2] *)
(** [G1 @@ S] is a subenvironment of [G2 @@ S], denoted [G1 @@ S ⪯ G2],
    if [dom(G1) = dom(G2)] and for each [x],
    [G1 @@ S ⊢ G1(x) <: G2(x)]. *)
Reserved Notation "G1 '@@' S ⪯ G2" (at level 40).

Inductive subenv: ctx -> sigma -> ctx -> Prop :=
| subenv_empty : forall S, empty @@ S ⪯ empty
| subenv_grow: forall G G' S x T T',
    G @@ S ⪯ G' ->
    ok (G & x ~ T) ->
    ok (G' & x ~ T') ->
    G @@ S ⊢ T <: T' ->
    G & x ~ T @@ S ⪯ G' & x ~ T'
where "G1 '@@' S ⪯ G2" := (subenv G1 S G2).

Hint Constructors subenv.

(** If [ok G], then [G ⪯ G].
    Note: [ok(G)] means that [G]'s domain consists of distinct variables.
    [ok] is defined in [TLC.LibEnv.v] *)
Lemma subenv_refl : forall G S, ok G -> G @@ S ⪯ G.
Proof.
  introv H. induction H; auto.
Qed.
Hint Resolve subenv_refl.

(** [G' subG G]                  #<br>#
    [ok(G', x: T)]               #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G', x: T subG G, x: T]  #<br># *)
Lemma subenv_push : forall G1 G2 S x T,
    G1 @@ S ⪯ G2 ->
    ok (G1 & x ~ T) -> ok (G2 & x ~ T) ->
    (G1 & x ~ T) @@ S ⪯ (G2 & x ~ T).
Proof.
  intros. induction H; intros; auto.
Qed.
Hint Resolve subenv_push.


(** [G ⊢ S <: U]                      #<br>#
    [ok(G, x: S)] (see [subenv_push]) #<br>#
    [――――――――――――――――――――――――――――――――――]  #<br>#
    [G', x: T subG G, x: T] *)
Lemma subenv_last: forall G S x T U,
  G @@ S ⊢ T <: U ->
  ok (G & x ~ T) ->
  (G & x ~ T) @@ S ⪯ (G & x ~ U).
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


Lemma subenv_implies_ok : forall G1 S G2,
    G1 @@ S ⪯ G2 -> ok G1 /\ ok G2.
Proof.
  intros. inversion H; split; auto.
Qed.
