(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import Coq.Program.Equality.

(** * Equivenvironments [G1 ⪯ G2] *)
(** [G1] is a equivenvironment of [G2], denoted [G1 ⪯ G2],
    if [dom(G1) = dom(G2)] and for each [x],
    [G1 ⊢ G1(x) <: G2(x)]. *)
Reserved Notation "G1 ≍ G2" (at level 35).

Inductive equivenv: ctx -> ctx -> Prop :=
| equivenv_empty : empty ≍ empty
| equivenv_grow: forall G G' x T,
    G ≍ G' ->
    ok (G & x ~ T) ->
    G & x ~ T ≍ G' & x ~ T
| equivenv_grow_open: forall G G' x T,
    G ≍ G' ->
    ok (G & x ~ typ_bnd T) ->
    G & x ~ typ_bnd T ≍ G' & x ~ open_typ x T
| equivenv_grow_bnd : forall G G' x T,
    G ≍ G' ->
    ok (G & x ~ open_typ x T) ->
    G & x ~ open_typ x T ≍ G' & x ~ typ_bnd T
where "G1 ≍ G2" := (equivenv G1 G2).

Hint Constructors equivenv.

(** If [ok G], then [G ⪯ G].
    Note: [ok(G)] means that [G]'s domain consists of distinct variables.
    [ok] is defined in [TLC.LibEnv.v] *)
Lemma equivenv_refl : forall G, ok G -> G ≍ G.
Proof.
  intros G H. induction H; auto.
Qed.
Hint Resolve equivenv_refl.

Lemma equivenv_ok_fresh : forall G G', G ≍ G' -> ok G' /\ (forall x, x # G -> x # G').
Proof.
  introv H.
  induction H;
    destruct_all;
    match goal with
    | [H : ok (?G & ?x ~ _) |- _] =>
      pose proof (ok_push_inv H0) as [? ?]; split; auto
    | _ => split; auto
    end.
Qed.

Lemma equivenv_ok_l : forall G G', G ≍ G' -> ok G.
Proof.
  introv H. induction H; auto.
Qed.
Hint Resolve equivenv_ok_l.

Lemma equivenv_ok_r : forall G G', G ≍ G' -> ok G'.
Proof.
  introv H. apply equivenv_ok_fresh in H. apply H.
Qed.
Hint Resolve equivenv_ok_r.

Lemma equivenv_ok_r_push : forall G G' x T T', G ≍ G' -> ok (G & x ~ T) -> ok (G' & x ~ T').
Proof.
  introv H Hok. apply equivenv_ok_fresh in H.
  apply ok_push; apply H. apply (ok_push_inv Hok).
Qed.
Hint Resolve equivenv_ok_r_push.

Lemma equivenv_symm : forall G G', G ≍ G' -> G' ≍ G.
Proof.
  intros G G' H.
  induction H; constructor; auto;
    destruct (equivenv_ok_fresh H) as [? ?]; destruct (ok_push_inv H0) as [? ?];
  auto.
Qed.
Hint Resolve equivenv_symm.
