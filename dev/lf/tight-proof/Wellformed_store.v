Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

(* ###################################################################### *)
(** ** Well-formed store *)

Lemma wf_sto_to_ok_G: forall s G,
  wf_sto G s -> ok G.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_sto_to_ok_G.

Lemma ctx_binds_to_sto_binds_raw: forall s G x T,
  wf_sto G s ->
  binds x T G ->
  exists G1 G2 v, G = G1 & (x ~ T) & G2 /\ binds x v s /\ ty_trm ty_precise sub_general G1 (trm_val v) T.
Proof.
  introv Wf Bi. gen x T Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) v.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [ds' [Eq [Bi' Tyds]]]]].
      subst. exists G1 (G2 & x ~ T) ds'. rewrite concat_assoc. auto.
Qed.

Lemma sto_binds_to_ctx_binds_raw: forall s G x v,
  wf_sto G s ->
  binds x v s ->
  exists G1 G2 T, G = G1 & (x ~ T) & G2 /\ ty_trm ty_precise sub_general G1 (trm_val v) T.
Proof.
  introv Wf Bi. gen x v Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) T.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [T0' [Eq Ty]]]].
      subst. exists G1 (G2 & x ~ T) T0'. rewrite concat_assoc. auto.
Qed.

Lemma typing_implies_bound: forall m1 m2 G x T,
  ty_trm m1 m2 G (trm_var (avar_f x)) T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_var (avar_f x)) as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm; eauto];
    try solve [inversion Heqt; eapply IHty_trm1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.
