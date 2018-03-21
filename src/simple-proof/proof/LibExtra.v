Set Implicit Arguments.

Require Import LibVar LibLN.

Lemma var_decide : forall (x y : var), {x = y} + {x <> y}.
Proof.
  intros x y.
  pose proof (var_compare_eq x y).
  rewrite LibReflect.isTrue_eq_if in H.
  cases_if; auto.
Qed.

(** Converting between binding and in dom *)
Lemma dom_to_binds : forall A (E : env A) x,
    x \in dom E ->
    exists v, binds x v E.
Proof.
  induction E using env_ind.
  - intros; false. simpl_dom.
    rewrite in_empty in H; auto.
  - intros.
    destruct (var_decide x0 x) as [?H | ?H].
    + subst x0; exists v; auto.
    + rewrite dom_concat, in_union in H.
      destruct H.
      * apply IHE in H.
        destruct H as [?v ?H].
        exists v0; apply binds_concat_left; auto.
      * false. simpl_dom; rewrite in_singleton in H.
        auto.
Qed.

Lemma binds_to_dom : forall A (E : env A) x v,
    binds x v E ->
    x \in dom E.
Proof.
  introv H. induction E using env_ind.
  - exfalso; eauto using binds_empty_inv.
  - destruct (binds_push_inv H) as [[? ?] | [? ?]]; subst; simpl_dom; rewrite in_union.
    + left. auto using in_singleton_self.
    + right. auto.
Qed.
