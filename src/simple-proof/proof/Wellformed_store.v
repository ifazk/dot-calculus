Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Narrowing.
Require Import Helper_lemmas.
Require Import Precise_types.
Require Import Invertible_typing.
Require Import General_to_tight.

(** This module establishes properties of the well-formedness
    relation [Gamma ~~ s] ([wf_sto]). *)

(** If [Gamma ~~ s] and [x notin s], then [x notin Gamma]. *)
Lemma wf_sto_notin_dom: forall G s x,
    G ~~ s ->
    x # s -> x # G.
Proof.
  intros. induction H; auto.
Qed.

(** If [Gamma ~~ s], the variables in the domain of [s] are distinct. *)
Lemma wf_sto_to_ok_G: forall s G,
    G ~~ s -> ok G.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_sto_to_ok_G.

Lemma invertible_val_to_precise_rec: forall G v T,
    G |-##v v : typ_bnd T ->
    G |-! trm_val v : typ_bnd T.
Proof.
  introv Ht.
  inversions Ht. assumption.
Qed.

Lemma invertible_val_to_precise_lambda: forall G v S T,
    G |-##v v : typ_all S T ->
    inert G ->
    exists L S' T',
      G |-! trm_val v : typ_all S' T' /\
      G |- S <: S' /\
      (forall y, y \notin L ->
                 G & y ~ S |- open_typ y T' <: open_typ y T).
Proof.
  introv Ht Hg. dependent induction Ht.
  - exists (dom G) S T. split*.
  - destruct (IHHt S0 T0 eq_refl Hg) as [L' [S1 [T1 [Hp [Hss Hst]]]]].
    exists (L \u L' \u dom G) S1 T1. split. assumption. split. apply subtyp_trans with (T:=S0).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ S)) as Hok. {
      apply* ok_push.
    }
    apply subtyp_trans with (T:=open_typ y T0).
    eapply narrow_subtyping. apply* Hst. apply subenv_last. apply* tight_to_general.
    assumption. assumption.
    apply* H0.
Qed.

Lemma precise_forall_inv : forall G v S T,
    G |-! trm_val v : typ_all S T ->
    exists t,
      v = val_lambda S t.
Proof.
  introv Ht. inversions Ht. exists* t.
Qed.

Lemma precise_bnd_inv : forall G v S,
    G |-! trm_val v : typ_bnd S ->
    exists ds,
      v = val_new S ds.
Proof.
  introv Ht. inversions Ht. exists* ds.
Qed.

Lemma corresponding_types: forall G s x T,
    G ~~ s ->
    inert G ->
    binds x T G ->
    (exists v, binds x v s /\
          G |- trm_val v : T).
Proof.
  introv Hwf Hin BiG. induction Hwf.
  - false* binds_empty_inv.
  - destruct (classicT (x = x0)).
    + subst. apply binds_push_eq_inv in BiG. subst.
      exists v. repeat split~. apply~ weaken_ty_trm.
    + apply binds_push_neq_inv in BiG; auto.
      assert (Hin': inert G).
      {
        inversions Hin.
        - false* empty_push_inv.
        - destruct (eq_push_inv H2) as [Hx [Hv HG]]. subst*.
      }
      specialize (IHHwf Hin' BiG) as [v' [Bis Ht]].
      exists v'. repeat split~. apply~ weaken_ty_trm.
Qed.
