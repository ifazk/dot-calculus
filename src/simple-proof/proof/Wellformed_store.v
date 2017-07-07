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
