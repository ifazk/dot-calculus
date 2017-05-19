Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

(* ###################################################################### *)
(** ** Weakening *)

Lemma weaken_rules:
  (forall G t T, ty_trm G t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_trm (G1 & G2 & G3) t T) /\
  (forall G d D, ty_def G d D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_def (G1 & G2 & G3) d D) /\
  (forall G ds T, ty_defs G ds T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_defs (G1 & G2 & G3) ds T) /\
  (forall G T U, subtyp G T U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subtyp (G1 & G2 & G3) T U).
Proof.
  apply rules_mutind; eauto 4; intros; subst.
  + eapply ty_var. eapply binds_weaken; eauto.
  + apply_fresh ty_all_intro as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ open_typ z T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + apply_fresh ty_let as z.
    - auto.
    - assert (zL: z \notin L) by auto.
      specialize (H0 z zL G1 G2 (G3 & z ~ T)).
      repeat rewrite concat_assoc in H0.
      apply* H0.
  + apply_fresh subtyp_all as z.
    - auto.
    - assert (zL: z \notin L) by auto.
      specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
      repeat rewrite concat_assoc in H0.
      apply* H0.
Qed.

Lemma weaken_ty_trm: forall G1 G2 t T,
    ty_trm G1 t T ->
    ok (G1 & G2) ->
    ty_trm (G1 & G2) t T.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_subtyp: forall G1 G2 S U,
  subtyp G1 S U ->
  ok (G1 & G2) ->
  subtyp (G1 & G2) S U.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_rules_p: forall G t T, 
    ty_trm_p G t T -> 
    forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      ty_trm_p (G1 & G2 & G3) t T.
Proof.
  intros. induction* H.
  - apply ty_var_p. apply* binds_weaken. subst*.
  - apply_fresh ty_all_intro_p as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL). 
    assert (Hz: G & z ~ T = G1 & G3 & z ~ T) by rewrite* H0.
    assert(Hok: ok (G1 & G2 & G3 & z ~ T)) by auto.
    rewrite <- concat_assoc.
    apply ((proj41 weaken_rules) (G & z ~ T)).
    + assumption.
    + rewrite concat_assoc. subst*.
    + rewrite concat_assoc. subst*.
  - apply_fresh ty_new_intro_p as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL). 
    assert (Hz: G & z ~ open_typ z T = G1 & G3 & z ~ open_typ z T) by rewrite* H0.
    assert(Hok: ok (G1 & G2 & G3 & z ~ open_typ z T)) by auto.
    rewrite <- concat_assoc.
    apply ((proj43 weaken_rules) (G & z ~ open_typ z T)).
    + assumption.
    + rewrite concat_assoc. subst*.
    + rewrite concat_assoc. subst*.
Qed.

Lemma weaken_ty_trm_p: forall G1 G2 t T,
    ty_trm_p G1 t T ->
    ok (G1 & G2) ->
    ty_trm_p (G1 & G2) t T.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_p.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.
