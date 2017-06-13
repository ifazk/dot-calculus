Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

(* ###################################################################### *)
(** ** Weakening *)

Lemma weaken_rules:
  (forall G t T, G |- t : T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 |- t : T) /\
  (forall G x T d D, G && x ~ T |- d : D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3 & x ~ T) ->
    (G1 & G2 & G3) && x ~ T |- d : D) /\
  (forall G x U ds T, G && x ~ U |- ds :: T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3 & x ~ U) ->
    G1 & G2 & G3 && x ~ U |- ds :: T) /\
  (forall G p, norm G p -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    norm (G1 & G2 & G3) p) /\
  (forall G T U, G |- T <: U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 |- T <: U).
Proof.
  apply rules_mutind; eauto 4; intros; subst.
  + eapply ty_var. eapply binds_weaken; eauto.
  + apply_fresh ty_all_intro as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 G3). apply* H.
  + apply_fresh ty_let as z.
    - auto.
    - assert (zL: z \notin L) by auto.
      specialize (H0 z zL G1 G2 (G3 & z ~ T)).
      repeat rewrite concat_assoc in H0.
      apply* H0.
  + apply* ty_sngl_intro. apply* binds_weaken.
  + apply ty_def_trm.
    rewrite <- concat_assoc. apply H;rewrite concat_assoc. reflexivity. assumption.
  + apply ty_def_val. rewrite <- concat_assoc. apply H; rewrite concat_assoc. reflexivity. assumption.
  + apply* norm_var. eapply binds_weaken; eassumption.
  + apply* subtyp_sngl_sel1.
  + apply* subtyp_sngl_sel2.
  + apply_fresh subtyp_all as z.
    auto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
Qed.

Lemma weaken_ty_trm:  forall G1 G2 t T,
    G1 |- t : T ->
    ok (G1 & G2) ->
    G1 & G2 |- t : T.
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
  G1 |- S <: U ->
  ok (G1 & G2) ->
  G1 & G2 |- S <: U.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_norm: forall G G' p,
  norm G p ->
  ok (G & G') ->
  norm (G & G') p.
Proof.
  introv Hn Hok.
  assert (G & G' = G & G' & empty) as EqG by (rewrite* concat_empty_r).
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity. rewrite <- EqG. assumption.
Qed.

Lemma weaken_rules_p:
  (forall G t T,
    G |-! t : T ->
    forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      G1 & G2 & G3 |-! t : T) /\
  (forall G p,
    norm_p G p -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    norm_p (G1 & G2 & G3) p).
Proof.
  apply ts_mutind_p; eauto; intros.
  - apply ty_var_p. apply* binds_weaken. subst*.
  - apply_fresh ty_all_intro_p as z.
    assert (zL: z \notin L) by auto.
    specialize (t0 z zL).
    assert (Hz: G & z ~ T = G1 & G3 & z ~ T) by rewrite* H.
    assert(Hok: ok (G1 & G2 & G3 & z ~ T)) by auto.
    rewrite <- concat_assoc.
    apply ((proj41 weaken_rules) (G & z ~ T)).
    + assumption.
    + rewrite concat_assoc. subst*.
    + rewrite concat_assoc. subst*.
  - apply_fresh ty_new_intro_p as z.
    assert (zL: z \notin L) by auto.
    specialize (t z zL).
    assert (Hz: G & z ~ open_typ z T = G1 & G3 & z ~ open_typ z T) by rewrite* H.
    assert(Hok: ok (G1 & G2 & G3 & z ~ open_typ z T)) by auto. inversions Hz.
    apply* ((proj53 weaken_rules) (G1 & G3)).
  - apply* norm_var_p. subst. apply* binds_weaken.
Qed.

Lemma weaken_ty_trm_p: forall G1 G2 t T,
    G1 |-! t : T ->
    ok (G1 & G2) ->
    G1 & G2 |-! t : T.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_p.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.
