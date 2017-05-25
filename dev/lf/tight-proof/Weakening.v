Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

(* ###################################################################### *)
(** ** Weakening *)

Lemma weaken_rules_ctx:
  (forall G S t T, G, S |- t :: T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3, S |- t :: T) /\
  (forall G S d D, G, S /- d :: D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3, S /- d :: D) /\
  (forall G S ds T, G, S /- ds ::: T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3, S /- ds ::: T) /\
  (forall G S T U, G, S |- T <: U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3, S |- T <: U).
Proof.
  apply rules_mutind; try solve [eauto].
  + intros. subst.
    eapply ty_var. eapply binds_weaken; eauto.
  + intros. subst.
    apply_fresh ty_all_intro as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ open_typ z T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh ty_let as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
  + intros. subst.
    apply_fresh subtyp_all as z.
    eauto.
    eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
Qed.

Lemma weaken_rules_sigma:
  (forall G S t T, G, S |- t :: T -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    G, S1 & S2 & S3 |- t :: T) /\
  (forall G S d D, G, S /- d :: D -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    G, S1 & S2 & S3 /- d :: D) /\
  (forall G S ds T, G, S /- ds ::: T -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    G, S1 & S2 & S3 /- ds ::: T) /\
  (forall G S T U, G, S |- T <: U -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    G, S1 & S2 & S3 |- T <: U).
Proof.
  apply rules_mutind; try solve [eauto].
  intros. subst.
  eapply ty_loc. eapply binds_weaken; eauto.
Qed.

Lemma weaken_ty_trm_ctx: forall G1 G2 S t T,
    G1, S |- t :: T ->
    ok (G1 & G2) ->
    G1 & G2, S |- t :: T.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_ctx.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_ty_trm_sigma: forall G S1 S2 t T,
  G, S1 |- t :: T ->
  ok (S1 & S2) ->
  G, S1 & S2 |- t :: T.
Proof.
  intros. assert (S1 & S2 = S1 & S2 & empty) as EqS. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqS. apply* weaken_rules_sigma.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqS. assumption.
Qed.

Lemma weaken_subtyp_ctx: forall G1 G2 S T U,
  G1, S |- T <: U ->
  ok (G1 & G2) ->
  G1 & G2, S |- T <: U.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_ctx.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_subtyp_sigma: forall G S1 S2 T U,
  G, S1 |- T <: U ->
  ok (S1 & S2) ->
  G, S1 & S2 |- T <: U.
Proof.
  intros.
    assert (S1 & S2 = S1 & S2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_sigma.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_rules_ctx_p: forall G S t T, 
    G, S |-! t :: T -> 
       forall G1 G2 G3,
         G = G1 & G3 ->
         ok (G1 & G2 & G3) ->
         G1 & G2 & G3, S |-! t :: T.
Proof.
  intros. induction* H.
  - apply ty_var_p. apply* binds_weaken. subst*.
  - apply_fresh ty_all_intro_p as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL). 
    assert (Hz: G & z ~ T = G1 & G3 & z ~ T) by rewrite* H0.
    assert(Hok: ok (G1 & G2 & G3 & z ~ T)) by auto.
    rewrite <- concat_assoc.
    apply ((proj41 weaken_rules_ctx) (G & z ~ T)).
    + assumption.
    + rewrite concat_assoc. subst*.
    + rewrite concat_assoc. subst*.
  - apply_fresh ty_new_intro_p as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL). 
    assert (Hz: G & z ~ open_typ z T = G1 & G3 & z ~ open_typ z T) by rewrite* H0.
    assert(Hok: ok (G1 & G2 & G3 & z ~ open_typ z T)) by auto.
    rewrite <- concat_assoc.
    apply ((proj43 weaken_rules_ctx) (G & z ~ open_typ z T)).
    + assumption.
    + rewrite concat_assoc. subst*.
    + rewrite concat_assoc. subst*.
Qed.

Lemma weaken_ty_trm_ctx_p: forall G1 G2 S t T,
    G1, S |-! t :: T ->
    ok (G1 & G2) ->
    G1 & G2, S |-! t :: T.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules_ctx_p.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_rules_sigma_p: forall G S t T, 
    G, S |-! t :: T -> 
       forall S1 S2 S3,
         S = S1 & S3 ->
         ok (S1 & S2 & S3) ->
         G, S1 & S2 & S3 |-! t :: T.
Proof.
  intros. induction H; try solve [eauto]; subst.
  - apply ty_loc_p. apply* binds_weaken.
  - apply_fresh ty_all_intro_p as z. 
    assert (zL: z \notin L) by auto.
    specialize (H z zL).
    apply (proj41 weaken_rules_sigma) with (S:=S1 & S3); auto.
  - apply_fresh ty_new_intro_p as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL).
    apply (proj43 weaken_rules_sigma) with (S:=S1 & S3); auto.
Qed.

Lemma weaken_ty_trm_sigma_p: forall G S1 S2 t T,
  G, S1 |-! t :: T ->
  ok (S1 & S2) ->
  G, S1 & S2 |-! t :: T.
Proof.
  intros. assert (S1 & S2 = S1 & S2 & empty) as EqS. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqS. apply* weaken_rules_sigma_p.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqS. assumption.
Qed.
