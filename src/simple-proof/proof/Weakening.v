(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.

(** * Weakening Lemma *)
(** Weakening states that typing is preserved in extended environments. *)

(** [G1, G3 ⊢ t: T]                    #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ t: T] #<br># #<br>#

    and

    [G1, G3 ⊢ d: D]                    #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ d: D] #<br># #<br>#

    and

    [G1, G3 ⊢ ds :: T]                 #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ ds :: T] #<br># #<br>#

    and

    [G1, G3 ⊢ T <: U]                  #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ T <: U] #<br># #<br>#

    The proof is by mutual induction on term typing, definition typing, and subtyping. *)
Lemma weaken_rules:
  (forall G S t T, G @@ S ⊢ t : T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 @@ S ⊢ t : T) /\
  (forall G S d D, G @@ S/- d : D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 @@ S /- d : D) /\
  (forall G S ds T, G @@ S/- ds :: T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 @@ S /- ds :: T) /\
  (forall G S T U, G @@ S ⊢ T <: U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 @@ S ⊢ T <: U).
Proof.
  apply rules_mutind; intros; subst;
  eauto 4 using binds_weaken;
  fresh_constructor;
    match goal with
    | [ H: forall z, z \notin ?L -> forall G, _,
        Hok: ok (?G1 & ?G2 & ?G3)
        |- context [?z ~ ?T] ] =>
      assert (zL : z \notin L) by auto;
      specialize (H z zL G1 G2 (G3 & z ~ T));
      rewrite? concat_assoc in H;
      apply~ H
    end.
Qed.

Lemma weaken_rules_sigma:
  (forall G S t T, G @@ S ⊢ t : T -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    G @@ (S1 & S2 & S3) ⊢ t : T) /\
  (forall G S d D, G @@ S /- d : D -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    G @@ (S1 & S2 & S3) /- d : D) /\
  (forall G S ds T, G @@ S /- ds :: T -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    G @@ (S1 & S2 & S3) /- ds :: T) /\
  (forall G S T U, G @@ S ⊢ T <: U -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    G @@ (S1 & S2 & S3) ⊢ T <: U).
Proof.
  apply rules_mutind; try solve [eauto].
  intros. subst.
  eapply ty_loc. eapply binds_weaken; eauto.
Qed.

Ltac weaken_specialize :=
  intros;
  match goal with
  | [ Hok: ok (?G1 & ?G2) |- _ ] =>
    assert (G1 & G2 = G1 & G2 & empty) as EqG by rewrite~ concat_empty_r;
    rewrite EqG; apply~ weaken_rules;
    (rewrite concat_empty_r || rewrite <- EqG); assumption
  end.

Ltac weaken_specialize_sigma :=
  intros;
  match goal with
  | [ Hok: ok (?G1 & ?G2) |- _ ] =>
    assert (G1 & G2 = G1 & G2 & empty) as EqG by rewrite~ concat_empty_r;
    rewrite EqG; apply~ weaken_rules_sigma;
    (rewrite concat_empty_r || rewrite <- EqG); assumption
  end.

(** Weakening lemma specialized to term typing. *)
Lemma weaken_ty_trm: forall G1 G2 S t T,
    G1 @@ S ⊢ t : T ->
    ok (G1 & G2) ->
    G1 & G2 @@ S ⊢ t : T.
Proof.
  weaken_specialize.
Qed.

Lemma weaken_ty_trm_sigma: forall G S1 S2 t T,
  G @@ S1 ⊢ t : T ->
  ok (S1 & S2) ->
  G @@ (S1 & S2) ⊢ t : T.
Proof.
  weaken_specialize_sigma.
Qed.

(** Weakening lemma specialized to subtyping. *)
Lemma weaken_subtyp: forall G1 G2 S T U,
  G1 @@ S ⊢ T <: U ->
  ok (G1 & G2) ->
  G1 & G2 @@ S ⊢ T <: U.
Proof.
  weaken_specialize.
Qed.

Lemma weaken_subtyp_sigma: forall G S1 S2 T U,
  G @@ S1 ⊢ T <: U ->
  ok (S1 & S2) ->
  G @@ (S1 & S2) ⊢ T <: U.
Proof.
  weaken_specialize_sigma.
Qed.
