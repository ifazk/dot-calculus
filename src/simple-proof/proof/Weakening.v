(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.

(** * Weakening Lemma *)
(** Weakening states that typing is preserved in extended environments. *)

(** [G1, G3 |- t: T]                    #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 |- t: T] #<br># #<br>#

    and

    [G1, G3 |- d: D]                    #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 |- d: D] #<br># #<br>#

    and

    [G1, G3 |- ds :: T]                 #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 |- ds :: T] #<br># #<br>#

    and

    [G1, G3 |- T <: U]                  #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 |- T <: U] #<br># #<br>#

    The proof is by mutual induction on term typing, definition typing, and subtyping. *)
Lemma weaken_rules:
  (forall G t T, G |- t : T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 |- t : T) /\
  (forall G d D, G /- d : D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 /- d : D) /\
  (forall G ds T, G /- ds :: T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    G1 & G2 & G3 /- ds :: T) /\
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
    rewrite? concat_assoc in H.
    apply~ H.
  + apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ open_typ z T)).
    rewrite? concat_assoc in H.
    apply~ H.
  + apply_fresh ty_let as z.
    - auto.
    - assert (zL: z \notin L) by auto.
      specialize (H0 z zL G1 G2 (G3 & z ~ T)).
      rewrite? concat_assoc in H0.
      apply~ H0.
  + apply_fresh subtyp_all as z.
    - auto.
    - assert (zL: z \notin L) by auto.
      specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
      rewrite? concat_assoc in H0.
      apply~ H0.
Qed.

(** Weakening lemma specialized to term typing. *)
Lemma weaken_ty_trm: forall G1 G2 t T,
    G1 |- t : T ->
    ok (G1 & G2) ->
    G1 & G2 |- t : T.
Proof.
  intros.
  assert (G1 & G2 = G1 & G2 & empty) as EqG by rewrite~ concat_empty_r.
  rewrite EqG. apply~ weaken_rules.
  - rewrite concat_empty_r. assumption.
  - rewrite <- EqG. assumption.
Qed.

(** Weakening lemma specialized to subtyping. *)
Lemma weaken_subtyp: forall G1 G2 S U,
  G1 |- S <: U ->
  ok (G1 & G2) ->
  G1 & G2 |- S <: U.
Proof.
  intros.
  assert (G1 & G2 = G1 & G2 & empty) as EqG by rewrite~ concat_empty_r.
  rewrite EqG. apply~ weaken_rules.
  - rewrite concat_empty_r. assumption.
  - rewrite <- EqG. assumption.
Qed.
