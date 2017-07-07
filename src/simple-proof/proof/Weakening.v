(** printing |-     %\vdash%         #&vdash;#                     *)
(** printing /-     %\vdash%         #&vdash;#                     *)
(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** printing ->     %\rightarrow%    #&rarr;#                      *)
(** printing =>     %\Rightarrow%    #&rArr;#                      *)
(** printing ~~     %\~%             #~#                           *)
(** printing /\     %\wedge%         #&and;#                       *)
(** printing \/     %\vee%           #&or;#                        *)
(** printing forall %\forall%        #&forall;#                    *)
(** printing exists %\exists%        #&exist;#                     *)
(** printing lambda %\lambda%        #&lambda;#                    *)
(** printing mu     %\mu%            #&mu;#                        *)
(** printing nu     %\nu%            #&nu;#                        *)
(** printing Gamma  %\Gamma%         #&Gamma;#                     *)
(** printing Gamma' %\Gamma'%        #&Gamma;'#                    *)
(** printing Gamma1 %\Gamma_1%       #&Gamma;<sub>1</sub>#         *)
(** printing Gamma2 %\Gamma_2%       #&Gamma;<sub>2</sub>#         *)
(** printing Gamma3 %\Gamma_3%       #&Gamma;<sub>3</sub>#         *)
(** printing top    %\top%           #&#8868;#                     *)
(** printing bottom %\bot%           #&perp;#                      *)
(** printing <>     %\ne%            #&ne;#                        *)
(** printing isin   %\in%            #&isin;#                      *)
(** printing subG   %\prec:%         #&#8826;:#                    *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.

(** * Weakening Lemma *)
(** Weakening states that typing is preserved in extended environments. *)

(** [Gamma1, Gamma3 |- t: T]            #<br>#
    [ok(Gamma1, Gamma2, Gamma3)]
    -------------------------------
    [Gamma1, Gamma2, Gamma3 |- t: T]    #<br>#
    and                                #<br>#
    [Gamma1, Gamma3 |- d: D]            #<br>#
    [ok(Gamma1, Gamma2, Gamma3)]
    -------------------------------
    [Gamma1, Gamma2, Gamma3 |- d: D]    #<br>#
    and                                #<br>#
    [Gamma1, Gamma3 |- ds :: T]         #<br>#
    [ok(Gamma1, Gamma2, Gamma3)]
    -------------------------------
    [Gamma1, Gamma2, Gamma3 |- ds :: T] #<br>#
    and                                #<br>#
    [Gamma1, Gamma3 |- T <: U]          #<br>#
    [ok(Gamma1, Gamma2, Gamma3)]
    -------------------------------
    [Gamma1, Gamma2, Gamma3 |- T <: U]  #<br>#

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

(** Weakening lemma specialized to term typing. *)
Lemma weaken_ty_trm: forall G1 G2 t T,
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

(** Weakening lemma specialized to subtyping. *)
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

(** Weakening lemma for precise typing.
    The first formulation is more general (required for a useful induction hypothesis). *)
Lemma weaken_rules_p: forall G t T,
    G |-! t : T ->
    forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      G1 & G2 & G3 |-! t : T.
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

(** Weakening lemma for precise typing
    (this version is used in the proof). *)
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
