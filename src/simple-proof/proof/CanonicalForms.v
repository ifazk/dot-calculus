(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module proves the Canonical Forms Lemmas, which allow us
    to retrieve the shape of a value given its type. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions RecordAndInertTypes PreciseTyping TightTyping InvertibleTyping
        GeneralToTight Subenvironments Weakening Narrowing Substitution StronglyTypedStores.

(** * Simple Implications of Typing *)

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma typing_implies_bound: forall G x T,
  G ⊢ trm_var (avar_f x) : T ->
  exists S, binds x S G.
Proof.
  introv Ht. dependent induction Ht; eauto.
Qed.

(** * Functions under Inert Contexts *)
(** This lemma corresponds to Lemma 3.7 ([forall] to [G(x)]) in the paper.

    [inert G]            #<br>#
    [G ⊢ x: forall(T)U]       #<br>#
    [――――――――――――――-]    #<br>#
    [exists T', U',]          #<br>#
    [G(x) = forall(T')U']     #<br>#
    [G ⊢ T <: T']        #<br>#
    [forall fresh y, G, y: T ⊢ U'^y <: U^y] *)
Lemma var_typ_all_to_binds: forall G x T U,
    inert G ->
    G ⊢ trm_var (avar_f x) : typ_all T U ->
    (exists L T' U',
        binds x (typ_all T' U') G /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_all (inert_ok Hin) Hinv) as [T' [U' [V' [L [Htp [Hs1 Hs2]]]]]].
  exists L T' U'. repeat split.
  - apply* inert_precise_all_inv.
  - apply~ tight_to_general.
  - assumption.
Qed.

(** This lemma corresponds to Lemma 3.8 ([forall] to [lambda]) in the paper.

    [inert G]                       #<br>#
    [G ⊢ v: forall(T)U]                  #<br>#
    [――――――――――――]                  #<br>#
    [exists T', t,]                       #<br>#
    [v = lambda(T')t]              #<br>#
    [G ⊢ T <: T']                   #<br>#
    [forall fresh y, G, y: T ⊢ t^y: U^y] *)
Lemma val_typ_all_to_lambda: forall G v x t T U,
    inert G ->
    trm_val x v t ->
    G ⊢ t : typ_all T U ->
    (exists L T' t',
        v = val_fun T' t' /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_trm y t') : open_typ y U)).
Proof.
  introv Hin Htv Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible_forall Hin Htv Htt).
  destruct (invertible_val_to_precise_lambda Hin Hinv) as [L [T' [U' [Htp [Hs1 Hs2]]]]].
  inversions Htp.
  exists (L0 \u L \u (dom G)) T' t0. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H3 y HL0).
  eapply ty_sub; eauto. eapply narrow_typing in H3; eauto.
Qed.

(** * Objects under Inert Contexts *)
(** This lemma corresponds to Lemma 3.9 ([mu] to [G(x)]) in the paper.

    [inert G]                    #<br>#
    [G ⊢ x: {a: T}]              #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [exists S, T', G(x) = mu(S)]       #<br>#
    [S^x = ... /\ {a: T'} /\ ...]  #<br>#
    [G ⊢ T' <: T]                *)
Lemma var_typ_rcd_to_binds: forall G x a T U,
    inert G ->
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T U) ->
    (exists S T',
        binds x (typ_bnd S) G /\
        record_has (open_typ x S) (dec_trm a T' T') /\
        G ⊢ T <: T' /\
        G ⊢ T' <: U).
Proof.
  introv Hin Ht.
  destruct (typing_implies_bound Ht) as [S BiG].
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_trm_dec Hinv) as [S' [T' [U' [Htp [Hs1 Hs2]]]]].
  destruct (pf_dec_trm_inv Hin Htp).
  destruct (pf_inert_rcd_U Hin Htp) as [?U' Hr]. subst.
  lets Hr': (precise_flow_record_has Hin Htp). apply pf_binds in Htp.
  exists U'0 S'. repeat_split_right; try assumption; apply* tight_to_general.
Qed.

(** This lemma corresponds to Lemma 3.10 ([mu] to [nu]) in the paper.

    [inert G]                  #<br>#
    [G ⊢ v: mu(T)]             #<br>#
    [G ⊢ x: T^x]               #<br>#
    [T = ... /\ {a: U} /\ ...  ] #<br>#
    [――――――――――――――――――――――――] #<br>#
    [exists t, ds, v = nu(T)ds     ] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: U] *)
Lemma val_mu_to_new: forall G v t S T U a x,
    inert G ->
    x # G ->
    trm_val x v t ->
    G ⊢ t: typ_bnd T ->
    G ⊢ trm_var (avar_f x) : open_typ x T ->
    record_has (open_typ x T) (dec_trm a S U) ->
    exists t' ds,
      v = val_obj T ds /\
      defs_has ds (def_trm a t') /\
      G ⊢ t': U.
Proof.
  introv Hi HxG Htv Ht Hx Hr.
  lets Htt: (general_to_tight_typing Hi Ht).
  lets Hinv: (tight_to_invertible_v Hi HxG Htv Htt).
  inversions Hinv. inversions H.
  pick_fresh z. assert (z \notin L) as Hz by auto.
  specialize (H1 z Hz).
  assert (Hds: G /- open_defs x ds :: open_typ x T)
    by (destruct_notin; eapply renaming_def; eauto).
  destruct (record_has_ty_defs Hds Hr) as [d [Hh Hd]]. inversions Hd.
  exists t0 (open_defs x ds). split*.
Qed.

Lemma strong_mu_to_new: forall G s x T,
    inert G ->
    ty_val_s G s x ->
    binds x (typ_bnd T) G ->
    exists ds, binds x (val_obj T (open_defs x ds)) s /\
               G /- open_defs x ds :: open_typ x T.
Proof.
  introv Hi Hts Bi.
  inversions Hts.
  - pose proof (binds_functional Bi H); subst T0; clear H.
    pose proof (general_to_tight_typing Hi H1).
    pose proof (tight_to_invertible_fun Hi (trm_val_fun x _ _) H).
    inversions H2. inversions H3.
  - pose proof (binds_functional Bi H). inversions H1.
    exists ds; split; auto.
Qed.

(** * Canonical Forms for Functions

    [inert G]            #<br>#
    [s: G]               #<br>#
    [G ⊢ x: forall(T)U]       #<br>#
    [――――――――――――――――――] #<br>#
    [s(x) = lambda(T')t] #<br>#
    [G ⊢ T <: T']        #<br>#
    [G, x: T ⊢ t: U]          *)
Lemma canonical_forms_fun: forall G s x T U,
  inert G ->
  strongly_typed G s ->
  G ⊢ trm_var (avar_f x) : typ_all T U ->
  (exists L T' t, binds x (val_fun T' t) s /\ G ⊢ T <: T' /\
  (forall y, y \notin L -> G & y ~ T ⊢ open_trm y t : open_typ y U)).
Proof.
  introv Hin Hst Hty.
  destruct (var_typ_all_to_binds Hin Hty) as [L [S [T' [BiG [Hs1 Hs2]]]]].
  pose proof (corresponding_types Hst BiG).
  inversions H.
  - pose proof (binds_functional BiG H0). subst T0.
    destruct (val_typ_all_to_lambda Hin (trm_val_fun x _ _) H2)
      as [L' [S' [t' [Heq [Hs1' Hs2']]]]].
    exists (L \u L' \u (dom G)) S' t'. inversions Heq.
    repeat_split_right; eauto.
    intros.
    assert (HL: y \notin L) by auto.
    assert (HL': y \notin L') by auto.
    specialize (Hs2 y HL).
    specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    eapply ty_sub; eauto.
  - pose proof (binds_functional BiG H0). congruence.
Qed.

(** * Canonical Forms for Objects

    [inert G]            #<br>#
    [s: G]               #<br>#
    [G ⊢ x: {a:T}]       #<br>#
    [――――――――――――――――――] #<br>#
    [exists S, ds, t,] #<br>#
    [s(x) = nu(S)ds] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: T] *)
Lemma canonical_forms_obj: forall G s x a S T,
  inert G ->
  strongly_typed G s ->
  G ⊢ trm_var (avar_f x) : (typ_rcd (dec_trm a S T)) ->
  (exists S ds t, binds x (val_obj S (open_defs x ds)) s /\
                  defs_has (open_defs x ds) (def_trm a t) /\
                  G ⊢ t : T).
Proof.
  introv Hi Hst Hty.
  destruct (var_typ_rcd_to_binds Hi Hty) as [?S [?T' [?H [?H [?H ?H]]]]].
  pose proof (corresponding_types Hst H) as Hts.
  destruct (strong_mu_to_new Hi Hts H) as [?ds [?Bis ?]].
  pose proof (record_has_ty_defs H3 H0) as [?d [? ?]].
  inversions H5.
  exists S0 ds t. repeat_split_right; eauto.
Qed.
