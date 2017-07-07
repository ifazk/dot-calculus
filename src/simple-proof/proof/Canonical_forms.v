(** This module proves the Canonical Forms Lemmas, which allow us
    to retrieve the shape of a value given its type. *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import Narrowing.
Require Import Helper_lemmas.
Require Import Precise_types.
Require Import Invertible_typing.
Require Import General_to_tight.
Require Import Wellformed_store.
Require Import Substitution.

(** [inert G]            #<br>#
    [G |- x: forall(T)U]       #<br>#
    [――――――――――――――-]    #<br>#
    [exists T', U'.]          #<br>#
    [G(x) = forall(T')U']     #<br>#
    [G |- T <: T']        #<br>#
    [forall fresh y.
      G, y: T |- U'^y <: U^y]
*)
Lemma var_typ_all_to_binds: forall G x T U,
    inert G ->
    G |- trm_var (avar_f x) : typ_all T U ->
    (exists L T' U',
        binds x (typ_all T' U') G /\
        G |- T <: T' /\
        (forall y, y \notin L -> G & y ~ T |- (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_all (inert_ok Hin) Hinv) as [T' [U' [L [Htp [Hs1 Hs2]]]]].
  exists L T' U'. repeat split.
  - apply~ inert_precise_all_inv.
  - apply~ tight_to_general.
  - assumption.
Qed.

(** [inert G]                       #<br>#
    [G |- v: forall(T)U]                  #<br>#
    [――――――――――――]                  #<br>#
    [exists T' t.]                       #<br>#
    [v = lambda(T').t]              #<br>#
    [G |- T <: T']                   #<br>#
    [forall fresh y. G, y: T |- t^y: U^y] *)
Lemma val_typ_all_to_lambda: forall G v T U,
    inert G ->
    G |- (trm_val v) : typ_all T U ->
    (exists L T' t,
        v = val_lambda T' t /\
        G |- T <: T' /\
        (forall y, y \notin L -> G & y ~ T |- (open_trm y t) : open_typ y U)).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible_v Hin Htt).
  destruct (invertible_val_to_precise_lambda Hinv Hin) as [L [T' [U' [Htp [Hs1 Hs2]]]]].
  destruct (precise_forall_inv Htp) as [t Heq].
  subst. inversions Htp.
  exists (L0 \u L \u (dom G)) T' t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H1 y HL0).
  eapply ty_sub; eauto. eapply narrow_typing in H1; eauto.
  apply~ subenv_last.
Qed.

(** * Canonical Forms for Functions

    [inert G]            #<br>#
    [G ~~ s]             #<br>#
    [G |- x: forall(T)U]       #<br>#
    [――――――――――――――――――] #<br>#
    [s(x) = lambda(T')t] #<br>#
    [G |- T <: T']        #<br>#
    [G, x: T |- t: U]          *)
Lemma canonical_forms_fun: forall G s x T U,
  G ~~ s ->
  inert G ->
  G |- trm_var (avar_f x) : typ_all T U ->
  (exists L T' t, binds x (val_lambda T' t) s /\ G |- T <: T' /\
  (forall y, y \notin L -> G & y ~ T |- open_trm y t : open_typ y U)).
Proof.
  introv Hwf Hin Hty.
  destruct (var_typ_all_to_binds Hin Hty) as [L [S [T' [BiG [Hs1 Hs2]]]]].
  destruct (corresponding_types Hwf Hin BiG) as [v [Bis Ht]].
  destruct (val_typ_all_to_lambda Hin Ht) as [L' [S' [t [Heq [Hs1' Hs2']]]]].
  subst.
  exists (L \u L' \u (dom G)) S' t. repeat split~.
  - eapply subtyp_trans; eauto.
  - intros.
    assert (HL: y \notin L) by auto.
    assert (HL': y \notin L') by auto.
    specialize (Hs2 y HL).
    specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    + eapply ty_sub; eauto.
    + apply~ subenv_last.
Qed.

(** [d1 isin ds]             #<br>#
    [label(d2) notin ds]     #<br>#
    [―――――――――――――――――――――]  #<br>#
    [label(d1) <> label(d2)]  *)
Lemma defs_has_hasnt_neq: forall ds d1 d2,
  defs_has ds d1 ->
  defs_hasnt ds (label_of_def d2) ->
  label_of_def d1 <> label_of_def d2.
Proof.
  introv Hhas Hhasnt.
  unfold defs_has in Hhas.
  unfold defs_hasnt in Hhasnt.
  induction ds.
  - simpl in Hhas. inversion Hhas.
  - simpl in Hhasnt. simpl in Hhas. case_if; case_if.
    + inversions Hhas. assumption.
    + apply IHds; eauto.
Qed.

(** [G |- ds :: ... /\ D /\ ...]       #<br>#
    [―――――――――――――――――――――――]       #<br>#
    [exists d. ds = ... /\ d /\ ...]       #<br>#
    [G |- d: D]                      *)
Lemma record_has_ty_defs: forall G T ds D,
  G /- ds :: T ->
  record_has T D ->
  exists d, defs_has ds d /\ G /- d : D.
Proof.
  introv Hdefs Hhas. induction Hdefs.
  - inversion Hhas; subst. exists d. split.
    + unfold defs_has. simpl. rewrite If_l; reflexivity.
    + assumption.
  - inversion Hhas; subst.
    + destruct (IHHdefs H4) as [d' [H1 H2]].
      exists d'. split.
      * unfold defs_has. simpl. rewrite If_r. apply H1.
        apply not_eq_sym. eapply defs_has_hasnt_neq; eauto.
      * assumption.
    + exists d. split.
      * unfold defs_has. simpl. rewrite If_l; reflexivity.
      * inversions* H4.
Qed.

(** This lemma corresponds to Lemma 3.9 (mu to G(x)) in the paper.

    [inert G]                    #<br>#
    [G |- x: {a: T}]              #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [exists S T'. G(x) = mu(S)]       #<br>#
    [S^x = ... /\ {a: T'} /\ ...]  #<br>#
    [G |- T' <: T]                *)
Lemma var_typ_rcd_to_binds: forall G x a T,
    inert G ->
    G |- trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    (exists S T',
        binds x (typ_bnd S) G /\
        record_has (open_typ x S) (dec_trm a T') /\
        G |- T' <: T).
Proof.
  introv Hin Ht.
  destruct (typing_implies_bound Ht) as [S BiG].
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_trm_dec Hinv) as [T' [Htp Hs]].
  destruct (precise_flow_lemma Htp) as [U Pf].
  destruct (pf_inert_rcd_U Hin Pf) as [U' Hr]. subst.
  lets Hr': (precise_flow_record_has Hin Pf). apply pf_binds in Pf.
  exists U' T'. split. assumption. split. assumption. apply* tight_to_general.
Qed.

(** This lemma corresponds to Lemma 3.10 (mu to nu) in the paper.

    Note: the paper formulation misses the condition that [G |- x: T^x].
    We will fix that in the final submission.

    [inert G]                  #<br>#
    [G |- v: mu(T)]             #<br>#
    [G |- x: T^x]               #<br>#
    [T = ... /\ {a: U} /\ ...  ] #<br>#
    [――――――――――――――――――――――――] #<br>#
    [exists t ds. v = nu(T)ds     ] #<br>#
    [ds^x = ... /\ {a = t} ...] #<br>#
    [G |- t: U] *)
Lemma val_mu_to_new: forall G v T U a x,
    inert G ->
    G |- trm_val v: typ_bnd T ->
    G |- trm_var (avar_f x) : open_typ x T ->
    record_has (open_typ x T) (dec_trm a U) ->
    exists t ds,
      v = val_new T ds /\
      defs_has (open_defs x ds) (def_trm a t) /\
      G |- t: U.
Proof.
  introv Hi Ht Hx Hr.
  lets Htt: (general_to_tight_typing Hi Ht).
  lets Hinv: (tight_to_invertible_v Hi Htt).
  lets Hp: (invertible_val_to_precise_rec Hinv).
  destruct (precise_bnd_inv Hp) as [ds Heq]. subst.
  inversions Hp. pick_fresh z. assert (z \notin L) as Hz by auto.
  specialize (H1 z Hz).
  assert (G /- open_defs x ds :: open_typ x T) as Hds. {
    rewrite subst_intro_typ with (x:=z). rewrite subst_intro_defs with (x:=z).
    eapply subst_ty_defs. eapply H1. apply* ok_push. auto.
    rewrite* <- subst_intro_typ. auto. auto.
  }
  destruct (record_has_ty_defs Hds Hr) as [d [Hh Hd]]. inversions Hd.
  exists t ds. split*.
Qed.

(** * Canonical Forms for Objects

    [inert G]            #<br>#
    [G ~~ s]             #<br>#
    [G |- x: forall(T)U]       #<br>#
    ――――――――――――――――――――
    [s(x) = lambda(T')t] #<br>#
    [G |- T <: T']        #<br>#
    [G, x: T |- t: U] *)
Lemma canonical_forms_obj: forall G s x a T,
  inert G ->
  G ~~ s ->
  G |- trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
  (exists S ds t, binds x (val_new S ds) s /\ defs_has (open_defs x ds) (def_trm a t) /\ G |- t : T).
Proof.
  introv Hi Hwf Hty.
  destruct (var_typ_rcd_to_binds Hi Hty) as [S [T' [Bi [Hr Hs]]]].
  destruct (corresponding_types Hwf Hi Bi) as [v [Bis Ht]].
  apply ty_var in Bi. apply ty_rec_elim in Bi.
  destruct (val_mu_to_new Hi Ht Bi Hr) as [t [ds [Heq [Hdefs Ht']]]].
  subst. exists S ds t. repeat split~. eapply ty_sub; eauto.
Qed.
