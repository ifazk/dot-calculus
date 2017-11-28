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
Require Import Definitions Narrowing RecordAndInertTypes
            Substitution Weakening InertTyping.

(** * Well-typed stacks *)

(** The operational semantics is defined in terms of pairs [(s, t)], where
    [s] is a stack and [t] is a term.
    Given a typing [G ⊢ (s, t): T], [well_typed] establishes a correspondence
    between [G] and the stack [s].

    We say that [s] is well-typed with respect to [G] if
    - [G = {(xi mapsto Ti) | i = 1, ..., n}]
    - [s = {(xi mapsto vi) | i = 1, ..., n}]
    - [G ⊢ vi: Ti].

    We say that [e] is well-typed with respect to [G], denoted as [s: G]. *)

Definition well_typed (G : ctx) (s : sta) : Prop :=
  ok G /\
  ok s /\
  (dom G = dom s) /\
  (forall x T v, binds x T G ->
            binds x v s ->
            G ⊢ trm_val v : T).

Hint Unfold well_typed.

(** * Well-typedness *)

(** If [s: G], the variables in the domain of [s] are distinct. *)
Lemma well_typed_to_ok_G: forall s G,
    well_typed G s -> ok G.
Proof.
  intros. destruct H as [? [? ?]]. auto.
Qed.
Hint Resolve well_typed_to_ok_G.

Lemma well_typed_to_ok_s: forall s G,
    well_typed G s -> ok s.
Proof.
  intros. destruct H as [? [? ?]]. auto.
Qed.
Hint Resolve well_typed_to_ok_s.

(** [s: G]       #<br>#
    [x ∉ dom(G)] #<br>#
    [――――――――――] #<br>#
    [x ∉ dom(s)] *)
Lemma well_typed_notin_dom: forall G s x,
    well_typed G s ->
    x # s ->
    x # G.
Proof.
  introv Hwt. destruct Hwt as [? [? [?Hdom ?]]].
  unfold notin. rewrite Hdom.
  auto.
Qed.

Lemma well_typed_empty:
    well_typed empty empty.
Proof.
  repeat split; auto.
  - simpl_dom; auto.
  - introv B. exfalso; apply* binds_empty_inv.
Qed.
Hint Resolve well_typed_empty.

Lemma well_typed_push: forall G s x T v,
    well_typed G s ->
    x # G ->
    x # s ->
    G ⊢ trm_val v : T ->
    well_typed (G & x ~ T) (s & x ~ v).
Proof.
  intros. unfold well_typed in *.
  destruct_all.
  repeat split; auto.
  - simpl_dom. fequal. auto.
  - intros x0 T0 v0 BxG. gen v0.
    destruct (binds_push_inv BxG) as [[?Heqx ?HeqT] | [?Hneq ?HB]].
    + subst x0 T0. introv Bxv. apply binds_push_eq_inv in Bxv.
      subst v0. apply weaken_ty_trm; auto.
    + intros.
      assert (binds x0 T0 G) by eauto using binds_push_neq_inv.
      assert (binds x0 v0 s) by eauto using binds_push_neq_inv.
      apply weaken_ty_trm; eauto.
Qed.
Hint Resolve well_typed_push.

(** [s: G]              #<br>#
    [G(x) = T]          #<br>#
    [―――――――――――――]     #<br>#
    [exists v, s(x) = v]     #<br>#
    [G ⊢ v: T]          *)
Lemma corresponding_types: forall G s x T,
    well_typed G s ->
    binds x T G ->
    (exists v, binds x v s /\
          G ⊢ trm_val v : T).
Proof.
  introv Hwt BiG. destruct Hwt as [?HokG [?HokS [?HdomEq ?]]].
  pose proof (get_some_inv BiG) as HinDom.
  symmetry in HdomEq.
  pose proof (get_some (Logic.eq_ind_r _ HinDom HdomEq)) as [?v Bis].
  exists v. split.
  - apply Bis.
  - eauto.
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
  well_typed G s ->
  G ⊢ trm_var (avar_f x) : typ_all T U ->
  (exists L T' t, binds x (val_fun T' t) s /\ G ⊢ T <: T' /\
  (forall y, y \notin L -> G & y ~ T ⊢ open_trm y t : open_typ y U)).
Proof.
  introv Hin Hwt Hty.
  destruct (var_typ_all_to_binds Hin Hty) as [L [S [T' [BiG [Hs1 Hs2]]]]].
  destruct (corresponding_types Hwt BiG) as [v [Bis Ht]].
  destruct (val_typ_all_to_lambda _ Hin Ht) as [L' [S' [t [Heq [Hs1' Hs2']]]]].
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
Lemma canonical_forms_obj: forall G s x a T,
  inert G ->
  well_typed G s ->
  G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
  (exists S ds t, binds x (val_obj S ds) s /\ defs_has (open_defs x ds) (def_trm a t) /\ G ⊢ t : T).
Proof.
  introv Hi Hwt Hty.
  destruct (var_typ_rcd_to_binds Hi Hty) as [S [T' [Bi [Hr Hs]]]].
  destruct (corresponding_types Hwt Bi) as [v [Bis Ht]].
  apply ty_var in Bi. apply ty_rec_elim in Bi.
  destruct (val_mu_to_new _ Hi Ht Bi Hr) as [t [ds [Heq [Hdefs Ht']]]].
  subst. exists S ds t. repeat split~. eapply ty_sub; eauto.
Qed.
