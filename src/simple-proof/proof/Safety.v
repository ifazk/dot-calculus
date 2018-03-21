Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import
        Binding Definitions RecordAndInertTypes PreciseTyping
        OperationalSemantics Substitution Weakening
        StronglyTypedStores CanonicalForms.

(** The typing of a term with a stack *)
Inductive sto_trm_typ : sto * trm -> typ -> Prop :=
| sto_trm_typ_c : forall G s t T,
    inert G ->
    strongly_typed G s ->
    G ⊢ t : T ->
    sto_trm_typ (s, t) T.

Hint Constructors sto_trm_typ.

Notation "'⊢' t ':' T" := (sto_trm_typ t T) (at level 40, t at level 59).

(** * Preservation *)

(** If a value [v] has type [T], then [v] has a precise type [T']
    that is a subtype of [T].
    This lemma corresponds to Lemma 3.15 in the paper. *)
Lemma val_typing: forall G v x t T,
  trm_val x v t ->
  x # G ->
  G ⊢ t : T ->
  exists T', G ⊢!v v ^^ x : T' /\ G ⊢ T' <: T.
Proof.
  intros G v x t T Htv Hfr H. inversions Htv; simpl; dependent induction H; eauto;
  destruct (IHty_trm _ _ Hfr eq_refl); destruct_all; eauto.
Qed.

(** Helper tactics for proving Preservation *)

Ltac binds_eq :=
  match goal with
  | [Hb1: binds ?x _ ?G,
     Hb2: binds ?x _ ?G |- _] =>
     apply (binds_functional Hb1) in Hb2; inversions Hb2
  end.

Ltac invert_red :=
  match goal with
  | [Hr: (_, _) |-> (_, _) |- _] => inversions Hr
  end.

Ltac red_trm_to_val :=
  match goal with
  | [ H : (_, trm_lambda ?T ?e) |-> _ |- _ ] =>
    remember (val_fun T e);
    assert (trm_val (val_fun T e) (trm_lambda T e)) by auto
  | [ H : (_, trm_new ?T ?ds) |-> _ |- _ ] =>
    assert (trm_val (val_obj T ds) (trm_new T ds)) by auto
  | _ => idtac
  end.

Ltac trm_val_contra :=
  match goal with
  | [ H : trm_val _ _ _ |- _ ] =>
      try solve [inversions H; simpl in *; congruence]
  | _ => idtac
  end.

Ltac solve_IH :=
  match goal with
  | [IH: strongly_typed _ _ ->
         inert _ ->
         forall t', (_, _) |-> (_, _) -> _,
       Wf: strongly_typed _ _,
       In: inert _,
       Hr: (_, _) |-> (_, ?t') |- _] =>
    specialize (IH Wf In t' Hr); destruct_all
  end;
  match goal with
  | [Hi: _ & ?G' ⊢ _ : _ |- _] =>
    exists G'; repeat_split_right; auto
  end.

Ltac solve_let :=
  invert_red; trm_val_contra; solve_IH; fresh_constructor; eauto; apply* weaken_rules.

(** [s: G]                  #<br>#
    [inert [G]              #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [G ⊢ t: T]              #<br>#
    [―――――――――――――――――――]   #<br>#
    [exists G', inert G']        #<br>#
    [s': G, G']             #<br>#
    [G, G' ⊢ t': T]         *)
Lemma preservation_helper: forall G s t s' t' T,
    strongly_typed G s ->
    inert G ->
    (s, t) |-> (s', t') ->
    G ⊢ t : T ->
    exists G', inert G' /\
          strongly_typed (G & G') s' /\
          G & G' ⊢ t' : T.
Proof.
  introv Hwf Hin Hred Ht. gen t'.
  induction Ht; intros; try solve [invert_red; trm_val_contra].
  - Case "ty_all_intro".
    invert_red. inversions H6.
    exists (x ~ typ_all T U). repeat_split_right; auto.
    + rewrite <- concat_empty_l; eauto.
    + assert (dom G = dom s) by apply Hwf.
      assert (x # G) by (rewrite H1; auto). clear H4; clear H1.
      assert (G ⊢ trm_lambda T t : typ_all T U) by eauto.
      apply (strongly_typed_push_fun Hwf H2 H1).
  - Case "ty_all_elim".
    invert_red; try trm_val_contra.
    destruct (canonical_forms_fun Hin Hwf Ht1) as [?L [?T [?t [?Bis [?Hsub ?Hty]]]]].
    binds_eq.
    exists (@empty typ). rewrite concat_empty_r. repeat_split_right; auto.
    pick_fresh y. destruct_notin. specialize (Hty y H).
    eapply renaming_typ; try eassumption; eauto.
  - Case "ty_new_intro".
    invert_red.
      match goal with
        | [Hn: ?x # ?s |- _] =>
          pose proof (strongly_typed_notin_dom Hwf Hn) as Hng
      end.
      assert (Ht: G ⊢ trm_new T ds : typ_bnd T) by eauto.
      pose proof (val_typing H5 Hng Ht) as [V [Hv Hs]].
      exists (x ~ V). repeat_split_right.
      + rewrite <- concat_empty_l. constructor~. apply (precise_inert_typ Hv).
      + apply~ strongly_typed_push_precise.
      + assert (G & x ~ V ⊢ trm_var (avar_f x) : V) by auto.
         eapply ty_sub. apply H0. apply* weaken_subtyp.
  - Case "ty_new_elim".
    pose proof (canonical_forms_obj Hin Hwf Ht) as [?S [ds [t [Bis [Has Ty]]]]].
    invert_red; trm_val_contra. binds_eq.
    exists (@empty typ). rewrite concat_empty_r. repeat_split_right; auto.
    rewrite <- H2 in H5.
    match goal with
    | [Hd: defs_has _ (def_trm _ ?t') |- G ⊢ t': T] =>
      rewrite* <- (defs_has_inv Has Hd)
    end.
  - Case "ty_let".
    destruct t; try solve [solve_let].
    + SCase "[t = (let x = a in u)] where a is a variable".
      repeat invert_red; trm_val_contra.
      exists (@empty typ). rewrite concat_empty_r. repeat_split_right; auto.
      apply* renaming_fresh.
  - Case "ty_sub".
    solve_IH.
    match goal with
    | [Hs: _ ⊢ _ <: _,
       Hg: _ & ?G' ⊢ _: _ |- _] =>
      apply weaken_subtyp with (G2:=G') in Hs;
      eauto
    end.
Qed.

(** ** Preservation Theorem *)

(** [⊢ (s, t): T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [⊢ (s', t'): T]         *)
Theorem preservation : forall s s' t t' T,
    ⊢ (s, t) : T ->
    (s, t) |-> (s', t') ->
    ⊢ (s', t') : T.
Proof.
  introv Ht Hr. destruct Ht as [* Hi Hwf Ht].
  lets Hp: (preservation_helper Hwf Hi Hr Ht). destruct Hp as [G' [Hi' [Hwf' Ht']]].
  apply sto_trm_typ_c with (G:=G & G'); auto. apply* inert_concat.
Qed.

(** * Progress *)

(** Helper tactic for proving progress *)
Ltac solve_let_prog :=
  match goal with
      | [IH: ⊢ (?s, ?t) : ?T ->
             inert _ ->
             strongly_typed _ _ -> _,
         Hi: inert _,
         Hwt: strongly_typed _ _ |- _] =>
        assert (⊢ (s, t): T) as Hs by eauto;
        specialize (IH Hs Hi Hwt) as [IH | [s' [t' Hr]]];
        eauto; inversion IH
      end.

(** ** Progress Theorem *)

(** [⊢ (s, t): T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [t] is in normal form   #<br>#
    or [exists s', t'] such that [(s, t) |-> (s', t')] *)
Theorem progress: forall s t T,
    ⊢ (s, t) : T ->
    norm_form t \/ exists s' t', (s, t) |-> (s', t').
Proof.
  introv Ht. inversion Ht as [G s' t' T' Hi Hwt HT]. subst.
  induction HT; eauto.
  - Case "trm_lambda".
    pick_fresh x.
    right. exists (s & x ~ (val_fun T t)) (trm_var (avar_f x)). auto.
  - Case "ty_all_elim".
    pose proof (canonical_forms_fun Hi Hwt HT1). destruct_all. right*.
  - Case "trm_new".
    right. pick_fresh x.
    exists (s & x ~ (val_obj T (open_defs x ds))) (trm_var (avar_f x)). auto.
  - Case "ty_new_elim".
    pose proof (canonical_forms_obj Hi Hwt HT). destruct_all. right*.
  - Case "ty_let".
    right. destruct t; try solve [solve_let_prog; trm_val_contra].
    pose proof (var_typing_implies_avar_f HT) as [x A]. subst*.
Qed.
