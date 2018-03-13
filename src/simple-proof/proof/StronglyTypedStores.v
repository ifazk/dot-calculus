Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import
        LibExtra Definitions Binding
        PreciseTyping Substitution Weakening.

(** * Strongly Typed Stores *)

(** The operational semantics is defined in terms of pairs [(s, t)], where
    [s] is a store and [t] is a term.
    Given a typing [G ⊢ (s, t): T], [strongly_typed] establishes a correspondence
    between [G] and the store [s].

    We say that [s] is strongly-typed with respect to [G] if
    - [G = {(xi mapsto Ti) | i = 1, ..., n}]
    - [s = {(xi mapsto vi) | i = 1, ..., n}]
    - If [vi] is a function then [G ⊢ vi: Ti]
    - If [vi = nu(T)ds] is an object then [Ti = mu(... /\ D /\ ...)] and
      [G ⊢ ds^xi :: (... /\ D /\ ...)^xi].

    We say that [s] is well-typed with respect to [G], denoted as [s: G]. *)

(** ** Strong Typing for Locations *)

(** We first define a strong typing relation for a single location. This
    definition will later be lifted to entire contexts and stores. *)

(** We say that a location [l] is strongly bound in the context [G] and store
    [s], denoted [s(l):G(l)] if there exists a [T] such t
    - if [s(x)] is a function [lambda(y: T)t] then [G ⊢ lambda(y: T)t : T]
    - if [s(x)] is an object [nu(y: U)ds] for some [U], then [T = mu(U)] and
      [G ⊢ ds^x :: U^x] *)

Inductive ty_val_s : ctx -> sto -> var -> Prop :=
| ty_val_fun_s : forall G s x S t T,
    binds x T G ->
    binds x (val_fun S t) s ->
    G ⊢ trm_lambda S t : T ->
    ty_val_s G s x
| ty_val_obj_s : forall G s x U ds T,
    binds x T G ->
    binds x (val_obj U (open_defs x ds)) s ->
    T = typ_bnd U ->
    G /- open_defs x ds :: open_typ x U ->
    ty_val_s G s x.
Hint Constructors ty_val_s.

(** A strongly bound location stays strongly bound in extended stores and contexts *)
Lemma ty_val_s_push: forall G s x y T v,
    ty_val_s G s x ->
    ok G ->
    y # G ->
    ty_val_s (G & y ~ T) (s & y ~ v) x.
Proof.
  intros.
  assert (x \notin \{ y }).
  { apply notin_singleton.
    intros ?H. subst x.
    inversions H; eauto using binds_fresh_inv. }
  induction H.
  - assert (G & y ~ T ⊢ trm_lambda S t : T0) by eauto using weaken_ty_trm.
    eauto.
  - assert (G & y ~ T /- open_defs x ds :: open_typ x U) by eauto using weaken_ty_defs.
    eapply ty_val_obj_s; eauto.
Qed.

(** ** Strong Typing for Stores *)

(** [s:G] if [s] and [G] have the same domain and every location in [s] is
    strongly bound *)
Definition strongly_typed (G : ctx) (s : sto) : Prop :=
  ok G /\
  ok s /\
  (dom G = dom s) /\
  (forall x,
      x \in dom G ->
      ty_val_s G s x).
Hint Unfold strongly_typed.

(** ** Simple lemmas for Stongly Typed Stores *)

(** If [s: G], the variables in the domain of [s] are distinct. *)
Lemma strongly_typed_to_ok_G: forall s G,
    strongly_typed G s -> ok G.
Proof.
  intros. destruct H as [? [? ?]]. auto.
Qed.
Hint Resolve strongly_typed_to_ok_G.

Lemma strongly_typed_to_ok_s: forall s G,
    strongly_typed G s -> ok s.
Proof.
  intros. destruct H as [? [? ?]]. auto.
Qed.
Hint Resolve strongly_typed_to_ok_s.

(** [s: G]       #<br>#
    [x ∉ dom(s)] #<br>#
    [――――――――――] #<br>#
    [x ∉ dom(G)] *)
Lemma strongly_typed_notin_dom: forall G s x,
    strongly_typed G s ->
    x # s ->
    x # G.
Proof.
  introv Hwt. destruct Hwt as [? [? [?Hdom ?]]].
  unfold notin. rewrite Hdom.
  auto.
Qed.

(** ** Inductive lemmas for Strongly Typed Stores *)

Lemma strongly_typed_empty:
    strongly_typed empty empty.
Proof.
  repeat split; auto.
  - simpl_dom; auto.
  - introv B. simpl_dom.
    rewrite in_empty in B.
    destruct B.
Qed.
Hint Resolve strongly_typed_empty.

Lemma strongly_typed_push_fun: forall G s x T T' e,
    strongly_typed G s ->
    x # G ->
    G ⊢ trm_lambda T' e : T ->
    strongly_typed (G & x ~ T) (s & x ~ val_fun T' e).
Proof.
  intros. unfold strongly_typed in *.
  destruct_all. repeat_split_right; auto.
  - apply ok_push; try assumption.
    rewrite <- H3. auto.
  - simpl_dom. fequal. auto.
  - intros x0 Hd.
    pose proof (dom_to_binds Hd) as [?T ?]; clear Hd.
    assert (binds x (val_fun T' e) (s & x ~ (val_fun T' e))) by auto.
    destruct (binds_push_inv H5) as [[? ?] | [? ?]]; subst.
    + apply (ty_val_fun_s H5 H6).
      apply weaken_ty_trm; auto.
    + apply ty_val_s_push; auto.
      apply H4. eauto using binds_to_dom.
Qed.

Lemma strongly_typed_push_precise: forall G s x T v,
    strongly_typed G s ->
    x # G ->
    x # s ->
    G ⊢!v v ^^ x : T ->
    strongly_typed (G & x ~ T) (s & x ~ v).
Proof.
  intros. inversions H2.
  - apply* strongly_typed_push_fun.
  - unfold strongly_typed in *.
    destruct_all; repeat_split_right; auto.
    + simpl_dom. fequal. auto.
    + intros x0 Hd.
      pose proof (dom_to_binds Hd) as [?T ?]; clear Hd.
      assert (binds x (val_obj T0 (open_defs x ds)) (s & x ~ (val_obj T0 (open_defs x ds)))) by auto.
      destruct (binds_push_inv H8) as [[? ?] | [? ?]]; subst.
      * apply (ty_val_obj_s _ H8 H9); auto.
        assert (ok (G & x ~ typ_bnd T0)) by auto.
        pick_fresh z.
        assert (z # (G & x ~ typ_bnd T0)) by auto.
        assert ((G & x ~ typ_bnd T0) & z ~ open_typ z T0 /- open_defs z ds :: open_typ z T0).
        { eapply (proj43 weaken_rules); auto. }
        assert (G & x ~ typ_bnd T0 ⊢ trm_var (avar_f x) : open_typ x T0) by auto.
        assert (z \notin fv_typ (typ_bnd T0)) by (simpl; auto).
        eapply (renaming_def _ _ H10 H11); auto.
        rewrite fv_ctx_types_push_eq; auto.
      * apply ty_val_s_push; eauto using binds_to_dom.
Qed.

(** ** Inversion lemmas for [s:G] *)

(** [s:G] implies every location is strongly typed *)

(** [s: G]              #<br>#
    [G(l) = T]          #<br>#
    [―――――――――――――]     #<br>#
    [s(l):G(l)]         *)
Lemma corresponding_types: forall G s x T,
    strongly_typed G s ->
    binds x T G ->
    ty_val_s G s x.
Proof.
  intros. unfold strongly_typed in H.
  destruct_all. apply H3.
  eauto using binds_to_dom.
Qed.

(** [s: G]              #<br>#
    [s(l) = v]          #<br>#
    [―――――――――――――]     #<br>#
    [s(l):G(l)]         *)
Lemma corresponding_types_s: forall G s x v,
    strongly_typed G s ->
    binds x v s ->
    ty_val_s G s x.
Proof.
  intros. unfold strongly_typed in H.
  destruct_all. apply H3.
  rewrite H2. eauto using binds_to_dom.
Qed.
