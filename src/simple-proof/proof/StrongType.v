Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions Binding GeneralToTight InvertibleTyping Narrowing
        PreciseTyping RecordAndInertTypes Subenvironments
        Substitution TightTyping Weakening CanonicalForms
        InvertibleTyping PseudoNarrowing
.

Inductive ty_val_s : ctx -> sta -> var -> Prop :=
| ty_val_fun_s : forall G s x S t T,
    binds x T G ->
    binds x (val_fun S t) s ->
    G ⊢ trm_val (val_fun S t) : T ->
    ty_val_s G s x
| ty_val_obj_s : forall G s x U ds T,
    binds x T G ->
    binds x (val_obj U ds) s ->
    T = typ_bnd U ->
    G /- open_defs x ds :: open_typ x U ->
    ty_val_s G s x.
Hint Constructors ty_val_s.

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
  - assert (G & y ~ T ⊢ trm_val (val_fun S t) : T0) by eauto using weaken_ty_trm.
    eauto.
  - assert (G & y ~ T /- open_defs x ds :: open_typ x U) by eauto using weaken_ty_defs.
    eapply ty_val_obj_s; eauto.
Qed.

Definition strong_typed (G : ctx) (s : sta) : Prop :=
  ok G /\
  ok s /\
  (dom G = dom s) /\
  (forall x,
      x \in dom G ->
      ty_val_s G s x).
Hint Unfold strong_typed.

Definition var_decide (x y : var) : {x = y} + {x <> y} :=
  LibReflect.decidable_sumbool (LibReflect.comparable x y).

Lemma dom_to_binds : forall A (E : env A) x,
    x \in dom E ->
    exists v, binds x v E.
Proof.
  induction E using env_ind.
  - intros; false. simpl_dom.
    rewrite in_empty in H; auto.
  - intros.
    destruct (var_decide x0 x) as [?H | ?H].
    + subst x0; exists v; auto.
    + rewrite dom_concat, in_union in H.
      destruct H.
      * apply IHE in H.
        destruct H as [?v ?H].
        exists v0; apply binds_concat_left; auto.
      * false. simpl_dom; rewrite in_singleton in H.
        auto.
Qed.

Lemma binds_to_dom : forall A (E : env A) x v,
    binds x v E ->
    x \in dom E.
Proof.
  introv H. induction E using env_ind.
  - exfalso; eauto using binds_empty_inv.
  - destruct (binds_push_inv H) as [[? ?] | [? ?]]; subst; simpl_dom; rewrite in_union.
    + left. auto using in_singleton_self.
    + right. auto.
Qed.

Lemma strong_typed_to_ok_G: forall s G,
    strong_typed G s -> ok G.
Proof.
  intros. destruct H as [? [? ?]]. auto.
Qed.
Hint Resolve strong_typed_to_ok_G.

Lemma strong_typed_to_ok_s: forall s G,
    strong_typed G s -> ok s.
Proof.
  intros. destruct H as [? [? ?]]. auto.
Qed.
Hint Resolve strong_typed_to_ok_s.

Lemma strong_typed_notin_dom: forall G s x,
    strong_typed G s ->
    x # s ->
    x # G.
Proof.
  introv Hwt. destruct Hwt as [? [? [?Hdom ?]]].
  unfold notin. rewrite Hdom.
  auto.
Qed.

Lemma strong_typed_empty:
    strong_typed empty empty.
Proof.
  repeat split; auto.
  - simpl_dom; auto.
  - introv B. simpl_dom.
    rewrite in_empty in B.
    destruct B.
Qed.
Hint Resolve strong_typed_empty.

Lemma strong_typed_push: forall G s x T v,
    strong_typed G s ->
    x # G ->
    x # s ->
    G ⊢!v v : T ->
    strong_typed (G & x ~ T) (s & x ~ v).
Proof.
  intros. unfold strong_typed in *.
  destruct_all.
  repeat_split_right; auto.
  - simpl_dom. fequal. auto.
  - intros x0 Hd.
    pose proof (dom_to_binds Hd) as [?T ?]; clear Hd.
    assert (binds x v (s & x ~ v)) by auto.
    destruct (binds_push_inv H6) as [[? ?] | [? ?]]; subst.
    + destruct H2.
      * apply (ty_val_fun_s H6 H7).
        apply weaken_ty_trm; auto.
        eapply ty_all_intro; apply H2.
      * apply (ty_val_obj_s H6 H7); auto.
        assert (ok (G & x ~ typ_bnd T)) by auto.
        pick_fresh z.
        assert (z # (G & x ~ typ_bnd T)) by auto.
        assert ((G & x ~ typ_bnd T) & z ~ open_typ z T /- open_defs z ds :: open_typ z T).
        { eapply (proj43 weaken_rules); auto. }
        assert (G & x ~ typ_bnd T ⊢ trm_var (avar_f x) : open_typ x T) by auto.
        assert (z \notin fv_typ (typ_bnd T)) by (simpl; auto).
        eapply (renaming_def _ _ H8 H9); auto.
        rewrite fv_ctx_types_push_eq; auto.
    + apply ty_val_s_push; auto.
      apply H5. eauto using binds_to_dom.
Qed.
