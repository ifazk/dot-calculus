Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions Binding GeneralToTight InvertibleTyping Narrowing
        PreciseTyping RecordAndInertTypes Subenvironments
        Substitution TightTyping Weakening CanonicalForms
        InvertibleTyping PseudoNarrowing
.

(** Infrastructure *)

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

(** Strong Typing for variables *)
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

(** Strong Typing for stores *)
Definition strong_typed (G : ctx) (s : sta) : Prop :=
  ok G /\
  ok s /\
  (dom G = dom s) /\
  (forall x,
      x \in dom G ->
      ty_val_s G s x).
Hint Unfold strong_typed.

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

(** Inductive strong_typing lemmas *)
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

Lemma strong_typed_push_fun: forall G s x T T' e,
    strong_typed G s ->
    x # G ->
    G ⊢ trm_lambda T' e : T ->
    strong_typed (G & x ~ T) (s & x ~ val_fun T' e).
Proof.
  intros. unfold strong_typed in *.
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

Lemma strong_typed_push_precise: forall G s x T v,
    strong_typed G s ->
    x # G ->
    x # s ->
    G ⊢!v v : T ->
    strong_typed (G & x ~ T) (s & x ~ v).
Proof.
  intros. inversions H2.
  - apply* strong_typed_push_fun.
  - unfold strong_typed in *.
    destruct_all; repeat_split_right; auto.
    + simpl_dom. fequal. auto.
    + intros x0 Hd.
      pose proof (dom_to_binds Hd) as [?T ?]; clear Hd.
      assert (binds x (val_obj T0 ds) (s & x ~ (val_obj T0 ds))) by auto.
      destruct (binds_push_inv H6) as [[? ?] | [? ?]]; subst.
      * apply (ty_val_obj_s H6 H7); auto.
        assert (ok (G & x ~ typ_bnd T0)) by auto.
        pick_fresh z.
        assert (z # (G & x ~ typ_bnd T0)) by auto.
        assert ((G & x ~ typ_bnd T0) & z ~ open_typ z T0 /- open_defs z ds :: open_typ z T0).
        { eapply (proj43 weaken_rules); auto. }
        assert (G & x ~ typ_bnd T0 ⊢ trm_var (avar_f x) : open_typ x T0) by auto.
        assert (z \notin fv_typ (typ_bnd T0)) by (simpl; auto).
        eapply (renaming_def _ _ H8 H9); auto.
        rewrite fv_ctx_types_push_eq; auto.
      * apply ty_val_s_push; auto.
        apply H5. eauto using binds_to_dom.
Qed.

Lemma strong_corresponding_types: forall G s x T,
    strong_typed G s ->
    binds x T G ->
    ty_val_s G s x.
Proof.
  intros. unfold strong_typed in H.
  destruct_all. apply H3.
  eauto using binds_to_dom.
Qed.

Lemma strong_canonical_forms_fun: forall G s x T U,
  inert G ->
  strong_typed G s ->
  G ⊢ trm_var (avar_f x) : typ_all T U ->
  (exists L T' t, binds x (val_fun T' t) s /\ G ⊢ T <: T' /\
  (forall y, y \notin L -> G & y ~ T ⊢ open_trm y t : open_typ y U)).
Proof.
  introv Hin Hst Hty.
  destruct (var_typ_all_to_binds Hin Hty) as [L [S [T' [BiG [Hs1 Hs2]]]]].
  pose proof (strong_corresponding_types Hst BiG).
  inversions H.
  - pose proof (binds_func BiG H0). subst T0.
    destruct (val_typ_all_to_lambda _ Hin H2) as [L' [S' [t' [Heq [Hs1' Hs2']]]]].
    exists (L \u L' \u (dom G)) S' t'. inversions Heq.
    repeat_split_right; eauto.
    intros.
    assert (HL: y \notin L) by auto.
    assert (HL': y \notin L') by auto.
    specialize (Hs2 y HL).
    specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    eapply ty_sub; eauto.
  - pose proof (binds_func BiG H0). congruence.
Qed.

Lemma strong_typed_ctx_val: forall G s x,
    strong_typed G s ->
    x \in dom G ->
    ty_val_s G s x.
Proof.
  intros.
  unfold strong_typed in *; destruct_all; auto.
Qed.

Lemma strong_typed_mu_to_new: forall G s x T,
    inert G ->
    ty_val_s G s x ->
    binds x (typ_bnd T) G ->
    exists ds, binds x (val_obj T ds) s /\
               G /- open_defs x ds :: open_typ x T.
Proof.
  introv Hi Hts Bi.
  inversions Hts.
  - pose proof (binds_func Bi H); subst T0; clear H.
    pose proof (general_to_tight_typing Hi H1).
    pose proof (tight_to_invertible_v _ Hi H).
    inversions H2. inversions H3.
  - pose proof (binds_func Bi H). inversions H1.
    exists ds; split; auto.
Qed.

Lemma strong_canonical_forms_obj: forall G s x a T,
  inert G ->
  strong_typed G s ->
  G ⊢ trm_var (avar_f x) : (typ_rcd (dec_trm a T)) ->
  (exists S ds t, binds x (val_obj S ds) s /\
                  defs_has (open_defs x ds) (def_trm a t) /\
                  G ⊢ t : T).
Proof.
  introv Hi Hst Hty.
  destruct (var_typ_rcd_to_binds Hi Hty) as [?S [?T' [?H [?H ?H]]]].
  pose proof (strong_corresponding_types Hst H) as Hts.
  destruct (strong_typed_mu_to_new Hi Hts H) as [?ds [?Bis ?]].
  pose proof (record_has_ty_defs H2 H0) as [?d [? ?]].
  inversions H4.
  exists S ds t. repeat_split_right; eauto.
Qed.
