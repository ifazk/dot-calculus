Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Binding CanonicalForms Definitions GeneralToTight InvertibleTyping Narrowing
            OperationalSemantics PreciseTyping RecordAndInertTypes Substitution Weakening.

(** The typing of a term with a stack *)
Inductive sta_trm_typ : sta * trm -> typ -> Prop :=
| sta_trm_typ_c : forall G s t T,
    inert G ->
    well_typed G s ->
    G ⊢ t : T ->
    sta_trm_typ (s, t) T.

Hint Constructors sta_trm_typ.

Notation "'⊢' t ':' T" := (sta_trm_typ t T) (at level 40, t at level 59).

(** * Preservation *)

(** If a value [v] has type [T], then [v] has a precise type [T']
    that is a subtype of [T].
    This lemma corresponds to Lemma 3.15 in the paper. *)
Lemma val_typing: forall G v T,
  G ⊢ trm_val v : T ->
  exists T', G ⊢!v v : T' /\
        G ⊢ T' <: T.
Proof.
  intros G v T H. destruct v; simpl; dependent induction H; eauto;
  destruct (IHty_trm _ _ eq_refl); destruct_all; eauto.
Qed.

(** Helper tactics for proving Preservation *)

Ltac binds_eq :=
  match goal with
  | [Hb1: binds ?x _ ?G,
     Hb2: binds ?x _ ?G |- _] =>
     apply (binds_func Hb1) in Hb2; inversions Hb2
  end.

Ltac invert_red :=
  match goal with
  | [Hr: (_, _) |-> (_, _) |- _] => inversions Hr
  end.

Ltac red_trm_to_val :=
  match goal with
  | [ H : (_, trm_lambda ?T ?e) |-> _ |- _ ] =>
    remember (val_fun T e);
    assert (trm_val (val_fun T e) = trm_lambda T e) by auto
  | [ H : (_, trm_new ?T ?ds) |-> _ |- _ ] =>
    assert (trm_val (val_obj T ds) = trm_new T ds) by auto
  | _ => idtac
  end.

Ltac trm_val_contra :=
  match goal with
  | [ H : trm_val ?v = _ |- _ ] =>
      try solve [induction v; simpl in *; congruence]
  | _ => idtac
  end.

Ltac solve_IH :=
  match goal with
  | [IH: well_typed _ _ ->
         inert _ ->
         forall t', (_, _) |-> (_, _) -> _,
       Wf: well_typed _ _,
       In: inert _,
       Hr: (_, _) |-> (_, ?t') |- _] =>
    specialize (IH Wf In t' Hr); destruct_all
  end;
  match goal with
  | [Hi: _ & ?G' ⊢ _ : _ |- _] =>
    exists G'; repeat_split_right; auto
  | [Hi: ty_trm_aux (_ & ?G') _ _ |- _] =>
    exists G'; repeat_split_right; auto
  end.

Ltac solve_let :=
  invert_red; trm_val_contra; solve_IH;
  apply_fresh ty_aux_let as z; eauto; apply* weaken_rules.

Lemma sel_to_var_typ: forall G x a T,
  G ⊢ trm_sel (avar_f x) a : T ->
  G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T).
Proof.
  introv Hty.
  dependent induction Hty; auto.
  eapply ty_sub; eauto.
Qed.

Lemma record_has_typing: forall G x T d,
  G ⊢ trm_var (avar_f x) : T ->
  record_has T d ->
  G ⊢ trm_var (avar_f x) : typ_rcd d.
Proof.
  introv Ht Hr.
  dependent induction Hr; eauto.
Qed.

Lemma var_aux_to_gen : forall G y T,
  ty_trm_aux G (trm_var (avar_f y)) T ->
  G ⊢ (trm_var (avar_f y)) : T.
Proof.
  introv Ht.
  dependent induction Ht; eauto.
Qed.

Lemma defs_update_hasnt : forall ds l a t,
    defs_hasnt ds l ->
    defs_hasnt (defs_update ds a t) l.
Proof.
  induction ds.
  - intros.
    simpl; auto.
  - intros.
    unfold defs_hasnt in *.
    simpl in *.
    cases_if.
    specialize (IHds l a t H).
    destruct d.
    + simpl in *. cases_if. auto.
    + cases_if. simpl in *; cases_if; auto.
      simpl in *; cases_if; auto.
Qed.

Lemma defs_update_typing : forall T a y ds G D,
  record_has T (dec_trm a D) ->
  G /- ds :: T ->
  G ⊢ trm_var (avar_f y) : D ->
  G /- (defs_update ds a (trm_var (avar_f y))) :: T.
Proof.
  induction T; introv Hrh Hds Hty;
  try solve [inversion Hrh].
  - inversions Hrh.
    inversions Hds.
    inversions H2.
    simpl. cases_if.
    auto.
  - inversions Hds.
    inversions H4.
    + simpl.
      apply ty_defs_cons; auto.
      inversions Hrh; eauto.
      inversion H3.
      eauto using defs_update_hasnt.
    + pose proof (ty_defs_record_type H1) as [?ls ?].
      simpl in *. cases_if.
      { inversions Hrh.
        pose proof (record_typ_has_label_in H0 H6).
        pose proof (hasnt_notin H1 H0 H5).
        simpl in H2.
        contradiction.
        inversions H6.
        pose proof (IHT2 a0 y (defs_cons defs_nil (def_trm a0 (trm_var (avar_f y)))) G D
                         (rh_one _)
                         (ty_defs_one (ty_def_trm _ Hty))
                         Hty
                   ).
        simpl in H2; cases_if.
        inversions H2.
        apply ty_defs_cons; auto.
      }
      { apply ty_defs_cons.
        eapply IHT1; eauto.
        inversion Hrh; eauto.
        inversion H6. exfalso; auto.
        eauto.
        eauto using defs_update_hasnt.
      }
Qed.

Lemma binds_middle: forall A (E : env A) x v,
    binds x v E ->
    exists E1 E2, E = E1 & x ~ v & E2.
Proof.
  intros A E. induction E using env_ind.
  - intros. exfalso. apply (binds_empty_inv H).
  - introv Bis. apply binds_push_inv in Bis.
    destruct Bis as [[? ?] | [? ?]].
    + subst. exists E (@empty A).
      rewrite concat_empty_r; reflexivity.
    + pose proof (IHE _ _ H0) as [?E [?E ?]].
      subst E. exists E0 (E1 & x ~ v).
      rewrite concat_assoc; auto.
Qed.

Lemma defs_update_val_typing : forall L ds G a S T x y ds',
    ok G ->
    binds x (typ_bnd S) G ->
    (forall y, y \notin L -> G & (y ~ open_typ y S) /- open_defs y ds :: open_typ y S) ->
    record_has (open_typ x S) (dec_trm a T) ->
    defs_update (open_defs x ds) a (trm_var (avar_f y)) = open_defs x ds' ->
    G ⊢ trm_var (avar_f y) : T ->
    G ⊢ trm_val (val_obj S ds') : typ_bnd S.
Proof.
  intros.
  pick_fresh z.
  assert (z \notin (fv_ctx_types G \u fv_defs ds \u fv_typ S)) by auto.
  assert (z \notin L) by auto.
  assert (G & z ~ open_typ z S /- open_defs z ds :: open_typ z S) by eauto.
  assert (z # G) by auto.
  assert (G ⊢ trm_var (avar_f x) : open_typ x S) by auto.
  assert (Hdt: G /- open_defs x ds :: open_typ x S) by eauto using renaming_def.
  clear H9 H8 H7 H6 H5.
  pose proof (defs_update_typing H2 Hdt H4).
  rewrite H3 in H5.
Qed.

(** [s: G]                  #<br>#
    [inert [G]              #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [G ⊢ t: T]              #<br>#
    [―――――――――――――――――――]   #<br>#
    [exists G', inert G']        #<br>#
    [s': G, G']             #<br>#
    [G, G' ⊢ t': T]         *)
Lemma preservation_helper: forall G s t s' t' T,
    well_typed G s ->
    inert G ->
    (s, t) |-> (s', t') ->
    ty_trm_aux G t T ->
    exists G', inert G' /\
          well_typed (G & G') s' /\
          ty_trm_aux (G & G') t' T.
Proof.
  introv Hwf Hin Hred Ht. gen t'.
  induction Ht as [? ? ? Ht | ? ? ? ? Ht | ? ? ? ? ? ? BiG Hr Ht IHt | ? ? ? ? ? ? Htt Htu | ? ? ? ? Ht Hsub].
  induction Ht; intros; try solve [invert_red; trm_val_contra].
  - Case "ty_all_intro".
    red_trm_to_val.
    rewrite <- H1 in Hred.
    invert_red.
      match goal with
        | [Hn: ?x # ?s |- _] =>
          pose proof (well_typed_notin_dom Hwf Hn) as Hng
      end.
      assert (Ht: G ⊢ trm_lambda T t : typ_all T U) by eauto.
      rewrite <- H4 in Ht.
      pose proof (val_typing _ Ht) as [V [Hv Hs]].
      exists (x ~ V). repeat_split_right.
      ** rewrite <- concat_empty_l. constructor~. apply (precise_inert_typ Hv).
      ** apply~ well_typed_push. apply (precise_to_general_v Hv).
      ** assert (G & x ~ V ⊢ trm_var (avar_f x) : V) by auto.
         apply ty_aux_gen.
         eapply ty_sub. apply H2. apply* weaken_subtyp.
  - Case "ty_all_elim".
    match goal with
    | [Hx: _ ⊢ trm_var (avar_f _) : typ_all _ _ |- _] =>
        pose proof (canonical_forms_fun Hin Hwf Hx) as [L [T' [t [Bis [Hsub Hty]]]]];
          inversions Hred; trm_val_contra;
          binds_eq
    end.
    exists (@empty typ). rewrite concat_empty_r. repeat_split_right; auto.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    apply ty_aux_gen.
    eapply renaming_typ; eauto.
  - Case "ty_new_intro".
    red_trm_to_val.
    rewrite <- H0 in Hred.
    invert_red.
      match goal with
        | [Hn: ?x # ?s |- _] =>
          pose proof (well_typed_notin_dom Hwf Hn) as Hng
      end.
      assert (Ht: G ⊢ trm_new T ds : typ_bnd T) by eauto.
      rewrite <- H3 in Ht.
      pose proof (val_typing _ Ht) as [V [Hv Hs]].
      exists (x ~ V). repeat_split_right.
      ** rewrite <- concat_empty_l. constructor~. apply (precise_inert_typ Hv).
      ** apply~ well_typed_push. apply (precise_to_general_v Hv).
      ** assert (G & x ~ V ⊢ trm_var (avar_f x) : V) by auto.
         apply ty_aux_gen.
         eapply ty_sub. apply H1. apply* weaken_subtyp.
  - Case "ty_new_elim".
    pose proof (canonical_forms_obj Hin Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    invert_red; trm_val_contra. binds_eq.
    exists (@empty typ). rewrite concat_empty_r. repeat_split_right; auto.
  - Case "ty_let".
    destruct t; try solve [solve_let].
    + SCase "[t = (let x = a in u)] where a is a variable".
      repeat invert_red; trm_val_contra.
      exists (@empty typ). rewrite concat_empty_r. repeat_split_right; auto.
      apply ty_aux_gen.
      apply* renaming_fresh.
  - Case "ty_sub".
    solve_IH.
    eapply ty_aux_sub.
    apply H2.
    eapply weaken_subtyp; eauto.
  - Case "ty_aux_force".
    intros.
    exists (@empty typ). rewrite concat_empty_r.
    split; auto.
    invert_red; trm_val_contra.
    + split; auto.
      pose proof (sel_to_var_typ Ht).
      pose proof (canonical_forms_obj Hin Hwf H) as [S [ds' [t [Bis [Has Ty]]]]].
      pose proof (binds_func H1 Bis).
      injection H0; intros; subst.
      pose proof (defs_has_inv H5 Has); subst t.
      apply ty_aux_gen; auto.
    + split; auto.
      pose proof (sel_to_var_typ Ht).
      pose proof (var_typ_rcd_to_binds Hin H) as [?S [?T [? [? ?]]]].
      assert (G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T1)) by eauto using record_has_typing.
      pose proof (canonical_forms_obj Hin Hwf H4) as [?S [ds' [t' [Bis [Has Ty]]]]].
      pose proof (binds_func H3 Bis).
      injection H7; intros; subst; clear H7.
      pose proof (defs_has_inv H5 Has); subst t'.
      eapply ty_aux_sub.
      eapply ty_aux_force_assgn. all: eauto.
  - Case "ty_aux_force_assgn".
    intros.
    destruct t.
    + invert_red; trm_val_contra.
      invert_red; trm_val_contra.
      exists (@empty typ). rewrite concat_empty_r.
      repeat_split_right; auto.
      split; auto.
      destruct H0 as [? [? [? [? [?T [?ds [?ds [? [? ?]]]]]]]]].
      split; auto.
      split.
      { destruct Hwf. destruct_all; congruence. }
      intros.
      destruct (classicT (x = x0)).
      * subst x0. pose proof (binds_func H6 BiG).
        subst T1.
        pose proof (binds_func H4 H7); subst v; clear H7.
        assert (G ⊢ trm_val (val_obj T0 ds) : typ_bnd S) by (unfold well_typed in *; destruct_all; eauto).
        assert (G ⊢ trm_var (avar_f y) : T) by auto using var_aux_to_gen.

        injection H10; intros; subst T0 ds'. clear H10 H5.
        pose proof (binds_func H9 H6); subst v.
      * assert (binds x0 v s) by (apply H2; auto).
        destruct Hwf as [? [? [? ?Htv]]].
        apply* Htv.




      * subst x0.


      assert (Htx: G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T)) by eauto using record_has_typing.



      pose proof (sel_to_var_typ Ht).
      pose proof (var_typ_rcd_to_binds Hin H) as [?S [?T [? [? ?]]]].
      assert (G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T1)) by eauto using record_has_typing.
      pose proof (canonical_forms_obj Hin Hwf H4) as [?S [ds' [t' [Bis [Has Ty]]]]].
      pose proof (binds_func H3 Bis).
      injection H7; intros; subst; clear H7.
      pose proof (defs_has_inv H5 Has); subst t'.
      eapply ty_aux_sub.
      eapply ty_aux_force_assgn. all: eauto.





      pose proof (sel_to_var_typ Ht).
      pose proof (var_typ_rcd_to_binds Hin H) as [?S [?T [? [? ?]]]].
      pose proof (canonical_forms_obj Hin Hwf H) as [?S [ds' [t [Bis [Has Ty]]]]].
      split; auto.
      split; try apply H0.
      pose proof H0 as [? [? [? [? [?T [?ds [?ds [? [? ?]]]]]]]]].
      split.
      { destruct Hwf. destruct_all. congruence. }
      intros.
      destruct (classicT (x = x0)).
      * subst x0. pose proof (binds_func H5 Bis).
        injection H10; intros; subst T0 ds'. clear H10 H5.
        pose proof (binds_func H9 H6); subst v.

      SearchAbout (binds _ _ _).
      Check binds_push_eq_inv.



      pose proof (binds_func H1 Bis).
      injection H0; intros; subst.
      pose proof (defs_has_inv H5 Has); subst t.
      apply ty_aux_gen; auto.
    +

Ltac solve_IH_assgn :=
  match goal with
  | [Wf: well_typed _ _,
     In: inert _,
     IH: well_typed _ _ ->
         inert _ ->
         forall t', (_, _) |-> (_, _) -> _,
     Hr: (_, _) |-> (_, ?t') |- _] =>
    specialize (IH Wf In t' Hr); destruct_all
  end;
  match goal with
  | [Hi: _ & ?G' ⊢ _ : _ |- _] =>
    exists G'; repeat_split_right; auto
  | [Hi: ty_trm_aux (_ & ?G') _ _ |- _] =>
    exists G'; repeat_split_right; auto
  end.

Ltac solve_force_assgn :=
  invert_red; trm_val_contra; solve_IH_assgn;
  apply ty_aux_force_assgn; eauto; apply* weaken_rules || apply* weaken_ty_aux.



  invert_red; trm_val_contra.

 specialize (IHHta Hwf Hin t0' H0); destruct_all.

  match goal with
  | [Wf: well_typed _ _,
     In: inert _,
     IH: well_typed _ _ ->
         inert _ ->
         forall t', (_, _) |-> (_, _) -> _,
     Hr: (_, _) |-> (_, ?t') |- _] =>
    (* specialize (IH Wf In t' Hr); destruct_all *)
    idtac
  end.

  solve_IH_assgn.
  apply ty_aux_force_assgn; eauto; apply* weaken_rules || apply* weaken_ty_aux.


  apply ty_aux_force_assgn; eauto; apply* weaken_rules || apply* weaken_ty_aux.

  invert_red; trm_val_contra; solve_IH;
  apply ty_aux_force_assgn; eauto; apply* weaken_rules || apply* weaken_ty_aux.
    destruct t; try solve [solve_let].
    invert_red.

    repeat_split_right; auto.
Qed.
  Focus 2. intros. exists (@empty typ); rewrite concat_empty_r; repeat_split_right; auto.
  invert_red; auto. induction v; simpl in *; congruence. apply ty_aux_gen.

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
  apply sta_trm_typ_c with (G:=G & G'); auto. apply* inert_concat.
Qed.

(** * Progress *)

(** Helper tactic for proving progress *)
Ltac solve_let_prog :=
  match goal with
      | [IH: ⊢ (?s, ?t) : ?T ->
             inert _ ->
             well_typed _ _ -> _,
         Hi: inert _,
         Hwt: well_typed _ _ |- _] =>
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
    assert (trm_lambda T t = trm_val (val_fun T t)) by auto.
    rewrite H1. pick_fresh x.
    right. exists (s & x ~ (val_fun T t)) (trm_var (avar_f x)). auto.
  - Case "ty_all_elim".
    pose proof (canonical_forms_fun Hi Hwt HT1). destruct_all. right*.
  - Case "trm_new".
    right. assert (trm_new T ds = trm_val (val_obj T ds)) by auto.
    rewrite H0. pick_fresh x.
    exists (s & x ~ (val_obj T ds)) (trm_var (avar_f x)). auto.
  - Case "ty_new_elim".
    pose proof (canonical_forms_obj Hi Hwt HT). destruct_all. right*.
  - Case "ty_let".
    right. destruct t; try solve [solve_let_prog; trm_val_contra].
    pose proof (var_typing_implies_avar_f HT) as [x A]. subst*.
Qed.
