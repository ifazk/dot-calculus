Set Implicit Arguments.

Require Import LibMap LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Some_lemmas.
Require Import Inert_types.
Require Import General_to_tight.
Require Import Invertible_typing.
Require Import Narrowing.

(* ###################################################################### *)
(** ** Well-formed stack *)

Lemma wf_to_ok_s: forall G S sta sto,
    well_formed G S sta sto -> ok sta.
Proof. intros. induction H; jauto. Qed.

Lemma wf_to_ok_G: forall G S sta sto,
    well_formed G S sta sto -> ok G.
Proof. intros. induction H; jauto. Qed.

Lemma wf_to_ok_S: forall G S sta sto,
    well_formed G S sta sto -> ok S.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_to_ok_s wf_to_ok_G wf_to_ok_S.

Lemma wf_stack_to_ok_s: forall s G S,
    G, S ~~ s -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_stack_to_ok_G: forall s G S,
    G, S ~~ s -> ok G.
Proof. intros. induction H; jauto. Qed.

Lemma wf_stack_to_ok_S: forall s G S,
    G, S ~~ s -> ok S.
Proof. intros. induction H; jauto. Qed.

Lemma wt_store_to_ok_S: forall s G S,
    G, S |~ s -> ok S.
Proof.
  introv Wt. induction Wt; auto.
Qed.

Lemma wt_store_to_ok_G: forall s G S,
    G, S |~ s -> ok G.
Proof.
  introv Wt. induction Wt; auto.
Qed.

Hint Resolve wf_stack_to_ok_s wf_stack_to_ok_G wf_stack_to_ok_S wt_store_to_ok_S wt_store_to_ok_G.

Lemma wt_in_dom: forall G S sto l,
  G, S |~ sto ->
  l \in dom S ->
  index sto l.
Proof.
  introv Wt. gen l. induction Wt; intros.
  - rewrite dom_empty in H. rewrite in_empty in H. false.
  - lets Hind: (IHWt l0 H1).
    lets Hinh: (prove_Inhab x).
    pose proof (classicT (l = l0)) as [H' | H']; unfolds store, addr.
    * pose proof (indom_update sto l l0 (Some x)). 
      rewrite index_def. rewrite H2. left. rewrite H'. reflexivity. 
    * pose proof (indom_update sto l l0 (Some x)). 
      rewrite index_def. rewrite H2. right. assumption. 
  - lets Hinh: (prove_Inhab (Some x)).
    pose proof (classicT (l = l0)) as [H' | H']; unfolds store, addr.
    * rewrite index_def. rewrite indom_update. left. rewrite H'. reflexivity. assumption.
    * rewrite index_def. rewrite indom_update. right.
      assert (l0 \in dom S). {
        simpl_dom. rewrite in_union in H1. destruct H1.
        + rewrite in_singleton in H1. subst. false H'. reflexivity.
        + assumption.
      }
      lets Hin: (IHWt l0 H2). assumption. assumption.
  - apply IHWt in H0. assumption.
Qed.

Lemma wf_notin_dom: forall G S sta sto l,
  well_formed G S sta sto ->
  l # S ->
  l \notindom sto.
Proof.
  introv Hwf H. induction Hwf.
  - unfold store. rewrite LibMap.dom_empty. auto.
  - apply* IHHwf. 
  - apply* IHHwf. 
  - destruct (classicT (l = l0)).
    + subst. false (fresh_push_eq_inv H). 
    + assert (HS: l # S) by auto.
      specialize (IHHwf HS). unfold LibBag.notin in *.
      unfold not. intros. 
      destruct (indom_update_inv H1); false*.
  - destruct (classicT (l = l0)).
    + subst. false (binds_fresh_inv H0 H).
    + specialize (IHHwf H). unfold LibBag.notin in *.
      unfold not. intros. 
      destruct (indom_update_inv H2); false*.
Qed.

Lemma invertible_val_to_precise_rec: forall G S v T,
    G, S |-##v v : typ_bnd T ->
    G, S |-! trm_val v : typ_bnd T.
Proof.
  introv Ht.
  inversions Ht. assumption.
Qed.

Lemma invertible_val_to_precise_lambda: forall G S v V T,
    G, S |-##v v : typ_all V T ->
    inert G ->
    exists L V' T',
      G, S |-! trm_val v : typ_all V' T' /\
      G, S |- V <: V' /\
      (forall y, y \notin L ->
            G & y ~ V, S |- open_typ y T' <: open_typ y T).
Proof.
  introv Ht Hg. dependent induction Ht.
  - exists (dom G) V T. split*.
  - destruct (IHHt V0 T0 eq_refl Hg) as [L' [V1 [T1 [Hp [Hvv Hvt]]]]].
    exists (L \u L' \u dom G) V1 T1. split. assumption. split. apply subtyp_trans with (T:=V0).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ V)) as Hok. {
      apply* ok_push. apply* inert_ok.
    }
    apply subtyp_trans with (T:=open_typ y T0).
    eapply narrow_subtyping. apply* Hvt. apply subenv_last. apply* tight_to_general.
    assumption. assumption.
    apply* H0.
Qed.

(* Lemma invertible_val_to_precise_ref: forall G S v T, *)
(*     G, S |-##v v : typ_ref T -> *)
(*     exists T', *)
(*       G, S |-! trm_val v : typ_ref T' /\ *)
(*       G, S |- T' <: T /\ *)
(*       G, S |- T <: T'. *)
(* Proof. *)
(*   introv Ht. dependent induction Ht. *)
(*   - exists* T.  *)
(*   - destruct (IHHt T0 eq_refl) as [T' [Hty [Hs1 Hs2]]]. exists T'. repeat split.  *)
(*     + assumption. *)
(*     + apply subtyp_trans with (T:=T0); auto. *)
(*       apply (proj22 tight_to_general); auto. *)
(*     + apply subtyp_trans with (T:=T0); auto. *)
(*       apply (proj22 tight_to_general); auto. *)
(* Qed. *)

Lemma invertible_val_to_precise_nref: forall G S v T,
    G, S |-##v v : typ_nref T ->
    exists T',
      G, S |-! trm_val v : typ_nref T' /\
      G, S |- T' <: T /\
      G, S |- T <: T'.
Proof.
  introv Ht. dependent induction Ht.
  - exists* T. 
  - destruct (IHHt T0 eq_refl) as [T' [Hty [Hs1 Hs2]]]. exists T'. repeat split. 
    + assumption.
    + apply subtyp_trans with (T:=T0); auto.
      apply (proj22 tight_to_general); auto.
    + apply subtyp_trans with (T:=T0); auto.
      apply (proj22 tight_to_general); auto.
  (* - apply invertible_val_to_precise_ref in Ht. *)
  (*   destruct Ht as [T' [Ht [Hs1 Hs2]]]. *)
  (*   inversions Ht. *)
Qed.

Lemma precise_forall_inv : forall G S v V T,
    G, S |-! trm_val v : typ_all V T ->
    exists t,
      v = val_lambda V t.
Proof.
  introv Ht. inversions Ht. exists* t.
Qed.


Lemma precise_bnd_inv : forall G S v T,
    G, S |-! trm_val v : typ_bnd T ->
    exists ds,
      v = val_new T ds.
Proof.
  introv Ht. inversions Ht. exists* ds.
Qed.

Lemma precise_nref_inv : forall G S v T,
    G, S |-! trm_val v : typ_nref T ->
    exists l,
      v = val_loc l.
Proof.
  introv Ht. inversions Ht. exists* l.
Qed.

Lemma precise_obj_typ : forall G S T ds U,
    G, S |-! trm_val (val_new T ds) : U ->
    U = typ_bnd T.
Proof.
  introv Hp. dependent induction Hp; auto.
Qed.

Lemma precise_loc_typ : forall G S l T,
    G, S |-! trm_val (val_loc l) : T ->
    exists U,
      T = typ_nref U.
Proof.
  introv Hp. dependent induction Hp. exists* T.
Qed.

Lemma invertible_val_obj_all : forall G S V ds T U,
    G, S |-##v val_new V ds : typ_all T U ->
    False.
Proof.
  introv Ht. dependent induction Ht.
  apply precise_obj_typ in H. inversion H.
  apply* IHHt.
Qed.

Lemma invertible_val_obj_ref : forall G S V ds T,
    G, S |-##v val_new V ds : typ_ref T ->
    False.
Proof.
  introv Ht. dependent induction Ht.
  apply precise_obj_typ in H. inversion H.
Qed.

Lemma invertible_val_obj_nref : forall G S V ds T,
    G, S |-##v val_new V ds : typ_nref T ->
    False.
Proof.
  introv Ht. dependent induction Ht.
  apply precise_obj_typ in H. inversion H.
  apply* IHHt.
Qed.

Lemma corresponding_types: forall G S sta sto x T,
    well_formed G S sta sto ->
    inert G ->
    binds x T G ->
    ((exists L V U V' U' t, binds x (val_lambda V t) sta /\
                       G, S |-! trm_val (val_lambda V t) : typ_all V U /\
                       T = typ_all V' U' /\
                       G, S |- V' <: V /\
                       (forall y, y \notin L -> G & y ~ V', S |- open_typ y U <: open_typ y U')) \/
     (exists V ds, binds x (val_new V ds) sta /\
              G, S |-! trm_val (val_new V ds) : typ_bnd V /\
              T = typ_bnd V) \/
     (exists V V' l, binds x (val_loc l) sta /\
                G, S |-! trm_val (val_loc l) : typ_nref V /\
                (T = typ_nref V' \/ T = typ_ref V') /\
                G, S |- V <: V' /\
                G, S |- V' <: V)).
Proof.
  introv Hwf Hin Bi. induction Hwf. 
  - false* binds_empty_inv.
  - assert (inert G) as Hin'. {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H2) as [Hx [Ht Hg]]. subst*.
    }
    unfold binds in *. rewrite get_push in *. case_if.
    + inversions Bi. 
      inversion H1; subst.
      * right. right. exists T0 T0 l. split. reflexivity. 
        split. apply* weaken_ty_trm_ctx_p. split*.
      * left. exists L T0 U T0 U t. split. reflexivity.
        split. apply* weaken_ty_trm_ctx_p. split*.
      * right. left. exists T0 ds. split. reflexivity.
        split. apply* weaken_ty_trm_ctx_p. reflexivity.
      * apply general_to_tight_typing in H1.
        lets Hinv: (invertible_typing_lemma_v Hin' H1).
        assert (inert_typ T) as HinT. {
          inversions Hin.
          - false* empty_push_inv.
          - destruct (eq_push_inv H4) as [Hx [Hv HG]]. subst*.
        }
        inversions HinT.
        { apply invertible_val_to_precise_lambda in Hinv.
          destruct Hinv as [L [V' [T' [Hty [Hs1 Hs2]]]]].
          destruct (precise_forall_inv Hty) as [t Heq]. subst. left.
          exists (L \u dom G \u \{ x0}) V' T' S0 T1 t.
          split. reflexivity. split. apply* weaken_ty_trm_ctx_p.
          split. reflexivity.
          split. apply* weaken_subtyp_ctx. intros y Hy.
          apply (proj44 weaken_rules_ctx) with (G:=G & y ~ S0). apply* Hs2.
          reflexivity.
          apply ok_push. apply* inert_ok. simpl_dom. rewrite notin_union.
          split*.
          assumption.
        }
        { apply invertible_val_to_precise_rec in Hinv.
          destruct (precise_bnd_inv Hinv) as [ds Heq]. subst.
          right. left. exists T1 ds.
          split. reflexivity. split. apply* weaken_ty_trm_ctx_p. reflexivity.
        }
        { inversions Hinv. inversions H4.
        (* apply invertible_val_to_precise_ref in Hinv. *)
          (* destruct Hinv as [T [Ht [Hs1 Hs2]]]. *)
          (* inversion Ht.  *)
        }
        { apply invertible_val_to_precise_nref in Hinv.
          destruct Hinv as [T [Hty [Hs1 Hs2]]].
          destruct (precise_nref_inv Hty) as [l Heq]. subst.
          right. right. exists T T1 l.
          split. reflexivity. split. apply* weaken_ty_trm_ctx_p.
          split. left. reflexivity.
          split; apply* weaken_subtyp_ctx.
        }
        assumption.
    + specialize (IHHwf Hin' Bi).
      destruct IHHwf as [[L [V [U [V' [U' [t [Hv [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [[V [ds [Hv [Ht He]]]] | [V [V' [l [Hv [Ht [He Hs]]]]]]]].
      * left. exists (L \u dom G \u \{x0}) V U V' U' t. split. assumption. split.
        apply* weaken_ty_trm_ctx_p.
        split. assumption. split. apply* weaken_subtyp_ctx.
        intros y Hy.
        apply (proj44 (weaken_rules_ctx)) with (G:=G & y ~ V'). apply* Hs2.
        reflexivity. apply ok_push. apply* inert_ok. auto.
      * right. left. exists V ds. split. assumption. split. 
        apply* weaken_ty_trm_ctx_p. assumption.
      * right. right. exists V V' l. split. assumption. 
        split. apply weaken_ty_trm_ctx_p; auto. apply* inert_ok. 
        split. assumption. split; apply* weaken_subtyp_ctx.
  - assert (inert G) as Hin'. {
      inversions Hin.
      - false* empty_push_inv.
      - destruct (eq_push_inv H3) as [Hx [Ht Hg]]. subst*.
    }
    unfold binds in *. rewrite get_push in *. case_if.
    + inversions Bi. inversion H2; subst.
      * right. right. exists T0 T0 l. split. reflexivity. 
        split. apply* weaken_ty_trm_ctx_p. split*.
      * apply general_to_tight_typing in H2.
        lets Hinv: (invertible_typing_lemma_v Hin' H2).
        apply invertible_val_to_precise_nref in Hinv.
        destruct Hinv as [T' [Hty [Hs1 Hs2]]].
        destruct (precise_nref_inv Hty) as [l' Heq]. subst.
        right. right. exists T' T0 l.
        split. reflexivity. split. apply* weaken_ty_trm_ctx_p.
        split. right. reflexivity.
        split; apply* weaken_subtyp_ctx.
        assumption.
    + specialize (IHHwf Hin' Bi).
      destruct IHHwf as [[L [V [U [V' [U' [t [Hv [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [[V [ds [Hv [Ht He]]]] | [V [V' [l' [Hv [Ht [He Hs]]]]]]]].
      * left. exists (L \u dom G \u \{x0}) V U V' U' t. split. assumption. split.
        apply* weaken_ty_trm_ctx_p.
        split. assumption. split. apply* weaken_subtyp_ctx.
        intros y' Hy.
        apply (proj44 (weaken_rules_ctx)) with (G:=G & y' ~ V'). apply* Hs2.
        reflexivity. apply ok_push. apply* inert_ok. auto.
      * right. left. exists V ds. split. assumption. split. 
        apply* weaken_ty_trm_ctx_p. assumption.
      * right. right. exists V V' l'. split. assumption. 
        split. apply weaken_ty_trm_ctx_p; auto. apply* inert_ok. 
        split. assumption. split; apply* weaken_subtyp_ctx.
  - specialize (IHHwf Hin Bi).
      destruct IHHwf as [[L [V [U [V' [U' [t [Hv [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [[V [ds [Hv [Ht He]]]] | [V [V' [l' [Hv [Ht [He Hs]]]]]]]].
      * left. exists (L \u dom G \u \{x}) V U V' U' t. split. assumption. split.
        apply* weaken_ty_trm_sigma_p. split. assumption. 
        split. apply* weaken_subtyp_sigma.
        intros y Hy. apply* weaken_subtyp_sigma.
      * right. left. exists V ds. split. assumption. split. 
        apply* weaken_ty_trm_sigma_p. assumption.
      * right. right. exists V V' l'. split. assumption. 
        split. apply weaken_ty_trm_sigma_p; auto.
        apply* ok_push. split. assumption. split; apply* weaken_subtyp_sigma.
  - specialize (IHHwf Hin Bi).
      destruct IHHwf as [[L [V [U [V' [U' [t [Hv [Ht [Heq [Hs1 Hs2]]]]]]]]]] | [[V [ds [Hv [Ht He]]]] | [V [V' [l' [Hv [Ht [He Hs]]]]]]]].
      * left. exists (L \u dom G \u \{x}) V U V' U' t. split*.
      * right. left. exists V ds. split*. 
      * right. right. exists V V' l'. split*. 
Qed.

Lemma stack_binds_to_ctx_binds: forall G S sta sto x v,
    well_formed G S sta sto ->
    binds x v sta -> 
    exists V, binds x V G.
Proof.
  introv Hwf Bis.
  remember Hwf as Hwf'. clear HeqHwf'.
  induction Hwf.
  - false* binds_empty_inv.
  - destruct (binds_push_inv Bis) as [[Hx Hv] | [Hn Hb]]; subst.
    + exists* T.
    + destruct (IHHwf Hb Hwf) as [V HV]. exists V.
      apply* binds_push_neq.
  - destruct (binds_push_inv Bis) as [[Hx Hv] | [Hn Hb]]; subst.
    + exists* (typ_ref T).
    + destruct (IHHwf Hb Hwf) as [V HV]. exists V.
      apply* binds_push_neq.
  - auto.
  - auto.
Qed.

Lemma wf_stack_val_new_in_G: forall G S sta sto x T ds,
    well_formed G S sta sto ->
    inert G ->
    binds x (val_new T ds) sta ->
    binds x (typ_bnd T) G.
Proof.
  introv Hwf Hin Bis.
  assert (exists V, binds x V G) as Bi. {
    eapply stack_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [V Bi].
  induction Hwf.
  - false* binds_empty_inv.
  - assert (inert G /\ inert_typ T0) as HG. {
      inversions Hin. 
      - false* empty_push_inv. 
      - destruct (eq_push_inv H2) as [Hg [Hx Ht]]. subst. auto.
    }
    destruct HG as [HG HT].
    destruct (binds_push_inv Bis) as [[Hx Hv] | [Hn Hb]]; subst.
    + assert (T0 = typ_bnd T) as Heq. {
        apply binds_push_eq_inv in Bi. subst.
        clear IHHwf Hin Bis H H0 Hwf.
        apply general_to_tight_typing in H1; auto.
        apply invertible_typing_lemma_v in H1; auto.
        inversions H1; try solve [inversion HT].
        * apply* precise_obj_typ.
        * false* invertible_val_obj_all.
        * false* invertible_val_obj_nref.
      }
      subst*.
    + apply binds_push_neq_inv in Bi; auto.
  - assert (inert G) as HG. {
      inversions Hin. 
      - false* empty_push_inv. 
      - destruct (eq_push_inv H3) as [Hg [Hx Ht]]. subst. auto.
    }
    destruct (binds_push_inv Bis) as [[Hx Hv] | [Hn Hb]]; subst.
    + inversion Hv. 
    + apply binds_push_neq_inv in Bi; auto.
  - auto.
  - auto.
Qed.

Lemma precise_nref_subtyping: forall G S sta sto x l T,
    well_formed G S sta sto ->
    inert G -> 
    binds x (val_loc l) sta ->
    G, S |-# trm_var (avar_f x) : typ_nref T ->
    G, S |-# trm_val (val_loc l) : typ_nref T ->
    exists U,
      (G, S |-! trm_val (val_loc l) : typ_nref U /\
       G, S |- T <: U /\
       G, S |- U <: T).
Proof.
  introv Hwf Hin Bi Htx Htl.
  pose proof (invertible_typing_lemma_v Hin Htl).
  dependent induction H.
  - exists T. split*. 
  - pose proof (subtyp_nref_t H1 H0) as Hs.
    pose proof (ty_sub_t Htx Hs) as Htx'.
    pose proof (ty_sub_t Htl Hs) as Htl'.
    specialize (IHty_trm_inv_v l T0 Hwf Hin Bi Htx' Htl' eq_refl eq_refl) as [U [Hx [Hs1 Hs2]]].
    remember Hx as Hx'. inversions Hx'.
    exists U. repeat split.
    + assumption.
    + apply subtyp_trans with (T:=T0); auto.
      apply (proj22 tight_to_general); auto.
    + apply subtyp_trans with (T:=T0); auto.
      apply (proj22 tight_to_general); auto.
Qed.

Lemma val_new_typing: forall G S sta sto x T ds,
    well_formed G S sta sto ->
    inert G ->
    binds x (val_new T ds) sta ->
    G, S |-! trm_val (val_new T ds) : typ_bnd T.
Proof.
  introv Hwf Hin Bis.
  assert (exists T, binds x T G) as Bi. {
    eapply stack_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [T0 Bi].
  destruct (corresponding_types Hwf Hin Bi) as [Hnew | [Hlambda | Hloc]].
  - destruct Hnew as [_ [V [_ [_ [_ [t [Contra _]]]]]]].
    false.
  - destruct Hlambda as [T' [ds' [Bis' [Ht EqT]]]]. subst.
    pose proof (binds_func Bis Bis') as Heq; inversions Heq.
    assumption.
  - destruct Hloc as [V [l [Bi' [Htyp]]]].
    false.
Qed.
