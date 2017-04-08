Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Some_lemmas.
Require Import Good_types.
Require Import General_to_tight.
Require Import Tight_possible_types_val.
Require Import Narrowing.

(* ###################################################################### *)
(** ** Well-formed store *)

Lemma wf_sto_to_ok_G: forall s G,
  wf_sto G s -> ok G.
Proof. intros. induction H; jauto. Qed.

(*Lemma wf_good : forall G s, wf_sto G s -> good G.
Proof.
  intros. induction H.
  - apply good_empty.
  - apply good_all; auto.
    dependent induction H2.
    + apply good_typ_all.
    + apply good_typ_bnd.
      pick_fresh z. apply open_record_type_rev with (x:=z); auto.
      apply record_defs_typing with (G:=G & z ~ open_typ z T) (ds:= open_defs z ds). auto.
    + pose proof (H4 eq_refl) as [? Contra]. inversion Contra.
Qed.*)

Hint Resolve wf_sto_to_ok_G.

Lemma ctx_binds_to_sto_binds_raw: forall s G x T,
  wf_sto G s ->
  binds x T G ->
  exists v, binds x v s /\ ty_trm ty_general sub_general G (trm_val v) T.
Proof.
  introv Wf Bi. gen x T Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists v. split. reflexivity. apply* weaken_ty_trm.
    - specialize (IHWf _ _ Bi). destruct IHWf as [v' [Hg Ht]].
      subst. exists v'. split. assumption. apply* weaken_ty_trm.
Qed.

Lemma tpt_to_precise_rec: forall G v T,
    tight_pt_v G v (typ_bnd T) ->
    ty_trm ty_precise sub_general G (trm_val v) (typ_bnd T).
Proof.
  introv Ht.
  inversions Ht. assumption.
Qed.

Lemma tpt_to_precise_lambda: forall G v S T,
    tight_pt_v G v (typ_all S T) ->
    good G ->
    exists L S' T',
      ty_trm ty_precise sub_general G (trm_val v) (typ_all S' T') /\
      subtyp ty_general sub_general G S S' /\
      (forall y, y \notin L ->
                 subtyp ty_general sub_general (G & y ~ S) (open_typ y T') (open_typ y T)).
Proof.
  introv Ht Hg. dependent induction Ht.
  - exists (dom G) S T. split*.
  - destruct (IHHt S0 T0 eq_refl Hg) as [L' [S1 [T1 [Hp [Hss Hst]]]]].
    exists (L \u L' \u dom G) S1 T1. split. assumption. split. apply subtyp_trans with (T:=S0).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ S)) as Hok. {
      apply* ok_push. apply* good_ok.
    }
    apply subtyp_trans with (T:=open_typ y T0).
    eapply narrow_subtyping. apply* Hst. apply subenv_last. apply* tight_to_general.
    assumption. assumption.
    apply* H0.
Qed.

Lemma precise_forall_inv : forall G v S T,
    ty_trm ty_precise sub_general G (trm_val v) (typ_all S T) ->
    exists t,
      v = val_lambda S t.
Proof.
  introv Ht. inversions  Ht. exists* t. false* H.
Qed.

Lemma precise_bnd_inv : forall G v S,
    ty_trm ty_precise sub_general G (trm_val v) (typ_bnd S) ->
    exists ds,
      v = val_new S ds.
Proof.
  introv Ht. inversions Ht. exists* ds. false* H.
Qed.

Lemma corresponding_types: forall G s x T,
  wf_sto G s ->
  good G ->
  binds x T G ->
  ((exists L S U S' U' t, binds x (val_lambda S t) s /\
                  ty_trm ty_precise sub_general G (trm_val (val_lambda S t)) (typ_all S U) /\
                  T = typ_all S' U' /\
                  subtyp ty_general sub_general G S' S /\
                  (forall y, y \notin L ->
                  subtyp ty_general sub_general (G & y ~ S') (open_typ y U) (open_typ y U'))) \/
   (exists S ds, binds x (val_new S ds) s /\
                 ty_trm ty_precise sub_general G (trm_val (val_new S ds)) (typ_bnd S) /\
                 T = typ_bnd S)).
Proof.
  introv H Hgd Bi. induction H.
  - false* binds_empty_inv.
  - assert (good G) as Hg. {
      inversions Hgd. false* empty_push_inv. destruct (eq_push_inv H3) as [Hx [Hv HG]]. subst*.
    }
    unfolds binds. rewrite get_push in *. case_if.
    + inversions Bi. inversion H2; subst.
      * left. exists (L \u dom G) T0 U T0 U t.
        split*. split*.
        apply* weaken_ty_trm.
      * right. exists T0. exists ds. split*. split*.
        apply* weaken_ty_trm.
      * apply general_to_tight_typing in H2.
        lets Hpt: (tight_possible_types_lemma_v Hg H2).
        assert (good_typ T) as HgT. {
          inversions Hgd. false* empty_push_inv. destruct (eq_push_inv H6) as [Hx [Hv HG]]. subst*.
        }
        inversions HgT.
        apply tpt_to_precise_lambda in Hpt. destruct Hpt as [L [S' [T' [Hss [Hs1 Hs2]]]]].
        destruct (precise_forall_inv Hss) as [t Heq]. subst. left.
        exists (L \u dom G \u \{ x0}) S' T' S T1 t.
        split. apply* f_equal. split. apply* weaken_ty_trm. split. reflexivity.
        split. apply* weaken_subtyp. intros y Hy.
        apply (proj44 weaken_rules) with (G:=G & y ~ S). apply* Hs2. reflexivity.
        apply ok_push. apply* good_ok. simpl_dom. rewrite notin_union. split*.
        assumption.
        apply tpt_to_precise_rec in Hpt.
        destruct (precise_bnd_inv Hpt) as [ds Heq]. subst. right. exists T1 ds.
        split. reflexivity. split. apply* weaken_ty_trm. reflexivity.
        assumption.
    + specialize (IHwf_sto Hg Bi).
      destruct IHwf_sto as [[L [S [U [S' [U' [t [Hv [Ht [Heq [Hs1 Hs2]]]]]]]]]] |
                            [S [ds [Hv [Ht He]]]]].
      * left. exists (L \u dom G \u \{x0}) S U S' U' t. split. assumption. split.
        apply* weaken_ty_trm.
        split. assumption. split. apply* weaken_subtyp.
        intros y Hy. apply (proj44 (weaken_rules)) with (G:=G & y ~ S'). apply* Hs2.
        reflexivity. apply ok_push. apply* good_ok. auto.
      * right. exists S ds. split. assumption. split. apply* weaken_ty_trm. assumption.
Qed.

Lemma sto_binds_to_ctx_binds: forall G s x v,
  wf_sto G s -> binds x v s -> exists S, binds x S G.
Proof.
  introv Hwf Bis.
  remember Hwf as Hwf'. clear HeqHwf'.
  induction Hwf.
  false* binds_empty_inv.
  destruct (binds_push_inv Bis) as [[Hx Hv] | [Hn Hb]]; subst.
  - exists* T.
  - destruct (IHHwf Hb Hwf) as [S HS]. exists S.
    apply* binds_push_neq.
Qed.

Lemma wf_sto_val_new_in_G: forall G s x T ds,
  wf_sto G s ->
  good G ->
  binds x (val_new T ds) s ->
  binds x (typ_bnd T) G.
Proof.
  introv Hwf Hg Bis.
  assert (exists S, binds x S G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [S Bi].
  dependent induction Hwf.
  false* binds_empty_inv.
  assert (good G /\ good_typ T0) as HG. {
    inversions Hg. false* empty_push_inv. destruct (eq_push_inv H2) as [Hg [Hx Ht]].
    subst. auto.
  }
  destruct HG as [HG HT].
  destruct (binds_push_inv Bis) as [[Hx Hv] | [Hn Hb]]; subst.
  - apply binds_push_eq_inv in Bi. subst.
    clear IHHwf Hg Bis H H0 Hwf. gen x0.
    apply val_typing in H1. destruct H1 as [U [Ht Hs]].
    assert (U = typ_bnd T) as Hbnd. {
      dependent induction Ht; auto.
      assert (subtyp ty_general sub_general G T1 T0) as Hsub. {
        apply subtyp_trans with (T:=U). apply* precise_to_general_subtyping. assumption.
      }
      specialize (IHHt T ds eq_refl eq_refl eq_refl Hsub HG). subst.
      destruct U; specialize (H eq_refl); destruct H; inversion H.
    }
    subst. destruct T0; intro; inversions HT.
    * clear Ht HG. dependent induction Hs. auto.
      specialize


Lemma val_new_typing: forall G s x T ds,
  wf_sto G s ->
  good G ->
  binds x (val_new T ds) s ->
  ty_trm ty_precise sub_general G (trm_val (val_new T ds)) (typ_bnd T).
Proof.
  introv Hwf Hg Bis.
  assert (exists T, binds x T G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [T0 Bi].
  destruct (corresponding_types Hwf Hg Bi).
  - destruct H as [L [S [U [S' [U' [t [Bis' [Ht EqT]]]]]]]].
    false.
  - destruct H as [T' [ds' [Bis' [Ht EqT]]]]. subst.
    unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis.
    inversion Bis. subst.
    assumption.
Qed.
