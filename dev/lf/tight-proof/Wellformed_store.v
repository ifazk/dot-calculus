Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Some_lemmas.
Require Import Good_types.

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

(*
Lemma ctx_binds_to_sto_binds_raw: forall s G x T,
  wf_sto G s ->
  binds x T G ->
  exists G1 G2 v, G = G1 & (x ~ T) & G2 /\ binds x v s /\ ty_trm ty_precise sub_general G1 (trm_val v) T.
Proof.
  introv Wf Bi. gen x T Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) v.
      rewrite concat_empty_r.


    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [ds' [Eq [Bi' Tyds]]]]].
      subst. exists G1 (G2 & x ~ T) ds'. rewrite concat_assoc. auto.
Qed.*)

(*Lemma corresponding_types: forall G s x T,
  wf_sto G s ->
  binds x T G ->
  ((exists S U t, binds x (val_lambda S t) s /\
                  ty_trm ty_precise sub_general G (trm_val (val_lambda S t)) (typ_all S U) /\
                  T = typ_all S U) \/
   (exists S ds, binds x (val_new S ds) s /\
                 ty_trm ty_precise sub_general G (trm_val (val_new S ds)) (typ_bnd S) /\
                 T = typ_bnd S)).
Proof.
  introv H Bi. induction H.
  - false* binds_empty_inv.
  - unfolds binds. rewrite get_push in *. case_if.
    + inversions Bi. inversion H2; subst.
      * left. exists T0. exists U. exists t.
        split. auto. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        reflexivity.
      * right. exists T0. exists ds.
        split. auto. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        reflexivity.
      * assert (exists x, trm_val v = trm_var (avar_f x)) as A. {
          apply H3. reflexivity.
        }
        destruct A as [? A]. inversion A.
    + specialize (IHwf_sto Bi).
      inversion IHwf_sto as [IH | IH].
      * destruct IH as [S [U [t [IH1 [IH2 IH3]]]]].
        left. exists S. exists U. exists t.
        split. assumption. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        assumption.
      * destruct IH as [S [ds [IH1 [IH2 IH3]]]].
        right. exists S. exists ds.
        split. assumption. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        assumption.
Qed.*)

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

(*
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
*)

(*
Lemma val_new_typing: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  ty_trm ty_precise sub_general G (trm_val (val_new T ds)) (typ_bnd T).
Proof.
  introv Hwf Bis.
  assert (exists T, binds x T G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [T0 Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [S [U [t [Bis' [Ht EqT]]]]].
    false.
  - destruct H as [T' [ds' [Bis' [Ht EqT]]]]. subst.
    unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis.
    inversion Bis. subst.
    assumption.
Qed.
*)
