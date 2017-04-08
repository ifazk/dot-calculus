Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Narrowing.
Require Import Some_lemmas.
Require Import Canonical_forms1.
Require Import Canonical_forms2.
Require Import Good_types.
Require Import General_to_tight.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Proofs *)

(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.

(*
Let G |- t: T and G ~ s. Then either

- t is a normal form, or
- there exists a store s', term t' such that s | t -> s' | t', and for any such s', t' there exists an environment G'' such that, letting G' = G, G'' one has G' |- t': T and G' ~ s'.
The proof is by a induction on typing derivations of G |- t: T.
*)

Lemma safety: forall G s t T,
    wf_sto G s ->
    good G ->
    ty_trm ty_general sub_general G t T ->
    (normal_form t \/ (exists s' t' G' G'', red t s t' s' /\ G' = G & G'' /\ ty_trm ty_general sub_general G' t' T /\ wf_sto G' s')).
Proof.
  introv Hwf Hg H. dependent induction H; try solve [left; eauto].
  - (* All-E *) right.
    lets Ht: (general_to_tight_typing Hg H).
    destruct (tight_to_precise_typ_all Hg Ht) as [S' [T' [Hpt [Hsub [HSsub [L HTsub]]]]]].
    lets Bi: (good_precise_all_inv Hg Hpt).
    destruct (corresponding_types Hwf Hg Bi)
      as [[L' [S0 [V [S1 [V1 [t [Hb [Ht' [Heq [Hs1 Hs2]]]]]]]]]] | [S0 [ds [Hb [Ht' Heq]]]]].
    + inversions Heq.
      inversions Ht'.
(*      exists s (open_trm z t) G (@empty typ). split.
      apply* red_app. split. rewrite* concat_empty_r. split.
      inversions Ht'.*)
      * pick_fresh z'. assert (z' \notin L0) as Hz' by auto.
        specialize (H5 z' Hz').
        assert (ty_trm ty_general sub_general (G & z' ~ S1) (open_trm z' t) (open_typ z' V))
          as Htn. {
          apply narrow_typing with (G:=G & z' ~ S0). assumption. apply* subenv_last.
          apply* ok_push.
        }
        assert (ty_trm ty_general sub_general (G & z' ~ S) (open_trm z' t) (open_typ z' V))
          as Htn'. {
          apply narrow_typing with (G:=G & z' ~ S1). assumption. apply subenv_last.
          apply* tight_to_general. apply* ok_push. apply* ok_push.
        }
        exists s (open_trm z t) (G & z' ~ S) (z' ~ S). split.
        apply* red_app. split. reflexivity. split.
        assert (subtyp ty_general sub_general (G & z' ~ S) (open_typ z' V) (open_typ z' T))
          as Hs. {
          apply subtyp_trans with (T:=open_typ z' V1).
          apply narrow_subtyping with (G:=G & z' ~ S1). apply* Hs2. apply subenv_last.
          apply* tight_to_general. apply* ok_push. apply* ok_push.
          apply* HTsub.
        }
        assert (ty_trm ty_general sub_general (G & z' ~ S) (open_trm z' t) (open_typ z' T))
          as Htz. {
          apply ty_sub with (T:=open_typ z' V). intro Contra. inversion Contra.
          assumption. assumption.
        }
        rewrite subst_intro_trm with (x:=z'). rewrite subst_intro_typ with (x:=z').
        eapply subst_ty_trm. apply weaken_ty_trm. assumption.


  subst. inversion Heq; subst. inversions Ht.
  - exists (L \u L' \u L0) S t.
    split; auto.
    pose proof (tight_possible_types_lemma Hgd Hti) as Htp.
    inversion Htp; subst.


    lets C: (canonical_forms_1). Hwf Hg H).

    letc C: (corresponding_types).
    lets C: (canonical_forms_1 Hwf H).
    destruct C as [L [T' [t [Bis [Hsub Hty]]]]].
    exists s (open_trm z t) G (@empty typ).
    split.
    apply red_app with (T:=T'). assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
    eapply subst_ty_trm. eapply Hty.
    apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
    rewrite subst_fresh_typ.
    apply ty_sub with (T:=S).
    intro Contra. inversion Contra.
    assumption. apply subtyp_refl.
    eauto. eauto. eauto. eauto.
  - (* Fld-E *) right.
    pose proof (canonical_forms_2 Hwf H) as [S [ds [t [Bis [Has Ty]]]]].
    exists s t G (@empty typ).
    split.
    apply red_sel with (T:=S) (ds:=ds); try assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    assumption.
    assumption.
  - (* Let *) right.
    destruct t.
    + (* var *)
      assert (exists x, a = avar_f x) as A. {
        eapply var_typing_implies_avar_f. eassumption.
      }
      destruct A as [x A]. subst a.
      exists s (open_trm x u) G (@empty typ).
      split.
      apply red_let_var.
      split.
      rewrite concat_empty_r. reflexivity.
      split.
      pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H0 y FrL).
      rewrite subst_intro_trm with (x:=y).
      rewrite <- subst_fresh_typ with (x:=y) (y:=x).
      eapply subst_ty_trm. eapply H0.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
      rewrite subst_fresh_typ. assumption. eauto. eauto. eauto. eauto.
    + lets Hv: (val_typing H).
      destruct Hv as [T' [Htyp Hsub]].
      pick_fresh x. assert (x \notin L) as FrL by auto. specialize (H0 x FrL).
      exists (s & x ~ v) (open_trm x u) (G & (x ~ T')) (x ~ T').
      split.
      apply red_let. eauto.
      split. reflexivity. split. Check narrow_typing.
      apply narrow_typing with (G:=G & x ~ T).
      assumption.
      apply subenv_last. assumption.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      apply wf_sto_push. assumption. eauto. eauto. assumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; auto.
    right. destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
    exists s' t' G' G''.
    split; try split; try split; try assumption.
    apply ty_sub with (T:=T).
    intro Contra. inversion Contra.
    assumption.
    rewrite IH2. apply weaken_subtyp. assumption.
    rewrite <- IH2. eapply wf_sto_to_ok_G. eassumption.
Qed.
