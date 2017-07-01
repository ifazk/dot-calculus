Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import Some_lemmas.
Require Import General_to_tight.
Require Import Invertible_typing.
Require Import Inert_types.
Require Import Substitution.
Require Import Narrowing.
Require Import Weakening.

Module ec.

Inductive ec : Type :=
| e_hole : sto -> ec
| e_term : sto -> trm -> ec.

Inductive app_ec : ec -> ec -> ec -> Prop :=
| app_hole_hole : forall s s',
    app_ec (e_hole s) (e_hole s') (e_hole (s & s'))
| app_hole_term : forall s s' t',
    app_ec (e_hole s) (e_term s' t') (e_term (s & s') t')
| app_term_empty : forall s t,
    app_ec (e_term s t) (e_hole (@empty val)) (e_term s t).

Inductive red : ec -> trm -> ec -> trm -> Prop :=
| red_term : forall e e' e'' t t',
    red e t e t' ->
    app_ec e' e e'' ->
    red e'' t e'' t'
| red_apply_hole : forall x T t s y,
    red (e_hole ((x ~ (val_lambda T t)) & s))
        (trm_app (avar_f x) (avar_f y))
        (e_hole ((x ~ (val_lambda T t)) & s))
        (open_trm y t)
| red_apply_term : forall x T t s u y,
    red (e_term ((x ~ (val_lambda T t)) & s) u)
        (trm_app (avar_f x) (avar_f y))
        (e_term ((x ~ (val_lambda T t)) & s) u)
        (open_trm y t)
| red_project_hole : forall x T ds a t s,
    defs_has (open_defs x ds) (def_trm a t) ->
    red (e_hole ((x ~ (val_new T ds)) & s))
        (trm_sel (avar_f x) a)
        (e_hole ((x ~ (val_new T ds)) & s))
        t
| red_project_term : forall x T ds a t s u,
    defs_has (open_defs x ds) (def_trm a t) ->
    red (e_term ((x ~ (val_new T ds)) & s) u)
        (trm_sel (avar_f x) a)
        (e_term ((x ~ (val_new T ds)) & s) u)
        t
| red_let_var : forall e x t,
    red e (trm_let (trm_var (avar_f x)) t) e (open_trm x t)
| red_let_let : forall e s t u,
    red e (trm_let (trm_let s t) u) e (trm_let s (trm_let t u)).

End ec.

(** TODO: find appropriate place for definition *)
Fixpoint ec_of_trm (t : trm) : (ec * trm) :=
  match t with
  | (trm_var x) => (e_empty, (trm_var x))
  | (trm_val v) => (e_empty, (trm_val v))
  | (trm_sel x a) => (e_empty, (trm_sel x a))
  | (trm_app x y) => (e_empty, (trm_app x y))
  | (trm_let t1 t2) =>
    match t1 with
    | (trm_val v) =>
      let (e, t') := ec_of_trm t2 in
      let x : var := var_gen ((fv_ec e) \u (fv_trm t') \u (fv_val v)) in
      ((e_let_val x v (open_ec x e)), (open_trm x t'))
    | _ =>
      let x : var := var_gen ((fv_trm t1) \u (fv_trm t2)) in
      ((e_let_trm x (open_trm x t2)), t1)
    end
  end.

Inductive binds_ec : var -> val -> ec -> Prop :=
| binds_ec_single: forall x v e, binds_ec x v (e_let_val x v e)
| binds_ec_push: forall x v x' v' e,
    binds_ec x v e -> (** TODO: conditions on x' ? **)
    binds_ec x v (e_let_val x' v' e).
Hint Constructors binds_ec.

Lemma test: forall x v,
    binds_ec x v (e_let_val x v e_empty).
Proof.
  intros. constructor.
Qed.

Lemma test2: forall x v,
    binds_ec x v e_empty -> False.
Proof.
  intros. inversion H.
Qed.

Lemma test3: forall x v x' t,
    binds_ec x v (e_let_trm x' t) -> False.
Proof.
  intros. inversion H.
Qed.

Inductive ec_red' : ec -> trm -> ec -> trm -> Prop :=
| red_apply'' : forall f a T t e,
    binds_ec f (val_lambda T t) e ->
    ec_red' e (trm_app (avar_f f) (avar_f a)) e (open_trm a t)
| red_project'' : forall x m e t T ds,
    binds_ec x (val_new T ds) e ->
    defs_has (open_defs x ds) (def_trm m t) ->
    ec_red' e (trm_sel (avar_f x) m) e t
| red_trm_something
| red_let_val'' : forall v t e x,
    x \notin (fv_ec e) ->
    ec_red' e (trm_let (trm_val v) t) (e_let_val x v e) (open_trm x t)
| red_let_var'' : forall x t e,
    ec_red' e (trm_let (trm_var (avar_f x)) t) e (open_trm x t)
| red_let_let'' : forall s t u e,
    ec_red' e (trm_let (trm_let s t) u) e (trm_let s (trm_let t u)).

(** TODO: move to definitions and update notation **)

(* Reserved Notation "e '[[' G ']]' '==' G'" (at level 10). *)
Inductive eg_app : ec -> ctx -> ctx -> Prop :=
| eg_empty : forall G, eg_app e_empty G G
| eg_val : forall G x e (v: val) T G',
    x \notin ((fv_ec e) \u (dom G) \u (fv_ctx_types G) \u (fv_typ T) \u (fv_val v)) ->
    G |-! trm_val v : T ->
    eg_app e (G & x ~ T) G' ->
    eg_app (e_let_val x v e) G G'
| eg_trm : forall G x u, eg_app (e_let_trm x u) G G
(* where "e '[[' G ']]' '==' G'" := (eg_app e G G') *).

(* Lemma e_preserves_inert : forall G e eG, *)
(*     inert G -> *)
(*     e[[G]] == eG -> *)
(*     inert eG. *)
(* Proof. *)
(*   introv Hi He. induction He; try assumption. *)
(*   apply IHHe. constructor; try assumption. *)
(*   apply (precise_inert_typ H0). auto. *)
(* Qed. *)

(* Lemma e_preserves_typing : forall G e t et T eG, *)
(*     e {{ t }} == et -> *)
(*     G |- et : T -> *)
(*     e[[G]] == eG -> *)
(*     exists U, eG |- t : U. *)
(* Proof. *)
(*   (* Hint: The proof follows the same general structure as parts of the safety proof in Safety.v. *)
(*            Those parts might not be in safety itself, but could be hidden in Some_lemmas that the *)
(*            safety proof invokes. *) *)
(*   (* Hint: I believe this proof uses val_new_typing somewhere. *) *)
(* Admitted. *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v)
| nf_let: forall v n, normal_form n -> normal_form (trm_let (trm_val v) n).
Hint Constructors normal_form.

Inductive ty_ec_trm: ctx -> ec -> trm -> typ -> Prop :=
| ty_empty: forall G t T,
    G |- t : T ->
    ty_ec_trm G e_empty t T
| ty_let_val: forall G G' x v e t T,
    x \notin ((dom G) \u (fv_ctx_types G) \u (dom G') \u (fv_ctx_types G') \u (fv_ec e) \u (fv_trm t) \u (fv_typ T)) ->
    eg_app (e_let_val x v e_empty) G G' ->
    ty_ec_trm G' e t T ->
    ty_ec_trm G (e_let_val x v e) t T
| ty_let_trm: forall G x t u T,
    G |- (trm_let t u) : T ->
    x \notin ((dom G) \u (fv_ctx_types G) \u (fv_trm t) \u (fv_trm u) \u (fv_typ T)) ->
    ty_ec_trm G (e_let_trm x u) t T.

Lemma preservation': forall e t e' t' T,
    ec_red' e t e' t' ->
    ty_ec_trm empty e t T ->
    ty_ec_trm empty e' t' T.
Proof.
  introv Hred Ht. gen e' t'.
  dependent induction Ht; intros.
  - dependent induction H; inversions Hred; admit.
  - induction Hred.
    +

Lemma preservation: forall G e t e' t' T,
    eg_app e empty G ->
    inert G ->
    ec_red' e t e' t' ->
    G |- t : T ->
    exists G', inert G' /\
          eg_app e' empty (G & G') /\
          G & G' |- t' : T.
Proof.
  introv Hg Hin Hred Ht.
  gen t'.
  dependent induction Ht; intros; try solve [inversions Hred].
  - admit.
  - admit.
  - destruct t.
    + inversions Hred.
      pick_fresh y.
      exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
      rewrite subst_intro_trm with (x:=y); auto.
      rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
      eapply subst_ty_trm; auto. rewrite~ subst_fresh_typ.
    + inversions Hred.
      (* pose proof some kind of x # G *)
      pose proof (val_typing Ht) as [V [Hv Hs]].
      pick_fresh y. assert (y \notin L) by auto.
      specialize (H y H1). exists (x ~ V). repeat split.
      * rewrite <- concat_empty_l. constructor~.
        apply (precise_inert_typ Hv).
      * admit. (* eapply eg_val. *)
      * rewrite subst_intro_trm with (x:=y); auto.
        rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
        eapply subst_ty_trm; auto.
        {
          eapply weaken_rules; eauto.
          admit.
        }
        { admit. }
        { apply~ fv_ctx_types_push. }
        {
          rewrite~ subst_fresh_typ.
          pose proof (ty_var (binds_tail x V G)).
          apply (ty_sub H2). apply (weaken_subtyp Hs). admit.
        }
    + inversions Hred.
    + inversions Hred.
    + inversions Hred. admit.
      (* specialize (IHHt Hg Hin). *)
      (* exists ( *)
  - specialize (IHHt Hg Hin t' Hred) as [G' [Hin' [Hgg' Ht']]].
    exists G'. repeat split; auto.
    apply weaken_subtyp with (G2:=G') in H.
    + apply (ty_sub Ht' H).
    + admit.
Qed.

Lemma progress: forall G e t T,
    eg_app e empty G ->
    inert G ->
    G |- t : T ->
    (normal_form t \/ exists e' t', ec_red' e t e' t').
Proof.
  introv Hg Hin Ht. dependent induction Ht; try solve [left; auto].
  - admit.
  - admit.
  - right. destruct t.
    + pose proof (var_typing_implies_avar_f Ht) as [x A]. subst.
      exists e (open_trm x u).
      apply red_let_var''.
    + pick_fresh x.
      exists (e_let_val x v e) (open_trm x u).
      apply~ red_let_val''.
    + specialize (IHHt Hg Hin) as [IH | [e' [t' Hred]]].
      * inversion IH.
      * inversions Hred.

Lemma progress_induction : forall e eG t T et,
  (* inert G -> *)
  e[[empty]] == eG ->
  eG |- t : T ->
  e {{ t }} == et ->
  (normal_form et \/ exists t' et', (et |=> et' /\ e {{ t' }} == et')).
Proof.
  introv HeG Ht Het.
  dependent induction e.
  - inversions Het. inversions HeG. dependent induction Ht; try solve [left; constructor]; try solve [false* empty_typing_var].
    + clear H0. specialize (IHHt JMeq_refl) as [? | ?].
      * induction H0.
        { false* empty_typing_var. }
        {
          induction u.
          - left. constructor~.
          - left. constructor~.
          - right. destruct v.
            + admit.
            + admit.
          - right. admit.
          - admit.
        }
        {
          right. exists (trm_let (trm_val v) (trm_let n u)) (trm_let (trm_val v) (trm_let n u)).
          split.
          - apply red_let_let'.
          - constructor.
        }
      * destruct H0 as (t' & et' & Htet' & Heq).
        inversions Heq. admit.
    + apply~ IHHt.
  - admit.
  - inversions HeG. inversions Het. dependent induction Ht; try solve [left; constructor]; try solve [false* empty_typing_var].
    + admit.
    + admit.
    + admit.
    + admit.
Qed.

(**********************)

  (* induction Ht. (* ; try solve [left; eauto]. *) *)
  (* - gen G. dependent induction e; intros. *)
  (*   + left. inversions Het. constructor. *)
  (*   + inversions HeG. *)
  (*     assert (Hin': inert (G & v ~ T0)). { *)
  (*       constructor*. apply (precise_inert_typ H7). *)
  (*     } *)
  (*     inversions Het. *)
  (*     specialize (IHe _ _ _ _ H H10 _ Hin' H8). right. *)
  (*     destruct IHe. *)
  (*     * inversions H0. *)
  (*       { admit. } *)
  (*       {  *)

  (*     right. exists (trm_var (avar_f x0)) (trm_let (trm_val v) t). split. *)
  (*     * admit. *)
  (*     * constructor*. *)


(*       pose proof (e_preserves_inert Hin' HeG). *)
(*       (* assert (inert (G & x ~ T)). { *) *)
(*       (*   constructor*. *) *)
(*       (* } apply (IHHeG. *) *)

(* (* dependent induction Het; left; constructor. *) *)
(* (*     +  *) *)
(* (*     + left. constructor. *) *)

  (* Hint: The proof follows the same general structure as the safety proof in Safety.v. *)
  (* Hint: The proof uses e_preserves_inert and e_preserves_typing. *)

Lemma progress : forall t T,
  empty |- t : T ->
  (normal_form t \/ exists t', t |=> t').
Proof.
  intros.
  assert (normal_form t \/ exists t' et', (t |=> et' /\ e_empty {{ t' }} == et')). {
    apply progress_induction with (eG := empty) (t := t) (T := T);
      try constructor; try assumption.
  }
  destruct H0.
  - left. assumption.
  - destruct H0 as (t' & et & ? & _). (* [t' [et [? _]]].  *)right. exists et. assumption.
Qed.

(* Lemma test1: forall x u u', *)
(*     u |=> u' -> *)
(*     open_trm x u |=> open_trm x u'. *)
(* Proof. *)
(*   intros. dependent induction H. *)
(*   - induction e; inversions H0; inversions H1. *)
(*     + assumption. *)
(*     +  *)


(* Lemma test1: forall x u u', *)
(*     open_trm x u |=> open_trm x u' -> *)
(*     u |=> u'. *)
(* Proof. *)
(*   intros. dependent induction H. *)
(*   - destruct e; inversions H0; inversions H1. *)
(*     + eapply IHec_red; eauto. *)
(*     + apply open_fresh_ec_injective in H4; auto. subst. *)
(*       eapply IHec_red; eauto. *)
(*   - inversions H0. inversions H1.  *)
(*     apply open_fresh_ec_injective in H4; auto. subst. *)
(*     eapply (proj41 open_fresh_trm_val_def_defs_injective) in H5; auto. *)

(* Lemma test: forall e t t' x u u', *)
(*     e {{ t }} == (open_trm x u) -> *)
(*     e {{ t' }} == (open_trm x u') -> *)
(*     t |=> t' -> *)
(*     u |=> u'. *)
(* Proof. *)
(*   introv Ht Ht' Hred. induction e; inversions Ht; inversions Ht'. *)
(*   - eapply IHHred; eauto. *)

Lemma preservation : forall G t T t',
  inert G ->
  G |- t : T ->
  t |=> t' ->
  G |- t' : T.
Proof.
  introv Hin Ht Htt'. gen t'.
  induction Ht; intros.
  - dependent induction Htt'.
    + inversions H1. inversions H0. eapply IHHtt'; eauto.
    + inversions H1. inversions H0.
    + inversions H1.
  - clear H H0. dependent induction Htt'.
    + inversions H. inversions H0. eapply IHHtt'; eauto.
    + inversions H1. inversions H0.
    + inversions H1.
  - dependent induction Htt'.
    + inversions H. inversions H0. eapply IHHtt'; eauto.
    + inversions H1. inversions H0.
    + inversions H1.
  - clear H. dependent induction Htt'.
    + inversions H. inversions H0. eapply IHHtt'; eauto.
    + inversions H1. inversions H0.
    + inversions H1.
  - clear Ht. dependent induction Htt'.
    + inversions H. inversions H0. eapply IHHtt'; eauto.
    + inversions H1. inversions H0.
    + inversions H1.
  - destruct t.
    + (* pose proof (var_typing_implies_avar_f Ht) as [x A]. subst. *)
      dependent induction Htt'.
      * destruct e; inversions H1; inversions H2.
        { eapply IHHtt'; eauto. }
        {
          eapply (proj41 open_fresh_trm_val_def_defs_injective) in H4; auto.
          subst. apply_fresh ty_let as z; auto.
        }
      * inversions H3.
      * inversions H1.
      * clear H0 IHHt. pick_fresh z.
        rewrite subst_intro_trm with (x:=z); auto.
        rewrite <- subst_fresh_typ with (x:=z) (y:=y); auto.
        eapply subst_ty_trm.
        { apply~ H. }
        { constructor~. apply~ inert_ok. }
        { auto. }
        { rewrite~ subst_fresh_typ. }
    + dependent induction Htt'.
      * destruct e; inversions H1; inversions H2.
        { eapply IHHtt'; eauto. }
        {
          (* clear IHHtt'. *)
          apply open_fresh_ec_injective in H5; auto. subst.

          apply_fresh ty_let as z; eauto.
          admit.
          (* eapply H0; eauto. *)
          (* - admit. *)
          (* - eapply red_term'; eauto. *)
          (*   + rewrite subst_intro_trm with (x:=v); auto. *)

        }
        {
          eapply (proj41 open_fresh_trm_val_def_defs_injective) in H4; auto.
          subst. apply_fresh ty_let as z; eauto.
        }
      * inversions H1. inversions H3.
        apply open_fresh_ec_injective in H6; auto. subst.
        apply_fresh ty_let as z; eauto.
        admit.
      * inversions H1. inversions H2.
        apply open_fresh_ec_injective in H8; auto. subst.
        apply_fresh ty_let as z; eauto.
        admit.
    + dependent induction Htt'.
      * destruct e; inversions H1; inversions H2.
        { eapply IHHtt'; eauto. }
        {
          apply (proj41 open_fresh_trm_val_def_defs_injective) in H4; auto.
          subst. apply_fresh ty_let as z; eauto.
        }
      * inversions H3.
      * inversions H1.
    + dependent induction Htt'.
      * destruct e; inversions H1; inversions H2.
        { eapply IHHtt'; eauto. }
        {
          apply (proj41 open_fresh_trm_val_def_defs_injective) in H4; auto.
          subst. apply_fresh ty_let as z; eauto.
        }
      * inversions H3.
      * inversions H1.
    + dependent induction Htt'.
      * destruct e; inversions H1; inversions H2.
        { eapply IHHtt'; eauto. }
        {
          apply (proj41 open_fresh_trm_val_def_defs_injective) in H4; auto.
          subst. apply_fresh ty_let as z; eauto.
        }
      * inversions H3.
      * inversions H1.
      * dependent induction Ht.
        { apply_fresh ty_let as z; eauto. clear H0 IHHt.
          assert (forall x : var, x \notin L -> G & z ~ U0 & x ~ T |- open_trm x (open_rec_trm 1 z u) : U) by admit.
          assert (z \notin L0) by auto.
          specialize (H6 z H2).

          pose proof (ty_let _ H6 H1).
          unfold open_trm in *. simpl. assumption.
        }
        {
          eapply IHHt; eauto.
          - admit.
          - admit.
          - admit.
        }


  - clear Ht. dependent induction Htt'.
    + inversions H. inversions H0. eapply IHHtt'; eauto.
    + inversions H1. inversions H0.
    + inversions H1.
  - clear Ht. dependent induction Htt'.
    + inversions H. inversions H0. eapply IHHtt'; eauto.
    + inversions H1. inversions H0.
    + inversions H1.
  - clear Ht1 Ht2. dependent induction Htt'.
    + inversions H. inversions H0. eapply IHHtt'; eauto.
    + inversions H1. inversions H0.
    + inversions H1.
  - specialize (IHHt Hin t' Htt').
    apply (ty_sub IHHt H).
Qed.
