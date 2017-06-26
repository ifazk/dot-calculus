Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Some_lemmas.
Require Import General_to_tight.
Require Import Invertible_typing.
Require Import Inert_types.
Require Import Substitution.
Require Import Narrowing.

(* (** NB **)  *)
(* Hypothesis var_dec : forall x y: var, {x = y} + {x <> y}. *)

(* Fixpoint binds_ec (x : var) (e : ec) : option val := *)
(*   match e with *)
(*   | e_empty => None *)
(*   | e_let_val y v e => if var_dec x y then Some v else binds_ec x e *)
(*   | e_let_trm y t => None *)
(*   end. *)

(** TODO: move to definitions and update notation **) 

Reserved Notation "e '[[' G ']]' '==' G'" (at level 10).
Inductive eg_app : ec -> ctx -> ctx -> Prop :=
| eg_empty : forall G, e_empty [[G]] == G
| eg_val : forall G x e (v: val) T G',
    x \notin ((fv_ec e) \u (dom G) \u (fv_ctx_types G) \u (fv_typ T) \u (fv_val v)) ->
    G |-! trm_val v : T ->
    e[[G & x ~ T]] == G' ->
    (e_let_val x v e) [[G]] == G'
| eg_trm : forall G x u, (e_let_trm x u) [[G]] == G
where "e '[[' G ']]' '==' G'" := (eg_app e G G').

Lemma e_preserves_inert : forall G e eG,
    inert G ->
    e[[G]] == eG ->
    inert eG.
Proof.
  introv Hi He. induction He; try assumption.
  apply IHHe. constructor; try assumption.
  apply (precise_inert_typ H0). auto. 
Qed.

Lemma e_preserves_typing : forall G e t et T eG,
    e {{ t }} == et ->
    G |- et : T ->
    e[[G]] == eG ->
    exists U, eG |- t : U.
Proof.
  (* Hint: The proof follows the same general structure as parts of the safety proof in Safety.v.
           Those parts might not be in safety itself, but could be hidden in Some_lemmas that the
           safety proof invokes. *)
  (* Hint: I believe this proof uses val_new_typing somewhere. *)
Admitted.

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v)
| nf_let: forall v n, normal_form n -> normal_form (trm_let (trm_val v) n).

Hint Constructors normal_form.

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
