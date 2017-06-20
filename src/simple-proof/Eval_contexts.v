Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Some_lemmas.
Require Import General_to_tight.
Require Import Invertible_typing.
Require Import Inert_types.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive ec : Set :=
| e_empty     : ec              (* [] *)
| e_let_val   : var -> val -> ec -> ec  (* let x = v in e *)
| e_let_trm   : var -> trm -> ec.      (* let x = [] in t *)

Fixpoint vars (e: ec) : list var := match e with
| e_empty => []
| e_let_val x v e => x :: (vars e)
| e_let_trm x t => [x]
end.

Reserved Notation "e '[' u ']' '==' t" (at level 10).
Inductive ec_app : ec -> trm -> trm -> Prop :=               
(* e[u] ≡ t *)
| ec_empty : forall t,
    e_empty [t] == t                                      
(* ⦰[t] ≡ t *)
| ec_val : forall e u t v x,
    ~ In x (vars e) ->
    e[u] == (open_trm x t) ->
    (e_let_val x v e) [u] == (trm_let (trm_val v) t)
(* let x = v in e[u] ≡ let x=v in t *)
(* (e,x=v)[u] ≡ let x=v in t *)
| ec_trm : forall u t x e,
    ~ In x (vars e) ->
    (e_let_trm x (open_trm x t)) [u] == (trm_let u t)
(* let x = [u] in t ≡ let x=u in t *)
where "e '[' u ']' '==' t" := (ec_app e u t).

Reserved Notation "t1 '=>' t2" (at level 10).
Inductive ec_red : trm -> trm -> Prop :=
| red_term : forall t t' e et et',
    t => t' ->
    e[t] == et ->
    e[t'] == et' ->
    et => et'
| red_apply : forall x e y t T t1 t2,
    ~ In x (vars e) ->
    (e_let_val x (val_lambda T t) e) [ (trm_app (avar_f x) (avar_f y)) ] == t1 ->
    (e_let_val x (val_lambda T t) e) [ (open_trm y t) ] == t2 ->
    t1 => t2
| red_project : forall x e a t ds T t1 t2,
    ~ In x (vars e) ->
    defs_has (open_defs x ds) (def_trm a t) ->
    (e_let_val x (val_new T ds) e) [ (trm_sel (avar_f x) a) ] == t1 ->
    (e_let_val x (val_new T ds) e) [ t ] == t2 ->
    t1 => t2
| red_let_var : forall y t,
    trm_let (trm_var (avar_f y)) t => (open_trm y t)
| red_let_let : forall s t u,
    trm_let (trm_let s t) u => (trm_let s (trm_let t u))
where "t1 '=>' t2 " := (ec_red t1 t2).

Reserved Notation "e '[[' G ']]' '==' G'" (at level 10).
Inductive eg_app : ec -> ctx -> ctx -> Prop :=
| eg_empty : forall G, e_empty [[G]] == G
| eg_val : forall G x e (v: val) T G',
    ~ In x (vars e) ->
    x # G ->
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
  apply (precise_inert_typ H1).
Qed.

Lemma e_preserves_typing : forall G e t et T eG,
    e[t] == et ->
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
| nf_let: forall v n, normal_form n -> normal_form (trm_let v n).

Lemma progress_induction : forall e eG t T et,
  (* inert G -> *)
  e[[empty]] == eG ->
  eG |- t : T ->
  e[t] == et ->
  (normal_form et \/ exists t' et', (et => et' /\ e[t'] == et')).
Proof.
  introv HeG Ht Het.

(**********************)

  (* dependent induction e. *)
  (* - inversions Het. inversions HeG. dependent induction Ht; try solve [left; constructor]. *)
  (*   + (* apply (general_to_tight_typing Hin) in Ht1. *) *)
  (*     (* apply (invertible_typing_lemma Hin) in Ht1. *) *)
  (*     (* dependent induction Ht1. *) *)
  (*     (* * *) *)

  (*     (* apply (general_to_tight_typing Hin) in Ht2. *) *)
  (*     specialize (IHHt1 Hin). specialize (IHHt2 Hin). *)
  (*     destruct IHHt1; destruct IHHt2. *)
  (*     * right. *)
  (*       (* pick_fresh z'. *) *)
  (*       (* pose proof (ec_val e_empty (open_trm z'  *) *)
  (*       (* exists (open_trm y t). *) *)
  (*       admit. *)
  (*     * admit. *)
  (*     * admit. *)
  (*     * destruct H as (t1 & et1 & H1 & H1'). *)
  (*       destruct H0 as (t2 & et2 & H2 & H2'). *)
  (*       inversions H1'. inversions H2'. *)
  (*       inversions H1. *)
  (*   + *)
  
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
Admitted.

Lemma progress : forall t T,
  empty |- t : T ->
  (normal_form t \/ exists t', t => t').
Proof.
  intros.
  assert (normal_form t \/ exists t' et', (t => et' /\ e_empty[t'] == et')). {
    apply progress_induction with (eG := empty) (t := t) (T := T); 
      try constructor; try assumption.
  }
  destruct H0. 
  - left. assumption.
  - destruct H0 as (t' & et & ? & _). right. exists et. assumption.
Qed.

Lemma preservation : forall G t T t',
  inert G ->
  G |- t : T ->
  t => t' ->
  G |- t' : T.
Proof.
  introv Hin Ht Htt'. gen t'. 
  dependent induction Ht; intros.
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
  - (* clear IHHt H0. *) 
    (* dependent induction Htt'. *)
    (* + inversions H1; inversions H2. *)
    (*   * eapply IHHtt'; eauto. *)
    (*   * pose proof (ty_let u Ht H). *)
    (* + inversions H1. inversions H0. inversions H11. *)
    admit.
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
