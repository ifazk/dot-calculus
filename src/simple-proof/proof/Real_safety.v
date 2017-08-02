Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Narrowing.
Require Import Helper_lemmas.
Require Import Precise_types.
Require Import Substitution.
Require Import Canonical_forms.
Require Import Safety.
Require Import Renaming.
Require Import Invertible_typing.
Require Import General_to_tight.

(* TODO move to definitions *)
Definition close_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => If x = u then avar_b k else avar_f x
  end.

Fixpoint close_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (close_rec_dec k u D)
  | typ_and T1 T2  => typ_and (close_rec_typ k u T1) (close_rec_typ k u T2)
  | typ_sel x L    => typ_sel (close_rec_avar k u x) L
  | typ_bnd T      => typ_bnd (close_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (close_rec_typ k u T1) (close_rec_typ (S k) u T2)
  end
with close_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (close_rec_typ k u T) (close_rec_typ k u U)
  | dec_trm m T   => dec_trm m (close_rec_typ k u T)
  end.

Fixpoint close_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (close_rec_avar k u a)
  | trm_val v      => trm_val (close_rec_val k u v)
  | trm_sel v m    => trm_sel (close_rec_avar k u v) m
  | trm_app f a    => trm_app (close_rec_avar k u f) (close_rec_avar k u a)
  | trm_let t1 t2  => trm_let (close_rec_trm k u t1) (close_rec_trm (S k) u t2)
  end
with close_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds   => val_new (close_rec_typ (S k) u T) (close_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (close_rec_typ k u T) (close_rec_trm (S k) u e)
  end
with close_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (close_rec_typ k u T)
  | def_trm m e => def_trm m (close_rec_trm k u e)
  end
with close_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil       => defs_nil
  | defs_cons tl d => defs_cons (close_rec_defs k u tl) (close_rec_def k u d)
  end.

Definition close_avar u a := close_rec_avar  0 u a.
Definition close_typ  u t := close_rec_typ   0 u t.
Definition close_dec  u D := close_rec_dec   0 u D.
Definition close_trm  u e := close_rec_trm   0 u e.
Definition close_val  u v := close_rec_val   0 u v.
Definition close_def  u d := close_rec_def   0 u d.
Definition close_defs u l := close_rec_defs  0 u l.

Fixpoint ec_trm_helper (e: ec) (s: sto) (t: trm) : trm :=
  match s with
  | nil => match e with
          | e_hole _ => t
          | e_term _ u => trm_let t u
          end
  | cons (x, v) s => trm_let (trm_val v) (close_trm x (ec_trm_helper e s t))
  end.

Fixpoint ec_trm (e: ec) (t: trm): trm := ec_trm_helper e (ec_sto e) t.

Inductive ec_trm' : ec -> trm -> trm -> Prop :=
| ec_trm_empty_hole : forall t,
    ec_trm' (e_hole empty) t t
| ec_trm_empty_term : forall t u,
    ec_trm' (e_term empty u) t (trm_let t u)
| ec_trm_sto_hole : forall x v s t t',
    x \notin ((fv_trm t') \u (dom s)) ->
    ec_trm' (e_hole s) t (open_trm x t') ->
    ec_trm' (e_hole (x ~ v & s)) t (trm_let (trm_val v) t')
| ec_trm_sto_term: forall x v s t t' u,
    x \notin ((fv_trm t') \u (dom s)) ->
    ec_trm' (e_term s u) t (open_trm x t') ->
    ec_trm' (e_term (x ~ v & s) u) t (trm_let (trm_val v) t').

Fixpoint ec_vars (e: ec) := from_list (keys (ec_sto e)).

Fixpoint max_ec (t': trm) : ec * trm :=
  match t' with
  | trm_let (trm_val v) u =>
    match max_ec u with
    | ((e_hole s), t) =>
      let x := (var_gen (fv_ec (e_hole s))) in
      ((e_hole (s & x ~ v)), (open_trm x t))
    | ((e_term s u), t) =>
      let x := (var_gen (fv_ec (e_term s u))) in
      ((e_term (s & x ~ v) u), (open_trm x t))
    end
  | trm_let t u => ((e_term nil u), t)
  | t => ((e_hole nil), t)
  end.

(* Coq doesn't accept this *)
(* Fixpoint max_ec' (t' : trm) : ec * trm := *)
(*   match t' with *)
(*   | trm_let (trm_val v) u => *)
(*     let x := (var_gen (fv_trm t')) in *)
(*     match max_ec' (open_trm x u) with *)
(*     | (e_hole s, t)    => (e_hole (s & x ~ v),    t) *)
(*     | (e_term s u', t) => (e_term (s & x ~ v) u', t) *)
(*     end *)
(*   | trm_let t u => (e_term empty u, t) *)
(*   | t => (e_hole empty, t) *)
(*   end. *)

Inductive max_ec': trm -> ec -> trm -> Prop :=
| max_ec_var : forall x,
    max_ec' (trm_var x) (e_hole empty) (trm_var x)
| max_ec_val : forall v,
    max_ec' (trm_val v) (e_hole empty) (trm_val v)
| max_ec_sel : forall x a,
    max_ec' (trm_sel x a) (e_hole empty) (trm_sel x a)
| max_ec_app : forall x y,
    max_ec' (trm_app x y) (e_hole empty) (trm_app x y)
| max_ec_let_var : forall x t,
    max_ec' (trm_let (trm_var x) t) (e_term empty t) (trm_var x)
| max_ec_let_sel : forall x a t,
    max_ec' (trm_let (trm_sel x a) t) (e_term empty t) (trm_sel x a)
| max_ec_let_app : forall x y t,
    max_ec' (trm_let (trm_app x y) t) (e_term empty t) (trm_app x y)
| max_ec_let_let : forall t' u' t,
    max_ec' (trm_let (trm_let t' u') t) (e_term empty t) (trm_let t' u')
| max_ec_let_val_hole : forall u s t v x,
    x \notin ((dom s) \u (fv_trm u) \u (fv_trm t) \u (fv_val v)) ->
    max_ec' (open_trm x u) (e_hole s) t ->
    max_ec' (trm_let (trm_val v) u) (e_hole (x ~ v & s)) t
| max_ec_let_val_term : forall u s u' t v x,
    x \notin ((dom s) \u (fv_trm u) \u (fv_trm u') \u (fv_trm t) \u (fv_val v)) ->
    max_ec' (open_trm x u) (e_term s u') t ->
    max_ec' (trm_let (trm_val v) u) (e_term (x ~ v & s) u') t.

(* Lemma max_ec'_open: forall u e t x, *)
(*     max_ec' u e t -> *)
(*     exists e' t', max_ec' (open_trm x u) e' t'. *)
(* Proof. *)
(*   intros. unfold open_trm. dependent induction H. *)
(*   - destruct x0. *)
(*     + simpl; case_if; repeat eexists; apply max_ec_var. *)
(*     + repeat eexists; apply max_ec_var. *)
(*   - destruct v. *)
(*     + simpl. repeat eexists; apply *)

Lemma max_ec'_all: forall u,
    exists e t, max_ec' u e t.
Proof.
  intros. induction u.
  - repeat eexists; apply max_ec_var.
  - repeat eexists; apply max_ec_val.
  - repeat eexists; apply max_ec_sel.
  - repeat eexists; apply max_ec_app.
  - destruct u1.
    + repeat eexists; apply max_ec_let_var.
    + admit.
    + repeat eexists; apply max_ec_let_sel.
    + repeat eexists; apply max_ec_let_app.
    + repeat eexists; apply max_ec_let_let.
Qed.

Lemma ec_term_val: forall u s t v,
    max_ec' u (e_term s t) (trm_val v) -> False.
Proof.
  intros. dependent induction H. eapply IHmax_ec'; auto.
Qed.

Lemma ec_hole_let: forall t u u' s,
    max_ec' u' (e_hole s) (trm_let t u) -> False.
Proof.
  intros. dependent induction H. eapply IHmax_ec'; auto.
Qed.

Lemma empty_before_inv: forall A x (v : A) E,
    x ~ v & E = empty -> False.
Proof.
  intros.
  destruct E using env_ind.
  - rewrite concat_empty_r in H. false empty_single_inv. symmetry. eauto.
  - rewrite concat_assoc in H. false empty_push_inv. symmetry. eauto.
Qed.

Lemma eq_before_inv: forall A x1 x2 (v1 v2 : A) E1 E2,
    x1 ~ v1 & E1 = x2 ~ v2 & E2 -> x1 = x2 /\ v1 = v2 /\ E1 = E2.
Proof.
  intros. gen E2. destruct E1 using env_ind; intros.
  - rewrite concat_empty_r in H. destruct E2 using env_ind.
    + rewrite concat_empty_r in H. apply eq_single_inv in H. split*.
    + rewrite concat_assoc in H. replace (x1 ~ v1) with (empty & x1 ~ v1) in H.
      * apply eq_push_inv in H. destruct H as [_ [_ ?]].
        rewrite <- concat_empty_l in H. rewrite concat_assoc in H.
        false* empty_middle_inv.
      * rewrite~ concat_empty_l.
  - rewrite concat_assoc in *.
    gen E1. destruct E2 using env_ind; intros.
    + rewrite concat_empty_r in H. replace (x2 ~ v2) with (empty & x2 ~ v2) in H.
      * apply eq_push_inv in H. destruct H as [_ [_ ?]]. symmetry in H.
        rewrite <- concat_empty_l in H. rewrite concat_assoc in H.
        false* empty_middle_inv.
      * rewrite~ concat_empty_l.
    + rewrite concat_assoc in H. apply eq_push_inv in H.
      destruct H as [? [? ?]].
      specialize (IHE1 _ H1) as [? [? ?]]. subst~.
Qed.

Lemma notin_before_inv: forall A x (v : A) E,
    x # (x ~ v & E) -> False.
Proof.
  intros. induction E using env_ind.
  - rewrite concat_empty_r in H.
    rewrite dom_single in H. false* notin_same.
  - rewrite concat_assoc in H. apply~ IHE.
Qed.

Lemma binds_before_eq: forall (A : Type) (x : var) (v : A) (E : env A),
    ok (x ~ v & E) ->
    binds x v (x ~ v & E).
Proof.
  intros. induction E using env_ind.
  - rewrite concat_empty_r. apply binds_single_eq.
  - rewrite concat_assoc in *. destruct (classicT (x = x0)).
    + subst. apply ok_push_inv in H. destruct H. auto.
    + apply~ binds_push_neq.
Qed.

Lemma binds_before_eq_inv: forall (A : Type) (x : var) (v1 v2 : A) (E : env A),
    ok (x ~ v2 & E) ->
    binds x v1 (x ~ v2 & E) -> v1 = v2.
Proof.
  intros. induction E using env_ind.
  - rewrite concat_empty_r in *. apply binds_single_eq_inv in H0. assumption.
  - rewrite concat_assoc in H. destruct (classicT (x = x0)).
    + subst. apply ok_push_inv in H. destruct H. auto.
      false~ notin_before_inv.
    + rewrite concat_assoc in H0. apply binds_push_neq_inv in H0; auto.
Qed.

Lemma ec_inverse'': forall e t u u',
    max_ec' u e t ->
    ec_trm' e t u' ->
    u = u'.
Proof.
  intros. gen u'.
  dependent induction H; intros; try solve [inversions~ H0; false empty_before_inv; symmetry; eauto].
  - gen u. dependent induction H1; intros.
    + symmetry in x. false* empty_before_inv.
    + destruct (eq_before_inv x) as [? [? ?]]. subst.
      f_equal. specialize (IHmax_ec' _ H1).
      eapply (proj41 open_fresh_trm_val_def_defs_injective); eauto.
  - dependent induction H1.
    + symmetry in x. false* empty_before_inv.
    + destruct (eq_before_inv x) as [? [? ?]]. subst.
      f_equal. specialize (IHmax_ec' _ H1).
      eapply (proj41 open_fresh_trm_val_def_defs_injective); eauto.
Qed.

Lemma lc_sto_before: forall x v s,
    lc_val v ->
    lc_sto s ->
    lc_sto (x ~ v & s).
Proof.
  intros. induction s using env_ind.
  - rewrite concat_empty_r. rewrite <- concat_empty_l. constructor~.
  - rewrite concat_assoc. inversions H0.
    + false* empty_push_inv.
    + apply eq_push_inv in H1. destruct H1 as [? [? ?]]. subst.
      constructor~.
Qed.

Lemma max_ec_preserves_lc: forall u e t,
    lc_trm u ->
    max_ec' u e t ->
    lc_term e t.
Proof.
  intros.
  dependent induction H0; inversions H; try solve [constructor~].
  - specialize (H5 x). specialize (IHmax_ec' H5).
    inversions IHmax_ec'. inversions H. inversions H4.
    repeat constructor~. apply~ lc_sto_before.
  - specialize (H5 x). specialize (IHmax_ec' H5).
    inversions IHmax_ec'. inversions H. inversions H4.
    repeat constructor~. apply~ lc_sto_before.
Qed.

Definition ctx_sto (s: sto) (G: ctx): Prop :=
  ok s /\
  ok G /\
  forall x v,
    binds x v s ->
    exists T,
      binds x T G /\
      G |- trm_val v : T.

Inductive ctx_sto' : ctx -> ctx -> sto -> Prop :=
| ctx_sto_empty: forall G,
    ok G ->
    ctx_sto' G empty empty
| ctx_sto_push: forall G G' s x v T,
    ctx_sto' G G' s ->
    x # G ->
    x # G' ->
    x # s ->
    x \notin (fv_ctx_types G) ->
    G & G' |- trm_val v : T ->
    ctx_sto' G (G' & x ~ T) (s & x ~ v).

Hint Constructors ctx_sto'.

Lemma ctx_sto_ctx_ok : forall G G' s,
    ctx_sto' G G' s ->
    ok G'.
Proof.
  introv Hcs. induction Hcs; auto.
Qed.

Lemma ctx_sto_sto_ok : forall G G' s,
    ctx_sto' G G' s ->
    ok s.
Proof.
  introv Hcs. induction Hcs; auto.
Qed.

(* Lemma ctx_sto_empty: forall G, *)
(*     ok G -> ctx_sto empty G. *)
(* Proof. *)
(*   unfold ctx_sto. intros. repeat split~. intros. *)
(*   false* binds_empty_inv. *)
(* Qed. *)

(* Hint Resolve ctx_sto_empty. *)

(* Lemma ctx_sto_push: forall s G x v T, *)
(*     ctx_sto s G -> *)
(*     G |- trm_val v : T -> *)
(*     x # G -> *)
(*     x # s -> *)
(*     ctx_sto (s & x ~ v) (G & x ~ T). *)
(* Proof. *)
(*   unfold ctx_sto. intros. destruct H as [Hoks [HokG ?]]. *)
(*   repeat split~. intros. *)
(*   destruct (classicT (x0 = x)). *)
(*   - subst. apply binds_push_eq_inv in H3. subst. exists T. *)
(*     repeat split~. apply~ weaken_ty_trm. *)
(*   - apply (binds_push_neq_inv H3) in n. *)
(*     assert (ok s) by auto. assert (ok G) by auto. *)
(*     destruct (H x0 v0 n) as [T' [Hbi Ht]]. *)
(*     exists T'. repeat split~. *)
(*     + apply~ binds_concat_left_ok. *)
(*     + apply~ weaken_ty_trm. *)
(* Qed. *)

Lemma ok_switch: forall (A : Type) (E F : env A) x T,
    ok (E & x ~ T & F) <-> ok (E & F & x ~ T).
Proof.
  intros. split; intros.
  {
    induction F using env_ind.
    - rewrite concat_empty_r in *. assumption.
    - rewrite concat_assoc in *.
      destruct (ok_push_inv H).
      specialize (IHF H0). destruct (ok_push_inv IHF).
      apply~ ok_push.
  }
  {
    induction F using env_ind.
    - rewrite concat_empty_r in *. assumption.
    - rewrite concat_assoc in *.
      destruct (ok_push_inv H). destruct (ok_push_inv H0).
      constructor~.
  }
Qed.

Lemma ok_before_inv: forall (A : Type) (E : env A) (x : var) (v : A),
    ok (x ~ v & E) -> ok E /\ x # E.
Proof.
  intros. induction E using env_ind.
  - auto.
  - rewrite concat_assoc in H. apply ok_push_inv in H. destruct H.
    destruct (IHE H). split~.
Qed.

Lemma inert_push_inv: forall G x T,
    inert (G & x ~ T) -> inert G /\ inert_typ T /\ x # G.
Proof.
  intros. inversions H.
  - false* empty_push_inv.
  - apply eq_push_inv in H0. destruct H0 as [? [? ?]]. subst~.
Qed.

Lemma inert_switch: forall x T G,
    inert (G & x ~ T) ->
    inert (x ~ T & G).
Proof.
  introv Hin. induction G using env_ind.
  - rewrite concat_empty_r. rewrite concat_empty_l in Hin. assumption.
  - destruct (inert_push_inv Hin) as [Hin' [HinT Hx]].
    destruct (inert_push_inv Hin') as [Hin'' [HinT' Hx']].
    rewrite concat_assoc. apply~ inert_all.
Qed.

Lemma ctx_sto_notin_dom : forall x G G' s,
    x # s ->
    ctx_sto' G G' s ->
    x # G'.
Proof.
  introv Hs Hcs. induction Hcs; auto.
Qed.

Lemma move_ctx_sto: forall G G' s x v T V,
    x # G ->
    x # G' ->
    x # s ->
    x \notin (fv_ctx_types G) ->
    ok G ->
    ok G' ->
    ok s ->
    ok (G & G') ->
    G |- trm_val v : V ->
    G |- V <: T ->
    ctx_sto' (G & x ~ T) G' s ->
    ctx_sto' G (x ~ V & G') (x ~ v & s).
Proof.
  introv HnotinG HnotinG' Hnotins HnotinGTypes HokG HokG' Hoks HokGG' Ht Hs.
  introv Hcs.
  dependent induction Hcs.
  - repeat rewrite concat_empty_r.
    replace (x ~ V) with (empty & x ~ V); try solve [rewrite~ concat_empty_l].
    replace (x ~ v) with (empty & x ~ v); try solve [rewrite~ concat_empty_l].
    constructor~. rewrite~ concat_empty_r.
  - assert (x # G'0) by auto. assert (x # s0) by auto.
    assert (ok G'0) by auto. assert (ok s0) by auto.
    rewrite concat_assoc in HokGG'. assert (ok (G & G'0)) by auto.
    specialize (IHHcs T x s0 H5 H7 G'0 H4 H6 G HnotinG HnotinGTypes HokG H8 Ht Hs JMeq_refl JMeq_refl JMeq_refl).
    repeat rewrite concat_assoc.
    constructor~.
    { rewrite~ fv_ctx_types_push_eq in H2. }
    {
      rewrite concat_assoc.
      eapply (proj41 narrow_rules); eauto.
      + apply ok_switch. constructor~.
      + apply subenv_concat.
        * apply~ subenv_last.
        * apply ok_switch. constructor~.
        * apply ok_switch. constructor~.
    }
Qed.

Lemma ctx_sto_exists: forall e t u U G,
    ec_trm' e t u ->
    ok G ->
    ok (ec_sto e) ->
    (forall x v, binds x v (ec_sto e) -> x # G) ->
    (forall x v, binds x v (ec_sto e) -> x \notin (fv_ctx_types G)) ->
    G |- u : U ->
    exists G' T,
      ok (G & G') /\
      inert G' /\
      ctx_sto' G G' (ec_sto e) /\
      G & G' |- t : T.
(* Use the fact that all the (let x=v in) in u have to type. Use
val_typing lemma from the existing proof to show that they have a precise
type. This type is inert.
*)
Proof.
  introv Hec HokG Hoks HeG HeGT Ht. gen G U Hoks. dependent induction Hec; intros.
  - exists (@empty typ) U. rewrite concat_empty_r. repeat split~.
  - dependent induction Ht.
    + exists (@empty typ) T. rewrite concat_empty_r. repeat split~.
    + apply~ IHHt.
  - dependent induction Ht.
    + clear IHHt H0. destruct (val_typing Ht) as [V [Hv Hs]].
      pick_fresh z.
      assert (Hz: z \notin L) by auto.
      specialize (H1 z Hz).
      assert (HG: x # G).
      {
        apply HeG with (v0:=v). simpl in *. apply~ binds_before_eq.
      }
      assert (Ht': G & x ~ T |- open_trm x t' : U).
      {
        assert (Hopent: z \notin (fv_trm (open_trm x t'))) by admit.
        assert (G = (map_keys (rename_var z x) G)) by rewrite~ map_keys_notin.
        assert (G = rename_ctx z x G).
        {
          unfold rename_ctx. rewrite <- H0. rewrite~ subst_fresh_ctx.
        }
        assert (x = (rename_var z x z)).
        {
          unfold rename_var. case_if~.
        }
        assert (G & x ~ T = rename_ctx z x (G & z ~ T)).
        {
          unfold rename_ctx.
          rewrite map_keys_push. rewrite <- H0. rewrite <- H3.
          rewrite~ subst_fresh_ctx.
          rewrite~ fv_ctx_types_push_eq.
        }

        rewrite <- subst_fresh_typ with (x:=z) (y:=x); auto.
        rewrite subst_intro_trm with (x:=z); auto.
        rewrite H4.
        eapply (proj41 (renaming_gen z x)); eauto.
      }
      assert (x # s) by auto.
      assert (HokG': ok (G & x ~ T)) by auto.
      assert (Hoks': ok s).
      {
        apply ok_before_inv in Hoks. destruct~ Hoks.
      }
      assert (HeG': (forall x' v, binds x' v (ec_sto (e_hole s)) -> x' # (G & x ~ T))).
      {
        intros. destruct (classicT (x' = x)).
        - subst. (* x in s, and s & x is ok? *) admit.
        - admit.
      }
      assert (HeGT': (forall x' v, binds x' v (ec_sto (e_hole s)) -> x' \notin fv_ctx_types (G & x ~ T))) by admit.
      destruct (IHHec _ HokG' HeG' HeGT' _ Ht' Hoks') as [G' [T' [Hok'' [Hin' [Hcs Ht'']]]]].
      pose proof (ctx_sto_notin_dom H0 Hcs).
      exists (x ~ V & G') T'. repeat split~.
      * rewrite concat_assoc. eapply ok_middle_change; eauto.
      * apply inert_switch. constructor~. eapply precise_inert_typ; eauto.
      * eapply move_ctx_sto; eauto.
        apply HeGT with (v0:=v). apply~ binds_before_eq.
        apply~ precise_to_general.
      * rewrite concat_assoc. eapply (proj41 narrow_rules); eauto.
        eapply ok_middle_change; eauto.
        apply subenv_concat. apply~ subenv_last. assumption.
        eapply ok_middle_change; eauto.
    + eapply IHHt; eauto.
  - admit. (* same as before *)
Qed.

(* Lemma hole_term: forall s t u, *)
(*     ec_trm (e_hole s) (trm_let t u) = ec_trm (e_term s u) t. *)
(* Proof. *)
(*   intros s. *)
(*   simpl. *)
(*   induction s using env_ind. *)
(*   - intros t u. *)
(*     unfold ec_trm_helper; rewrite? empty_def; auto. *)
(*   - intros t u. *)
(*     replace (ec_trm_helper (e_hole (s & x ~ v)) (s & x ~ v) (trm_let t u)) *)
(*       with (ec_trm_helper (e_hole empty) (s & x ~ v) (trm_let t u)) *)
(*       by (apply ec_trm_helper_e; auto). *)
(*     replace (ec_trm_helper (e_term (s & x ~ v) u) (s & x ~ v) t) *)
(*       with (ec_trm_helper (e_term empty u) (s & x ~ v) t) *)
(*       by (apply ec_trm_helper_e; auto). *)
(*     unfold ec_trm_helper; rewrite? single_def, concat_def; unfold LibList.append; simpl. *)
(*     apply f_equal, f_equal. *)
(*     replace (fix ec_trm_helper (e : ec) (s0 : sto) (t0 : trm) {struct s0} : trm := *)
(*                match s0 with *)
(*                | nil => match e with *)
(*                        | e_hole _ => t0 *)
(*                        | e_term _ u0 => trm_let t0 u0 *)
(*                        end *)
(*                | ((x0, v0) :: s1)%list => trm_let (trm_val v0) (close_trm x0 (ec_trm_helper e s1 t0)) *)
(*                end) with ec_trm_helper by auto. *)
(*     replace (ec_trm_helper (e_hole empty) s (trm_let t u)) *)
(*       with (ec_trm_helper (e_hole s) s (trm_let t u)) *)
(*       by (apply ec_trm_helper_e; auto). *)
(*     replace (ec_trm_helper (e_term empty u) s t) *)
(*       with (ec_trm_helper (e_term s u) s t) *)
(*       by (apply ec_trm_helper_e; auto). *)
(*     auto. *)
(* Qed. *)


Reserved Notation "e1 '/' t1 '||->' e2 '/' t2" (at level 40, e2 at level 39).

Inductive red' : ec -> trm -> ec -> trm -> Prop :=
(** [e(x) = lambda(T)t]  #<br>#
    [――――――――――――]  #<br>#
    [e | x y |-> e | t^y]  *)
| red_apply : forall x y e T t,
    lc_ec e ->
    lc_trm (open_trm y t) ->
    binds x (val_lambda T t) (ec_sto e) ->
    e / trm_app (avar_f x) (avar_f y) ||-> e / open_trm y t
(** [e(x) = nu(T)...{a = t}...]  #<br>#
    [――――――――――――――――――――――――]  #<br>#
    [e | x.a |-> e | t]  *)
| red_project : forall x a e T ds t,
    lc_ec e ->
    lc_trm t ->
    binds x (val_new T ds) (ec_sto e) ->
    defs_has (open_defs x ds) (def_trm a t) ->
    e / trm_sel (avar_f x) a ||-> e / t
(** [e[let x = [ ] in t] | y |-> e[ ] | t^y] *)
| red_let_var : forall x t s,
    lc_sto s ->
    lc_trm (open_trm x t) ->
    e_term s t / trm_var (avar_f x) ||-> e_hole s / open_trm x t
(** [e[let x = [ ] in t1] | let t2 in t3 |-> e[let x = [ ] in let t3 in t1] | t2] *)
| red_let_let : forall x s t1 t2 t3,
    lc_sto s ->
    lc_trm (open_trm x t1) ->
    lc_trm t2 ->
    lc_trm (open_trm x t3) ->
    e_term s t1 / trm_let t2 t3 ||-> e_term s (trm_let t3 t1) / t2
where "t1 '/' st1 '||->' t2 '/' st2" := (red' t1 st1 t2 st2).

(* Lemma red_term_to_hole: forall s u t t', *)
(*     e_term s u / t ||-> e_term s u / t' -> *)
(*     e_hole s / t ||-> e_hole s / t'. *)
(* Proof. *)
(*   intros. dependent induction H. *)
(*   - eapply red_apply; eauto. inversion~ H. *)
(*   - eapply red_project; eauto. inversion~ H. *)
(*   - induction u; inversions x. *)
(*     eapply IHu2; eauto. inversions H0. *)

(* Lemma canonical_forms_fun': forall G s x T U, *)
(*     inert G -> *)
(*     ctx_sto s G -> *)
(*     G |- trm_var (avar_f x) : typ_all T U -> *)
(*     exists L T' t, *)
(*       binds x (val_lambda T' t) s /\ *)
(*       G |- T <: T' /\ *)
(*       (forall y, y \notin L -> G & y ~ T |- open_trm y t : open_typ y U). *)
(* Proof. *)
(*   introv Hin Hcs Ht. *)
(*   unfold ctx_sto in Hcs. *)
(*   destruct (var_typ_all_to_binds Hin Ht) as [L [S [T' [BiG [Hs1 Hs2]]]]]. *)
(*   destruct (val_ *)

Lemma max_ec_trm: forall u e t,
    max_ec' u e t ->
    ec_trm' e t u.
Proof.
  intros. dependent induction H; try constructor; eauto.
Qed.

Definition ctx_sto'' G s :=
  (forall x T, binds x T G -> exists v, binds x v s /\ G |- trm_val v : T)
  (* /\ *)
  (* (forall x v, binds x v s -> exists T, binds x T G /\ G |- trm_val v : T) *)
.

Lemma ctx_sto_correspondence : forall G s,
    ctx_sto' empty G s -> ctx_sto'' G s.
Proof.
  intros. dependent induction H; unfold ctx_sto''; intros.
  - false* binds_empty_inv.
  - destruct (classicT (x0 = x)).
    + subst. exists v. apply binds_push_eq_inv in H5. subst.
      split~. rewrite concat_empty_l in H4. apply~ weaken_ty_trm.
      constructor~. apply (ctx_sto_ctx_ok H).
    + specialize (IHctx_sto' JMeq_refl). unfold ctx_sto'' in IHctx_sto'.
      destruct (IHctx_sto' _ _ (binds_push_neq_inv H5 n)) as [v' [Bi Ht]].
      exists v'. split~. apply~ weaken_ty_trm.
      constructor~. apply (ctx_sto_ctx_ok H).
Qed.

Lemma canonical1: forall G s x T U,
    inert G ->
    ctx_sto'' G s ->
    G |- trm_var (avar_f x) : typ_all T U ->
    (exists L T' t,
        binds x (val_lambda T' t) s /\
        G |- T <: T' /\
        (forall y, y \notin L -> G & y ~ T |- open_trm y t : open_typ y U)).
Proof.
  introv Hin Hcs Ht.
  destruct (var_typ_all_to_binds Hin Ht) as [L [S [T' [BiG [Hs1 Hs2]]]]].
  unfold ctx_sto'' in Hcs. specialize (Hcs _ _ BiG) as [v [Bis Htv]].
  destruct (val_typ_all_to_lambda Hin Htv) as [L' [S' [t [Heq [Hs1' Hs2']]]]].
  subst. exists (L \u L' \u (dom G)) S' t. repeat split~.
  - eapply subtyp_trans; eauto.
  - intros. assert (HL: y \notin L) by auto. specialize (Hs2 y HL).
    assert (HL': y \notin L') by auto. specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    + eapply ty_sub; eauto.
    + apply~ subenv_last.
Qed.

Lemma canonical2: forall G s x a T,
    inert G ->
    ctx_sto'' G s ->
    G |- trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    (exists S ds t,
        binds x (val_new S ds) s /\
        defs_has (open_defs x ds) (def_trm a t) /\
        G |- t : T).
Proof.
  introv Hin Hcs Ht.
  destruct (var_typ_rcd_to_binds Hin Ht) as [S [T' [BiG [Hr Hs]]]].
  unfold ctx_sto'' in Hcs. specialize (Hcs _ _ BiG) as [v [Bis Htv]].
  apply ty_var in BiG. apply ty_rec_elim in BiG.
  destruct (val_mu_to_new Hin Htv BiG Hr) as [t [ds [Heq [Hdefs Ht']]]].
  subst. exists S ds t. repeat split~. eapply ty_sub; eauto.
Qed.

Lemma lc_sto_lc_val: forall s x v,
    lc_sto s ->
    binds x v s ->
    lc_val v.
Proof.
  intros. induction s using env_ind.
  - false* binds_empty_inv.
  - apply lc_sto_push_inv in H. destruct H. destruct (classicT (x = x0)).
    + subst. apply binds_push_eq_inv in H0. subst~.
    + apply~ IHs. apply (binds_push_neq_inv H0 n).
Qed.

Lemma defs_neq_inv: forall ds d d',
    defs_has (defs_cons ds d) d' ->
    d <> d' ->
    defs_has ds d'.
Proof.
  intros. unfold defs_has in *. simpl in H. case_if~.
Qed.
Lemma lc_defs_has: forall x ds a t,
    lc_defs (open_defs x ds) ->
    defs_has (open_defs x ds) (def_trm a t) ->
    lc_trm t.
Proof.
  intros.
  induction H.
  - inversions H0.
  - destruct (classicT (d = (def_trm a t))).
    + subst. inversions~ H1.
    + apply IHlc_defs. eapply defs_neq_inv; eauto.
Qed.

(* lc u -> lc t *)
Lemma progress : forall u U e t,
    lc_trm u ->
    empty |- u : U ->
    max_ec' u e t ->
    normal_form e t \/ exists e' t', e / t ||-> e' / t'.
(* Proof sketch:

Use ctx_sto_exists on (ec_sto e) to get G.
Then do the same things as in old progress theorem.
We no longer have congruence reduction rules.
In their place, use the fact that max_ec never returns a let term that would need them.
*)
Proof.
  introv Hlc Ht Hmax.
  assert (ok (@empty typ)) by auto.
  destruct (ctx_sto_exists (max_ec_trm Hmax) H Ht) as [G [T [Hok [Hin [Hcs Ht']]]]].
  rewrite concat_empty_l in Ht'.
  apply ctx_sto_correspondence in Hcs.
  destruct e; simpl in *.
  {
    dependent induction Ht'; try solve [left; auto].
    - destruct (canonical1 Hin Hcs Ht'1) as [L [T' [t [Bis [Hs Ht']]]]].
      right. apply (max_ec_preserves_lc Hlc) in Hmax.
      inversions Hmax. inversions H0.
      pose proof (lc_sto_lc_val H3 Bis). inversions H0.
      repeat eexists. apply* red_apply.
    - destruct (canonical2 Hin Hcs Ht') as [S [ds [t [Bis [Has Ht'']]]]].
      right. apply (max_ec_preserves_lc Hlc) in Hmax.
      inversions Hmax. inversions H0.
      pose proof (lc_sto_lc_val H3 Bis). inversions H0.
      specialize (H6 x). pose proof (lc_defs_has _ _ H6 Has).
      repeat eexists. apply red_project with (T:=S) (ds:=ds) (t:=t); auto.
    - false* ec_hole_let.
    - apply~ IHHt'.
  }
  {
    dependent induction Ht'; right.
    - apply (max_ec_preserves_lc Hlc) in Hmax. inversions Hmax.
      inversions H1. repeat eexists; apply red_let_var; auto.
    - false* ec_term_val.
    - destruct (canonical1 Hin Hcs Ht'1) as [L [T' [t [Bis [Hs Ht']]]]].
      apply (max_ec_preserves_lc Hlc) in Hmax.
      inversions Hmax. inversions H0.
      pose proof (lc_sto_lc_val H4 Bis). inversions H0.
      repeat eexists. apply red_apply with (T:=T') (t:=t); auto.
    - false* ec_term_val.
    - destruct (canonical2 Hin Hcs Ht') as [S [ds [t [Bis [Has Ht'']]]]].
      apply (max_ec_preserves_lc Hlc) in Hmax.
      inversions Hmax. inversions H0.
      pose proof (lc_sto_lc_val H4 Bis). inversions H0.
      specialize (H7 x). pose proof (lc_defs_has _ _ H7 Has).
      repeat eexists. apply red_project with (T:=S) (ds:=ds) (t:=t); auto.
    - apply (max_ec_preserves_lc Hlc) in Hmax. inversions Hmax.
      inversions H2. inversions H3.
      pick_fresh z.
      repeat eexists; apply red_let_let with (x:=z); auto.
    - apply (max_ec_preserves_lc Hlc) in Hmax. inversions Hmax.
      inversions H0.
      repeat eexists; apply red_let_var; auto.
    - apply (max_ec_preserves_lc Hlc) in Hmax. inversions Hmax.
      inversions H0.
      repeat eexists; apply red_let_var; auto.
    - apply (max_ec_preserves_lc Hlc) in Hmax. inversions Hmax.
      inversions H0.
      repeat eexists; apply red_let_var; auto.
    - destruct* (IHHt' Hmax Hok Hin Hcs).
  }
Qed.

(* I think this one is false. Replacing both hole_preserves_type and term_preserves_type
with ec_preserves_type below.

Lemma hole_preserves_type : forall s t u t' u' U G,
    ec_trm (e_hole s) t = u ->
    ec_trm (e_hole s) t' = u' ->
    empty |- u : U ->
    ctx_sto s G ->
    G |- t' : U ->
    empty |- u' : U.
Admitted.
*)

(*
I don't know whether the following lemma is true or not.
I don't know whether we will need the following lemma or not.

Lemma term_preserves_type : forall s t u t' u' U G U' t'',
    ec_trm (e_term s t'') t = u ->
    ec_trm (e_term s t'') t' = u' ->
    empty |- u : U ->
    ctx_sto s G ->
    G |- t : U' ->
    G |- t' : U' ->
    empty |- u' : U.
Admitted.
*)

Lemma ec_preserves_type : forall s t u t' u' U G,
    ec_trm (e_hole s) t = u ->
    ec_trm (e_hole s) t' = u' ->
    empty |- u : U ->
    ctx_sto s G ->
    (forall T, G |- t : T -> G |- t' : T) ->
    empty |- u' : U.
Admitted.

Lemma ec_preserves_type' : forall e t u t' u' U G G',
    ec_trm' e t u ->
    ec_trm' e t' u' ->
    G |- u : U ->
    ctx_sto' G G' (ec_sto e) ->
    (forall T, G & G' |- t : T -> G & G' |- t' : T) ->
    G |- u' : U.
Admitted.

Lemma red_preserves_sto : forall e t e' t',
    e / t ||-> e' / t' ->
    ec_sto e = ec_sto e'.
Proof. introv Hred. inversion~ Hred. Qed.

Lemma ctx_sto_empty_sto_inv: forall G G',
    ctx_sto' G G' empty ->
    G' = empty.
Proof.
  intros. inversions H.
  - reflexivity.
  - symmetry in H0. false* empty_push_inv.
Qed.

Lemma term_to_hole: forall s t t' u,
    ec_trm' (e_term s t') t u ->
    ec_trm' (e_hole s) (trm_let t t') u.
Proof.
  intros. dependent induction H; constructor~.
Qed.

Lemma preservation : forall u U e t e' t' u',
    lc_trm u ->
    empty |- u : U ->
    ec_trm' e t u ->
    e / t ||-> e' / t' ->
    ec_trm' e' t' u' ->
    empty |- u' : U (* /\ lc_trm u' *).
Proof.
  introv Hlc Ht Hec Hred Hec'.
  assert (ok (@empty typ)) by auto.
  destruct (ctx_sto_exists Hec H Ht) as [G [T [Hok [Hin [Hcs Ht']]]]].
  lets Hcs': (ctx_sto_correspondence Hcs).
  rewrite concat_empty_l in *. destruct e.
  {
    destruct e'; try solve [inversions Hred].
    pose proof (red_preserves_sto Hred). simpl in *. subst s0.
    dependent induction Ht'; try solve [inversion Hred].
    - inversions Hred. simpl in *.
      apply (ec_preserves_type' Hec Hec' Ht Hcs).
      intros. rewrite concat_empty_l in *.
      dependent induction H0.
      + clear IHty_trm1 IHty_trm2.
        destruct (canonical1 Hin Hcs' H0_) as [L [T' [t' [Bis [Hs Ht']]]]].
        apply (binds_func H5) in Bis. inversions Bis.
        pick_fresh y. assert (HL: y \notin L) by auto.
        specialize (Ht' y HL).
        rewrite subst_intro_typ with (x:=y); auto.
        rewrite subst_intro_trm with (x:=y); auto.
        eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ.
      + eapply ty_sub; eauto.
    - inversions Hred. simpl in *.
      apply (ec_preserves_type' Hec Hec' Ht Hcs).
      intros. rewrite concat_empty_l in *.
      dependent induction H0.
      + clear IHty_trm.
        destruct (canonical2 Hin Hcs' H0) as [S [ds' [t [Bis [Has Ht'']]]]].
        apply (binds_func H5) in Bis. inversions Bis.
        rewrite <- (defs_has_inv Has H6). assumption.
      + eapply ty_sub; eauto.
    - eapply IHHt'; eauto.
  }
  {
    destruct e'.
    - apply term_to_hole in Hec.
      inversions Hred. apply (ec_preserves_type' Hec Hec' Ht Hcs).
      intros. rewrite concat_empty_l in *.
      dependent induction H0.
      + clear H2 IHty_trm.
        pick_fresh y.
        rewrite subst_intro_trm with (x:=y); auto.
        rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
        eapply subst_ty_trm; auto. rewrite~ subst_fresh_typ.
      + eapply ty_sub; eauto.
    - inversions Hred.
      + apply (ec_preserves_type' Hec Hec' Ht Hcs).
        intros. rewrite concat_empty_l in *.
        dependent induction H0.
        * clear IHty_trm1 IHty_trm2.
          destruct (canonical1 Hin Hcs' H0_) as [L [T' [t' [Bis [Hs Ht'']]]]].
          apply (binds_func H7) in Bis. inversions Bis.
          pick_fresh z. assert (HL: z \notin L) by auto.
          specialize (Ht'' z HL).
          rewrite subst_intro_typ with (x:=z); auto.
          rewrite subst_intro_trm with (x:=z); auto.
          eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ.
        * eapply ty_sub; eauto.
      + apply (ec_preserves_type' Hec Hec' Ht Hcs).
        intros. rewrite concat_empty_l in *.
        dependent induction H0.
        * clear IHty_trm.
          destruct (canonical2 Hin Hcs' H0) as [S [ds' [t [Bis [Has Ht'']]]]].
          apply (binds_func H6) in Bis. inversions Bis.
          rewrite <- (defs_has_inv Has H8). assumption.
        * eapply ty_sub; eauto.
      + apply term_to_hole in Hec.
        apply term_to_hole in Hec'.
        apply (ec_preserves_type' Hec Hec' Ht Hcs).
        intros. rewrite concat_empty_l in *.
        dependent induction H0.
        * clear H2 IHty_trm. gen L. dependent induction H0; intros.
          {
            clear H2 IHty_trm.
            apply_fresh ty_let as y; eauto.
            assert (HL: y \notin L) by auto.
            unfold open_trm. simpl. specialize (H1 y HL).
            apply_fresh ty_let as z; eauto.
            unfold open_trm.
            rewrite~ (proj41 (open_comm_trm_val_def_defs z y)).
            apply (proj41 (lc_opening_change_var_trm_val_def_defs x z)) with (n:=0) (t':=t0) in H6; auto.
            apply (lc_opening 1 y) in H6. unfold open_trm in H6. rewrite H6.
            assert (HL0: z \notin L0) by auto.
            specialize (H3 z HL0). eapply weaken_rules; eauto.
          }
          {
            eapply IHty_trm with (L:=L \u (dom G)); eauto. intros.
            assert (HL: x0 \notin L) by auto.
            specialize (H2 x0 HL). eapply narrow_typing; eauto.
            apply~ subenv_last.
          }
        * eapply ty_sub; eauto.
  }
Qed.
