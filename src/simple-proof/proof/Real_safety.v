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


Fixpoint ec_trm_helper(e: ec)(s: sto)(t: trm): trm :=
  match s with
  | nil => match e with
          | e_hole _ => t
          | e_term _ u => trm_let t u
          end
  | cons (x,v) s => trm_let (trm_val v) (open_trm x (ec_trm_helper e s t))
  end.

Fixpoint ec_trm(e: ec)(t: trm): trm := ec_trm_helper e (ec_sto e) t.

Fixpoint ec_vars(e: ec) := from_list (keys (ec_sto e)).

Fixpoint prepend(s: sto)(e: ec) :=
  match e with
  | e_hole s' => e_hole (s & s')
  | e_term s' t => e_term (s & s') t
  end.

Fixpoint max_ec(t': trm): ec * trm := match t' with
  | trm_let (trm_val v) u =>
    match max_ec(u) with
    | (e,t) =>
      let x := (var_gen (ec_vars e)) in
      ((prepend (x~v) e),(open_trm x t))
    end
  | trm_let t u => ((e_term nil u), t)
  | t => ((e_hole nil),t)
  end.

Lemma ec_inverse: forall e t u,
    (e,t) = max_ec(u) ->
    ec_trm e t = u
.
Admitted.

Lemma ec_preserves_lc: forall e t u,
    ec_trm e t = u ->
    lc_trm u ->
    lc_term e t
.
Admitted.

(*
Definition ctx_sto(s: sto)(G: ctx): Prop :=
    forall x v, binds x v s -> exists T, binds x T G /\ G |- (trm_val v) : T
.

I would prefer to use the above definition, but the definition below is
closer to what we already have, so it will be less work.
*)

Definition ctx_sto(s: sto)(G: ctx): Prop := G ~~ s.

Lemma ctx_sto_exists: forall e t u U,
    ec_trm e t = u ->
    empty |- u : U ->
    exists G, inert G /\ ctx_sto (ec_sto e) G
.
(* Use the fact that all the (let x=v in) in u have to type. Use
val_typing lemma from the existing proof to show that they have a precise
type. This type is inert.
*)
Admitted.

Lemma hole_type : forall s t u U G,
    ec_trm (e_hole s) t = u ->
    empty |- u : U ->
    ctx_sto s G ->
    G |- t : U
.
Admitted.

Lemma term_type : forall s t u U G,
    ec_trm (e_term s t') t = u ->
    empty |- u : U ->
    ctx_sto s G ->
    exists U', G |- t : U'
.
Admitted.

Lemma hole_term: forall s t u,
    ec_trm (e_hole s) (trm_let t u) = ec_trm (e_term s u) t
.
Admitted.


Reserved Notation "e1 '/' t1 '||->' e2 '/' t2" (at level 40, e2 at level 39).

Inductive red' : ec -> trm -> ec -> trm -> Prop :=
(** [e(x) = lambda(T)t]  #<br>#
    [――――――――――――]  #<br>#
    [e | x y |-> e | t^y]  *)
| red_apply : forall x y e T t,
    binds x (val_lambda T t) (ec_sto e) ->
    e / trm_app (avar_f x) (avar_f y) ||-> e / open_trm y t
(** [e(x) = nu(T)...{a = t}...]  #<br>#
    [――――――――――――――――――――――――]  #<br>#
    [e | x.a |-> e | t]  *)
| red_project : forall x a e T ds t,
    binds x (val_new T ds) (ec_sto e) ->
    defs_has (open_defs x ds) (def_trm a t) ->
    e / trm_sel (avar_f x) a ||-> e / t
(** [e[let x = [ ] in t] | y |-> e[ ] | t^y] *)
| red_let_var : forall x t s,
    e_term s t / trm_var (avar_f x) ||-> e_hole s / open_trm x t
(** [e[let x = [ ] in t1] | let t2 in t3 |-> e[let x = [ ] in let t3 in t1] | t2] *)
| red_let_let : forall s t1 t2 t3,
    e_term s t1 / trm_let t2 t3 ||-> e_term s (trm_let t3 t1) / t2
where "t1 '/' st1 '||->' t2 '/' st2" := (red' t1 st1 t2 st2).

Lemma progress : forall u T e t,
  empty |- u : T ->
  (e,t) = max_ec u ->
  normal_form e t \/ exists e' t', e / t ||-> e' / t'
.
(* Proof sketch:

Use ctx_sto_exists on (ec_sto e) to get G.
Then do the same things as in old progress theorem.
We no longer have congruence reduction rules.
In their place, use the fact that max_ec never returns a let term that would need them.
*)
Admitted.



Lemma hole_preserves_type : forall s t u t' u' U G,
    ec_trm (e_hole s) t = u ->
    ec_trm (e_hole s) t' = u' ->
    empty |- u : U ->
    ctx_sto s G ->
    G |- t' : U ->
    empty |- u' : U
.
Admitted.

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
    empty |- u' : U
.
Admitted.
*)

Lemma red_preserves_sto : forall e t e' t',
    e / t ||-> e' / t' ->
    ec_sto e = ec_sto e'
.
Admitted.

Lemma preservation : forall u T e t e' t' u',
    lc_trm u ->
    empty |- u : T ->
    ec_trm e t = u ->
    e / t ||-> e' / t' ->
    ec_trm e' t' = u' ->
    empty |- u' : T /\ lc_trm u'
.
(*
1) apply ctx_sto_exists
2) case-split on e (e_hole vs e_term)
3) for e_hole case, apply hole_type to get typing for t
4) induct on typing for t, inverting the ||-> in each case, like in the old proof
5) apply hole_preserves_type to go from type of t' to type of u'
6) for e_term case, apply term_type and/or hole_term and ???
*)
Admitted.
