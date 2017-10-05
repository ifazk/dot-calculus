Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions Helper_lemmas.

(** * Normal Forms
A normal form is defined in the WadlerFest DOT paper as:

[n ::= x | v | let x = v in n]

This corresponds to an evaluation context of the form
[(let x = v in)* [ ]] whose hole is filled by a variable [x]
or value [v]. *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v).

(** ** Evaluation Contexts

The paper defines an evaluation context with the following context-free grammar:

[e ::= [] | let x = [] in t | let x = v in e]

This grammar generates the language characterized by the regular expression:

[ (let x = v in)* []  ]               #<br>#
[| (let x = v in)* let x = [] in t]

It is more convenient in Coq to represent evaluation contexts following the above
regular expression. *)

(** Now, an evaluation context is either
    - [e_hole s], where [s] is a (possibly empty) store, which
      represents [(let x = v in)* []], or
    - [e_term s t], where [s] is the store and [t] the term to
      be evaluated next, which represents [(let x = v in)* let x = [] in t]. *)
Inductive ec : Type :=
| e_hole : sto -> ec
| e_term : sto -> trm -> ec.

(** A function that retrieves the store from an evaluation context. *)
Definition ec_sto (e : ec) :=
  match e with
  | e_hole s   => s
  | e_term s t => s
  end.

(** Locally closed evaluation contexts *)
Inductive lc_ec : ec -> Prop :=
| lc_ec_hole : forall s,
    lc_sto s ->
    lc_ec (e_hole s)
| lc_ec_term : forall s t,
    lc_sto s ->
    (forall x, lc_trm (open_trm x t)) ->
    lc_ec (e_term s t).

(** Locally closed terms that are decomposed using evaluation contexts *)
Definition lc_term (e : ec) (t : trm) : Prop :=
  lc_ec e /\ lc_trm t.

(** Free variables in an evaluation context *)
Fixpoint fv_ec (e: ec) : vars :=
  match e with
  | e_hole s => dom s
  | e_term s t => dom s \u (fv_trm t)
  end.

(** * Operational Semantics

The reduction rules in the paper are:

[t |-> t']                 #<br>#
[――――――――――――――] (Term)  #<br>#
[e[t] |-> e[t']] #<br># #<br>#

[v = lambda(z: T).t]                                      #<br>#
[―――――――――――――――――――――――――――――――――――――――――――――――] (Apply) #<br>#
[let x = v in e[x y] |-> let x = v in e[[y/z] t]] #<br># #<br>#

[v = nu(x: T)...{a = t}...]                             #<br>#
[―――――――――――――――――――――――――――――――――――――――――] (Project)   #<br>#
[let x = v in e[x.a] |-> let x = v in e[t]] #<br># #<br>#

[let x = y in t |-> [y/x] t] (Let-Var) #<br># #<br>#

[let x = let y = s in t in y |-> let y = s in let x = t in u] (Let-Let) #<br># #<br>#

We transform the rules by inlining the (Term) rule into all of the other rules:

[v = lambda(z: T).t]                                                #<br>#
[―――――――――――――――――――――――――――――――――――――――――――――――――――――――――] (Apply) #<br>#
[e1[let x = v in e2[x y]] |-> e1[let x = v in e2[[y/z] t]]] #<br># #<br>#

[v = nu(x: T)...{a = t}...]                                           #<br>#
[―――――――――――――――――――――――――――――――――――――――――――――――――――――――――] (Project) #<br>#
[e1[let x = v in e2[x.a]] |-> e1[let x = v in e2[t]]] #<br># #<br>#

[e[let x = y in t] |-> e[[y/x] t]] (Let-Var) #<br># #<br>#

[e[let x = let y = s in t in u] |-> e[let y = s in let x = t in u]] (Let-Let) #<br># #<br>#

We then note that in the Apply and Project rules,
[e1[let x = v in e2[ ]]]
is itself a larger evaluation context. We simplify this evaluation context
into just [e[ ]].

Additionally, we define a binds relation [e(x) = v] which determines
whether the evaluation context [e] contains the subterm [let x = v in e2]:

[e = e1[let x = v in e2[ ]]] #<br>#
[――――――――――――――――――――――――――] #<br>#
[e(x) = v] #<br># #<br>#

The (Apply) and (Project) reduction rules become:

[e(x) = lambda(z: T).t]         #<br>#
[―――――――――――――――――――――] (Apply) #<br>#
[e[x y] |-> e[[y/z] t]] #<br># #<br>#

[e(x) = nu(x: T)...{a = t}...]           #<br>#
[――――――――――――――――――――――――――――] (Project) #<br>#
[e[x.a] |-> e[t]] #<br># #<br>#

In general, there may be multiple decompositions of a term into an evaluation context
and a subterm. For example, the term

[let x = v1 in let y = v2 in x y]

decomposes in three ways:

[[let x = v1 in let y = v2 in x y]]

[let x = v1 in [let y = v2 in x y]]

[let x = v1 in let y = v2 in [x y]]

However, the reduction rules cannot apply to any of the decompositions except the
last one, because none of the reduction rules match the syntactic pattern

[e[let x = v in t]]

Therefore, the only decomposition to which a reduction rule can possibly apply
is the maximal one, where all prefixes of the form

[let x = v in]

have been shifted into the evaluation context.

In the proof, we represent terms in this maximally decomposed way, in the form
of a pair [(e, t)] of an evaluation context and a term.

A term of the form

[let x = t in u]

can be decomposed into evaluation contexts in two ways:

[[let x = t in u]]  (1)

[let x = [t] in u]  (2)

Similarly, a term of the form

[let x = v in u]

can be decomposed into evaluation contexts in three ways:

[[let x = v in u]]  (3)

[let x = [v] in u]  (4)

[let x = v in [u]]  (5)

Of these different decompositions of the same two terms, the reduction
rules can apply only to decompositions (2) and (5).

We add congruence reduction rules to reduce the decomposition (1) to
decomposition (2) and decompositions (3) and (4) to decomposition (5).

[e[let x = t in u] |-> e[let x = [t] in u]]
(Congruence-Let) #<br># #<br>#

[e[let x = [v] in u] |-> e[let x = v in [u]]]
(Congruence-Val) #<br># #<br>#

Rule (Congruence-Let) reduces (1) to (2). It also reduces (3) to (4).
Rule (Congruence-Val) then further reduces (4) to (5). *)

Reserved Notation "e1 '/' t1 '|->' e2 '/' t2" (at level 40, e2 at level 39).

Inductive red : ec -> trm -> ec -> trm -> Prop :=
(** [e(x) = lambda(T)t]    #<br>#
    [―――――――――――――――――――]  #<br>#
    [e | x y |-> e | t^y]  *)
| red_apply : forall x y e T t,
    binds x (val_lambda T t) (ec_sto e) ->
    e / trm_app (avar_f x) (avar_f y) |-> e / open_trm y t
(** [e(x) = nu(T)...{a = t}...]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [e | x.a |-> e | t]  *)
| red_project : forall x a e T ds t,
    binds x (val_new T ds) (ec_sto e) ->
    defs_has (open_defs x ds) (def_trm a t) ->
    e / trm_sel (avar_f x) a |-> e / t
(** [e[let x = [ ] in t] | y |-> e[ ] | t^y] *)
| red_let_var : forall x t s,
    e_term s t / trm_var (avar_f x) |-> e_hole s / open_trm x t
(** [e[let x = [ ] in t1] | let t2 in t3 |-> e[let x = [ ] in let t3 in t1] | t2] *)
| red_let_let : forall s t1 t2 t3,
    e_term s t1 / trm_let t2 t3 |-> e_term s (trm_let t3 t1) / t2
(** [e[ ] | let x = t in u |-> e[let x = [ ] in u] | t] *)
| red_congruence_let : forall s t u,
    e_hole s / trm_let t u |-> e_term s u / t
(** [e[let x = [ ] in t] | v |-> e[let x = v in [ ]] | t^x] *)
| red_congruence_val: forall s x v t,
    x # s ->
    e_term s t / trm_val v |-> e_hole (s & (x ~ v)) / open_trm x t
where "t1 '/' st1 '|->' t2 '/' st2" := (red t1 st1 t2 st2).

(** ** Typing of Evaluation Contexts *)

(** We define a typing relation for pairs [e] and [t] of an evaluation context and a term
    in an empty context.

    The term [e[t]] has type T in an empty context if and only if [G] is inert,
    [G] corresponds to the store of [e], and the term [e[t]] has type [T] in typing context
    [G] according to the general typing relation for terms . *)
Inductive ty_ec_trm: ctx -> ec -> trm -> typ -> Prop :=
| ty_e_hole : forall G s t T,
    inert G ->
    G ~~ s ->
    G ⊢ t : T ->
    ty_ec_trm G (e_hole s) t T
| ty_e_term : forall L G s u t T U,
    inert G ->
    G ~~ s ->
    G ⊢ t : T ->
    (forall x, x \notin L -> G & x ~ T ⊢ (open_trm x u) : U) ->
    ty_ec_trm G (e_term s u) t U.

Hint Constructors
     red wf_sto lc_ec.

(** The store of a locally closed evaluation context is also
    locally closed. *)
Lemma lc_ec_sto_inv : forall e,
    lc_ec e ->
    lc_sto (ec_sto e).
Proof.
  intros e H.
  induction H; auto.
Qed.

(** If the term [(let x = v in)* let x = [t] in u] represented by an
    evaluation context is locally closed, so is the term
    [(let x = v in)* [t]]. *)
Lemma lc_term_to_hole: forall s u t,
    lc_term (e_term s u) t ->
    lc_term (e_hole s) t.
Proof.
  intros. inversions H. inversions H0. repeat constructor~.
Qed.

(** * Lemmas About Local Closure *)

(** A value that is part of a binding in a locally closed evaluation
    context is also locally closed. *)
Lemma lc_ec_sto_binds_inv : forall e x v,
    lc_ec e ->
    binds x v (ec_sto e) ->
    lc_val v.
Proof.
  intros.
  inversions H; eauto using lc_sto_binds_inv.
Qed.

Inductive closed_ec_typing : ec -> trm -> typ -> Prop :=
| cet: forall G e t T, ty_ec_trm G e t T ->
  closed_ec_typing e t T.

Notation "'⊢' e '[' t ']:' T" := (closed_ec_typing e t T) (at level 40, t at level 59).
