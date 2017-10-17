Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import Binding.

(** * Normal Forms
A normal form is defined in the WadlerFest DOT paper as:

[n ::= x | v | let x = v in n]

This corresponds to an evaluation context of the form
[(let x = v in)* [ ]] whose hole is filled by a variable [x]
or value [v]. *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v)
| nf_let: forall v t, normal_form t -> normal_form (trm_let (trm_val v) t).

(** * Operational Semantics

The first four reduction rules correspond directly to the rules in Figure 7 of the paper.

The last two rules are congruence rules that implement the meaning of evaluation contexts.
Specifically, if a term [u] decomposes into an evaluation context and subterm
as [u = e[t]] and [e[t]] reduces to [e[t']] according to the rules from Figure 7,
then the purpose of the two congruence rules is to ensure that [u] also reduces
to [u'], where [u'] is the term [u' = e[t']]. The grammar for evaluation contexts
in the paper is:

[e ::= [] | let x = [] in t | let x = v in e]

A sentential form [eta] in a derivation of an evaluation context [e] is a string
of terminals (the elements of DOT terms) and the non-terminal [e]. Define
[e(eta)] to be a string of terminals formed by replacing [e] with [[]] in [eta].
We argue that whenever [eta_1] directly derives [eta_2] ([eta_1 => eta_2]),
and the reduction rules infer that [e(eta_2)[t_2] |-> e(eta_2)[t_2']], then the
reduction rules also infer that [e(eta_1)[t_1] |-> e(eta_1)[t_1']], where
[e(eta_2)[t_2] = e(eta_1)[t_1]] and [e(eta_2)[t_2'] = e(eta_1)[t_1']].
The argument is by considering each of the three cases
in the evaluation context grammar that justify [eta_1 => eta_2].
The first case replaces [e] with [[]], so [e(eta_1) = e(eta_2)], so the conclusion
trivially holds. The second case replaces [e] with [let x = [] in t]. In this case,
the reduction congruence rule [red_let_trm] has [e(eta_2)[t_2] |-> e(eta_2)[t_2']]
as a premise and [e(eta_1)[t_1] |-> e(eta_1)[t_1']] as a conclusion. The third case
replaces [e] with [let x = v in e].  Similarly, the congruence rule [red_let_val]
has [e(eta_2)[t_2] |-> e(eta_2)[t_2']] as a premise and [e(eta_1)[t_1] |-> e(eta_1)[t_1']]
as a conclusion. Thus, whenever [eta_1 => eta_2] and [e(eta_2)[t_2] |-> e(eta_2)[t_2']],
we also have that [e(eta_1)[t_1] |-> e(eta_1)[t_1']].

Reasoning inductively about the steps in the context-free grammar derivation of [e],
for every sentential
form [eta] that occurs in that derivation, the congruence reduction rules infer that
[e(eta)[u] |-> e(eta)[u']], where
[e(eta)[u] = e[t]] and [e(eta)[u'] = e[t']]. In particular, this is true for the
sentential form [eta = e], the first sentential form of every derivation. Since
[e(eta) = e(e) = []], we have shown that the congruence reduction rules infer that [u |-> u'].

Starting with an evaluation context [e] in its conclusion, the [red_let_val] rule appends
[let x = v] to the context to yield a new context used in its premise.
(More precisely, the rule replaces the non-terminal [e] within the context in the conclusion by
[let x = v in e].) This is the only reduction rule that modifies an existing evaluation context. Therefore,
in a derivation of a reduction judgment [u |-> u'] in an empty evaluation context, every evaluation context
that appears in the derivation is of the form [let x_1 = v_1 in ... let x_n = v_n in []].
Therefore, in order to be able to represent every step of every such derivation of a reduction
judgement in the Coq proof, it is sufficient to represent evaluation contexts by a data structure
that can represent all evaluation contexts of this form. The proof represents these evaluation
contexts by a [sto], a list of pairs of variables and values.
*)


Reserved Notation "e '[' t1 '|->' t2 ']'" (at level 60, t1 at level 39).

Inductive red : sto -> trm -> trm -> Prop :=
(** [e(x) = lambda(T)t]    #<br>#
    [――――――――――――――――――――]  #<br>#
    [e [x y] |-> e [t^y] ]  *)
| red_apply : forall x y e T t,
    lc_trm (trm_app (avar_f x) (avar_f y)) ->
    binds x (val_lambda T t) e ->
    e [ trm_app (avar_f x) (avar_f y) |-> open_trm y t ]
(** [e(x) = nu(T)...{a = t}...]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [e[ x.a] |-> e[t]]  *)
| red_project : forall x a e T ds t,
    lc_trm (trm_sel (avar_f x) a) ->
    binds x (val_new T ds) e ->
    defs_has (open_defs x ds) (def_trm a t) ->
    e [ trm_sel (avar_f x) a |-> t ]
(** [e[let x = y in t] |-> e[t^y]] *)
| red_let_var : forall y t e,
    lc_trm (trm_let (trm_var (avar_f y)) t) ->
    e [ trm_let (trm_var (avar_f y)) t |-> open_trm y t ]
(** [e[let x = (let y = s in t) in u] |-> e[let y = s in let x = t in u]] *)
| red_let_let : forall s t u e,
    lc_trm (trm_let (trm_let s t) u) ->
    e [ trm_let (trm_let s t) u |-> trm_let s (trm_let t u) ]
(** [e[t] |-> e[t']]                            #<br>#
    [――――――――――――――――――――――――――――――――――――――――]  #<br>#
    [e[let x = t in u] |-> e[let x = t' in u]]     *)
| red_let_trm : forall e t t' u,
    lc_trm (trm_let t u) ->
    e [ t |-> t' ] ->
    e [ trm_let t u |-> trm_let t' u ]
(** [(e, x = v) [t] |-> (e, x = v) [t']]        #<br>#
    [――――――――――――――――――――――――――――――――――――――――]   #<br>#
    [e[let x = v in t] |-> e[let x = v in t']]   *)
| red_let_val: forall e t t' v L,
    lc_trm (trm_let (trm_val v) t) ->
    (forall x, x \notin L  ->
      (e & x ~ v) [ open_trm x t |-> open_trm x t' ]) ->
    e [ trm_let (trm_val v) t |-> trm_let (trm_val v) t' ]
where "e [ t |-> t' ]" := (red e t t').
Hint Constructors red normal_form.


Lemma lc_env_eval_to_lc_trm : forall e t t',
    lc_sto e ->
    e [t |-> t'] ->
    lc_trm t'.
Proof with auto.
  introv Hlce He.
  induction He;
    match goal with
    | [ H : lc_at_trm _ _ |- _ ] => inversions H
    end;
    repeat constructor;
    do 2 try
       match goal with
       | [ H : binds _ _ _ |- _ ] => apply lc_sto_binds_inv in H; eauto
       | [ H : lc_at_val _ _ |- _ ] => inversions H
       | [ H : lc_at_trm _ _ |- _ ] => solve [inversions H; auto]
       end;
    try applys lc_at_to_open_trm_val_def_defs;
    eauto.
  - apply lc_defs_has in H1... inversion H1...
    applys lc_at_to_open_trm_val_def_defs...
  - eapply lc_at_relaxing_trm_val_def_defs; try eassumption.
    omega.
  - inversion H4. pick_fresh x.
    assert (x \notin L); auto.
    assert (lc_sto (e & x ~ v)); auto.
    specialize (H1 x H3 H6).
    applys open_to_lc_at_trm_val_def_defs. eassumption.
Qed.
