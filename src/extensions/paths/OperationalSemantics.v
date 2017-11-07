Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions Binding.

(** * Stack-Based Operational Semantics *)

(** * Path Lookup *)

Reserved Notation "s '∋' t" (at level 60).
Reserved Notation "s '↓' p '==' ds" (at level 60).


(** Looking up a path in a stack. *)

Inductive lookup : sta -> path * val -> Prop :=

(** [s(x) = v  ]    #<br>#
    [――――――――――]    #<br>#
    [s ∋ (x, v)]    *)
| lookup_var : forall s x v,
    binds x v s ->
    s ∋ (pvar x, v)

(** [s ↓ p = ...{a = v}...  ]    #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [s ∋ (p.a, v)]               *)
| lookup_val : forall s p ds a v,
    s ↓ p == ds ->
    defs_has ds (def_trm a (trm_val v)) ->
    s ∋ (p•a, v)

| lookup_path : forall s ds a p v,
    s ↓ p == ds ->
    defs_has ds (def_trm a (trm_path p)) ->
    s ∋ (p, v) ->
    s ∋ (p•a, v)

where "s '∋' t" := (lookup s t)

(** Opening of definitions:
    If [s ∋ (p, ν(x: T)ds)], then [lookup_open] gives us [ds] opened with [p]. *)

with lookup_open : sta -> path -> defs -> Prop :=

(** [s ∋ (p, ν(T)ds         ]    #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [s ↓ p = ds^p           ]    *)
     | lo_ds : forall s p T ds,
         s ∋ (p, val_new T ds) ->
         s ↓ p == open_defs_p p ds

where "s '↓' p '==' ds" := (lookup_open s p ds).

Reserved Notation "t1 '|->' t2" (at level 40, t2 at level 39).

Inductive red : sta * trm -> sta * trm -> Prop :=

(** [s ∋ (p, lambda(T)t)  ]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [(s, p q) |-> (s, t^q)]      *)
| red_app: forall s p q T t,
    s ∋ (p, val_lambda T t) ->
    (s, trm_app p q) |-> (s, open_trm_p p t)

(** [(s, let x = v in t) |-> ((s, x = v), t^x)] *)
| red_let : forall v t s x,
    x # s ->
    (s, trm_let (trm_val v) t) |-> (s & x ~ v, open_trm x t)

(** [(s, let y = p in t) |-> (s, t^p)] *)
| red_let_var : forall t s p,
    (s, trm_let (trm_path p) t) |-> (s, open_trm_p p t)

(** [(s, t0) |-> (s', t0')]                            #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――――]  #<br>#
    [(s, let x = t0 in t) |-> (s', let x = t0' in t)]  *)
| red_let_tgt : forall t0 t s t0' s',
    (s, t0) |-> (s', t0') ->
    (s, trm_let t0 t) |-> (s', trm_let t0' t)

where "t1 '|->' t2" := (red t1 t2).

(** ** Normal forms *)

(** Paths and values are considered to be in normal form. *)
Inductive norm_form: trm -> Prop :=
| nf_path: forall p, norm_form (trm_path p)
| nf_val: forall v, norm_form (trm_val v).

Hint Constructors red norm_form.
