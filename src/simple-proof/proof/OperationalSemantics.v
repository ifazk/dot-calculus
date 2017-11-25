Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions Binding.

(** * Stack-Based Operational Semantics *)

Reserved Notation "t1 '|->' t2" (at level 40, t2 at level 39).

Fixpoint defs_update (ds: defs) (a: trm_label) (t: trm) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons ds' (def_typ A T)  =>
    defs_cons (defs_update ds' a t) (def_typ A T)
  | defs_cons ds' (def_trm a' t')  =>
    If a = a' then defs_cons ds' (def_trm a t) else defs_cons (defs_update ds' a t) (def_trm a' t')
end.

Definition sto_update (x : var) (m : trm_label) (t : trm) (s1 : sta) (s2 : sta) : Prop :=
    ok s1 /\
    ok s2 /\
    dom s1 = dom s2 /\
    (forall y, (y <> x) ->
         (forall v, binds y v s1 -> binds y v s2) /\
         (forall v, binds y v s2 -> binds y v s1)) /\
    (exists T ds1 ds2, binds x (val_obj T ds1) s1 /\
                  binds x (val_obj T ds2) s2 /\
                  defs_update (open_defs x ds1) m t = open_defs x ds2).

Inductive red : sta * trm -> sta * trm -> Prop :=
(** [s(x) = nu(T)...{a = t}...]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(s, x.a) |-> (s, t)      ]  *)
| red_sel : forall x m s t T ds,
    binds x (val_obj T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    (s, trm_sel (avar_f x) m) |-> (s, trm_force (avar_f x) m)

| red_force_loc : forall x m s y T ds,
    binds x (val_obj T ds) s ->
    defs_has (open_defs x ds) (def_trm m (trm_var (avar_f y))) ->
    (s, trm_force (avar_f x) m) |-> (s, (trm_var (avar_f y)))

| red_force_term : forall x m s t T ds,
    binds x (val_obj T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    (forall y, (trm_var (avar_f y)) <> t) ->
    (s, trm_force (avar_f x) m) |-> (s, trm_force_assgn (avar_f x) m t)

(** [s(x) = lambda(T)t]      #<br>#
    [―――――――――――――――――――――]  #<br>#
    [(s, x y) |-> (s, t^y)]  *)
| red_app : forall f a s T t,
    binds f (val_fun T t) s ->
    (s, trm_app (avar_f f) (avar_f a)) |-> (s, open_trm a t)

(** [(s, let x = v in t) |-> ((s, x = v), t^x)] *)
| red_let_val : forall v s x,
    x # s ->
    (s, (trm_val v)) |-> (s & x ~ v, trm_var (avar_f x))

(** [(s, let y = x in t) |-> (s, t^x)] *)
| red_let_var : forall t s x,
    (s, trm_let (trm_var (avar_f x)) t) |-> (s, open_trm x t)

(** [(s, t0) |-> (s', t0')]                             #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――――]  #<br>#
    [(s, let x = t0 in t) |-> (s', let x = t0' in t)]  *)
| red_let_tgt : forall t0 t s t0' s',
    (s, t0) |-> (s', t0') ->
    (s, trm_let t0 t) |-> (s', trm_let t0' t)

| red_force_assgn_trm : forall t0 x m s t0' s',
    (s, t0) |-> (s', t0') ->
    (s, trm_force_assgn (avar_f x) m t0) |-> (s, trm_force_assgn (avar_f x) m t0')

| red_force_assgn_var : forall s x m y s',
    sto_update x m (trm_var (avar_f y)) s s' ->
    (s, trm_force_assgn (avar_f x) m (trm_var (avar_f y))) |->
    (s', (trm_var (avar_f y)))

where "t1 '|->' t2" := (red t1 t2).

(** ** Normal forms *)
(** Variables and values are considered to be in normal form. *)
Inductive norm_form: trm -> Prop :=
| nf_loc: forall x, norm_form (trm_var x).

Hint Constructors red norm_form.
