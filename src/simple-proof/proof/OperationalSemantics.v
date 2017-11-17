Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions Binding.

Fixpoint defs_update (ds: defs) (a: trm_label) (t: trm) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons ds' (def_typ A T)  =>
    defs_cons (defs_update ds' a t) (def_typ A T)
  | defs_cons ds' (def_trm a' t')  =>
    If a = a' then defs_cons ds' (def_trm a t') else defs_cons (defs_update ds' a t) (def_trm a' t')
end.

Reserved Notation "t1 '|->l' t2" (at level 40, t2 at level 39).

Definition call_stack := (list (var * trm_label)).

Inductive red_l : sta * trm * (list (var * trm_label)) -> sta * trm * (list (var * trm_label)) -> Prop :=
(** [s(x) = nu(T)...{a = t}...]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(s, x.a) |->l (s, t)      ]  *)
| red_sel1_l : forall x m s l y T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m (trm_var (avar_f y))) ->
    (s, trm_sel (avar_f x) m, l) |->l (s, (trm_var (avar_f y)), l)

| red_sel2_l : forall x m s t l T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    (forall x, t <> (trm_var (avar_f x))) ->
    (s, trm_sel (avar_f x) m, l) |->l (s, t, cons (x, m) l)

| red_sel3_l : forall x m s s' s1 s2 l y T ds ds',
    s = s1 & x ~ (val_new T ds) & s2 ->
    s' = s1 & x ~ (val_new T ds') & s2 ->
    (open_defs x ds') = (defs_update (open_defs x ds) m (trm_var (avar_f y))) ->
    (s, (trm_var (avar_f y)), cons (x, m) l) |->l (s', (trm_var (avar_f y)), l)

(** [s(x) = lambda(T)t]      #<br>#
    [―――――――――――――――――――――]  #<br>#
    [(s, x y) |->l (s, t^y)]  *)
| red_app_l : forall f a s T t l,
    binds f (val_lambda T t) s ->
    (s, trm_app (avar_f f) (avar_f a), l) |->l (s, open_trm a t, l)

(** [(s, let x = v in t) |->l ((s, x = v), t^x)] *)
| red_let_val_l : forall v t s x l,
    x # s ->
    (s, trm_let (trm_val v) t, l) |->l (s & x ~ v, open_trm x t, l)

(** [(s, let y = x in t) |->l (s, t^x)] *)
| red_let_var_l : forall t s x l,
    (s, trm_let (trm_var (avar_f x)) t, l) |->l (s, open_trm x t, l)

(** [(s, t0) |->l (s', t0')]                             #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――――]  #<br>#
    [(s, let x = t0 in t) |->l (s', let x = t0' in t)]  *)
| red_let_tgt_l : forall t0 t s t0' s' l,
    (s, t0, l) |->l (s', t0', l) ->
    (s, trm_let t0 t, l) |->l (s', trm_let t0' t, l)

where "t1 '|->l' t2" := (red_l t1 t2).

Inductive norm_form_l: trm -> Prop :=
| nf_var_l: forall x, norm_form_l (trm_var x).
