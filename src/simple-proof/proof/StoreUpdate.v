Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions.

Inductive defs_update : defs -> trm_label -> var -> defs -> Prop :=
| defs_update_var : forall ds a t x,
    defs_update (defs_cons ds (def_trm a t)) a x (defs_cons ds (def_trm a (trm_var (avar_f x))))
| defs_update_push : forall ds d a x ds',
    defs_update ds a x ds' ->
    defs_update (defs_cons ds d) a x (defs_cons ds' d).

Definition sto_update (s : sto) (x : var) (a : trm_label) (y : var) (s' : sto) :=
  ok s /\
  ok s' /\
  (dom s) = (dom s') /\
  (forall z v, z <> x ->
          binds z v s ->
          binds z v s') /\
  exists T ds ds', binds x (val_obj T ds) s /\
              defs_update ds a y ds' /\
              binds x (val_obj T ds') s'.

Lemma defs_update_open : forall x ds a y ds',
    defs_update ds a y ds' ->
    forall ds1, ds = (open_defs x ds1) ->
           exists ds1', ds' = (open_defs x ds1').
Proof.
  introv H. induction H; intros.
  - destruct ds1; inversions H.
    exists (defs_cons ds1 (def_trm a (trm_var (avar_f x0)))).
    reflexivity.
  - destruct ds1; inversion H0.
    pose proof (IHdefs_update _ H2) as [?ds ?].
    subst ds'. exists (defs_cons ds0 d0).
    reflexivity.
Qed.
