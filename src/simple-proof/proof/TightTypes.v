(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [⊢##] and [ty_val_inv], [⊢##v]). *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import PreciseTypes.

(** * Tight typing [G |-# t: T] *)

Reserved Notation "G '@@' S '⊢#' t ':' T" (at level 40, t at level 59).
Reserved Notation "G '@@' S '⊢#' T '<:' U" (at level 40, T at level 59).

(** *** Tight term typing [G @@ S ⊢# t: T] *)
(** Tight typing is very similar to general typing, and could be obtained by replacing
    all occurrences of [⊢] with [⊢#], except for the following:
    - in the type selection subtyping rules Sel-<: and <:-Sel ([subtyp_sel1] and [subtyp_sel2]),
      the premise is precise typing of a type declaration with equal bounds;
    - whenever a typing judgement in a premise extends the environment (for example, [ty_all_intro_t]),
      it is typed under general typing [⊢] and not tight typing [⊢#]. *)

Inductive ty_trm_t : ctx -> sigma -> trm -> typ -> Prop :=

(** [G(x) = T]   #<br>#
    [――――――――――] #<br>#
    [G @@ S ⊢# x: T]  *)
| ty_var_t : forall G S x T,
    binds x T G ->
    G @@ S ⊢# trm_var (avar_f x) : T

| ty_loc : forall G S l T,
    binds l T S ->
    G @@ S ⊢# trm_val (val_loc l) : (typ_ref T)

(** [G, x: T @@ S ⊢ t^x: U^x]       #<br>#
    [x fresh]                  #<br>#
    [――――――――――――――――――――――――] #<br>#
    [G @@ S ⊢# lambda(T)t: forall(T)U]     *)
| ty_all_intro_t : forall L G S T t U,
    (forall x, x \notin L ->
      G & x ~ T @@ S ⊢ open_trm x t : open_typ x U) ->
    G @@ S ⊢# trm_val (val_lambda T t) : typ_all T U

(** [G @@ S ⊢# x: forall(S)T] #<br>#
    [G @@ S ⊢# z: S]     #<br>#
    [――――――――――――――] #<br>#
    [G @@ S ⊢# x z: T^z]     *)
| ty_all_elim_t : forall G S x z T U,
    G @@ S ⊢# trm_var (avar_f x) : typ_all T U ->
    G @@ S ⊢# trm_var (avar_f z) : T ->
    G @@ S ⊢# trm_app (avar_f x) (avar_f z) : open_typ z U

(** [G, x: T^x @@ S ⊢ ds^x :: T^x]    #<br>#
    [x fresh]                    #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [G @@ S ⊢# nu(T)ds :: mu(T)]         *)
| ty_new_intro_t : forall L G S T ds,
    (forall x, x \notin L ->
      G & (x ~ open_typ x T) @@ S /- open_defs x ds :: open_typ x T) ->
    G @@ S ⊢# trm_val (val_new T ds) : typ_bnd T

(** [G @@ S ⊢# x: {a: T}] #<br>#
    [―――――――――――――――] #<br>#
    [G @@ S ⊢# x.a: T]        *)
| ty_new_elim_t : forall G S x a T,
    G @@ S ⊢# trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    G @@ S ⊢# trm_sel (avar_f x) a : T

(** [G @@ S ⊢# t: T]             #<br>#
    [G, x: T @@ S ⊢ u^x: U]       #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――]       #<br>#
    [G @@ S ⊢# let t in u: U]        *)
| ty_let_t : forall L G S t u T U,
    G @@ S ⊢# t : T ->
    (forall x, x \notin L ->
      G & x ~ T @@ S ⊢ open_trm x u : U) ->
    G @@ S ⊢# trm_let t u : U

(** [G @@ S ⊢# x: T^x]   #<br>#
    [――――――――――――――] #<br>#
    [G @@ S ⊢# x: mu(T)] *)
| ty_rec_intro_t : forall G S x T,
    G @@ S ⊢# trm_var (avar_f x) : open_typ x T ->
    G @@ S ⊢# trm_var (avar_f x) : typ_bnd T

(** [G @@ S ⊢# x: mu(T)] #<br>#
    [――――――――――――――] #<br>#
    [G @@ S ⊢# x: T^x]       *)
| ty_rec_elim_t : forall G S x T,
    G @@ S ⊢# trm_var (avar_f x) : typ_bnd T ->
    G @@ S ⊢# trm_var (avar_f x) : open_typ x T

(** [G @@ S ⊢# x: T]      #<br>#
    [G @@ S ⊢# x: U]      #<br>#
    [―――――――――――――]   #<br>#
    [G @@ S ⊢# x: T /\ U]      *)
| ty_and_intro_t : forall G S x T U,
    G @@ S ⊢# trm_var (avar_f x) : T ->
    G @@ S ⊢# trm_var (avar_f x) : U ->
    G @@ S ⊢# trm_var (avar_f x) : typ_and T U

(** [G @@ S ⊢# t: T]    #<br>#
    [G @@ S ⊢# T <: U]  #<br>#
    [―――――――――――――] #<br>#
    [G @@ S ⊢# t: U]        *)
| ty_sub_t : forall G S t T U,
    G @@ S ⊢# t : T ->
    G @@ S ⊢# T <: U ->
    G @@ S ⊢# t : U

| ty_ref_intro : forall G S x T,
    G @@ S ⊢# trm_var (avar_f x) : T ->
    G @@ S ⊢# (trm_ref (avar_f x) T) : typ_ref T

| ty_ref_elim : forall G S x T,
    G @@ S ⊢# trm_var (avar_f x) : typ_ref T ->
    G @@ S ⊢# trm_deref (avar_f x) : T

| ty_asgn : forall G S x y T,
    G @@ S ⊢# trm_var (avar_f x) : typ_ref T ->
    G @@ S ⊢# trm_var (avar_f y) : T ->
    G @@ S ⊢# trm_asg (avar_f x) (avar_f y) : T
where "G '@@' S '⊢#' t ':' T" := (ty_trm_t G S t T)

(** *** Tight subtyping [G @@ S ⊢# T <: U] *)
with subtyp_t : ctx -> sigma -> typ -> typ -> Prop :=

(** [G @@ S ⊢# T <: top] *)
| subtyp_top_t: forall G S T,
    G @@ S ⊢# T <: typ_top

(** [G @@ S ⊢# bot <: T] *)
| subtyp_bot_t: forall G S T,
    G @@ S ⊢# typ_bot <: T

(** [G @@ S ⊢# T <: T] *)
| subtyp_refl_t: forall G S T,
    G @@ S ⊢# T <: T

(** [G @@ S ⊢# S <: T]     #<br>#
    [G @@ S ⊢# T <: U]     #<br>#
    [―――――――――――――]    #<br>#
    [G @@ S ⊢# S <: U]         *)
| subtyp_trans_t: forall G S T U V,
    G @@ S ⊢# T <: U ->
    G @@ S ⊢# U <: V ->
    G @@ S ⊢# T <: V

(** [G @@ S ⊢# T /\ U <: T] *)
| subtyp_and11_t: forall G S T U,
    G @@ S ⊢# typ_and T U <: T

(** [G @@ S ⊢# T /\ U <: U] *)
| subtyp_and12_t: forall G S T U,
    G @@ S ⊢# typ_and T U <: U

(** [G @@ S ⊢# S <: T]       #<br>#
    [G @@ S ⊢# S <: U]       #<br>#
    [――――――――――――――――]   #<br>#
    [G @@ S ⊢# S <: T /\ U]       *)
| subtyp_and2_t: forall G S T U V,
    G @@ S ⊢# T <: U ->
    G @@ S ⊢# T <: V ->
    G @@ S ⊢# T <: typ_and U V

(** [G @@ S ⊢# T <: U]           #<br>#
    [――――――――――――――――――――――] #<br>#
    [G @@ S ⊢# {a: T} <: {a: U}]     *)
| subtyp_fld_t: forall G S a T U,
    G @@ S ⊢# T <: U ->
    G @@ S ⊢# typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)

(** [G @@ S ⊢# S2 <: S1]                   #<br>#
    [G @@ S ⊢# T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G @@ S ⊢# {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ_t: forall G S A S1 T1 S2 T2,
    G @@ S ⊢# S2 <: S1 ->
    G @@ S ⊢# T1 <: T2 ->
    G @@ S ⊢# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

(** [G @@ S ⊢! x: {A: T..T}] #<br>#
    [――――――――――――――――――] #<br>#
    [G @@ S ⊢# T <: x.A]         *)
| subtyp_sel2_t: forall G S x A T,
    G @@ S ⊢! trm_var (avar_f x) : typ_rcd (dec_typ A T T) ->
    G @@ S ⊢# T <: typ_sel (avar_f x) A

(** [G @@ S ⊢! x: {A: T..T}] #<br>#
    [――――――――――――――――――] #<br>#
    [G @@ S ⊢# x.A <: T]         *)
| subtyp_sel1_t: forall G S x A T,
    G @@ S ⊢! trm_var (avar_f x) : typ_rcd (dec_typ A T T) ->
    G @@ S ⊢# typ_sel (avar_f x) A <: T

(** [G @@ S ⊢# S2 <: S1]                #<br>#
    [G, x: S2 @@ S ⊢ T1^x <: T2^x]       #<br>#
    [x fresh]                       #<br>#
    [――――――――――――――――――――――――]      #<br>#
    [G @@ S ⊢# forall(S1)T1 <: forall(S2)T2]          *)
| subtyp_all_t: forall L G S S1 T1 S2 T2,
    G @@ S ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 @@ S ⊢ open_typ x T1 <: open_typ x T2) ->
    G @@ S ⊢# typ_all S1 T1 <: typ_all S2 T2
where "G '@@' S '⊢#' T '<:' U" := (subtyp_t G S T U).

Hint Constructors ty_trm_t subtyp_t.

Scheme ts_ty_trm_t_mut := Induction for ty_trm_t Sort Prop
with   ts_subtyp_t     := Induction for subtyp_t Sort Prop.
Combined Scheme ts_t_mutind from ts_ty_trm_t_mut, ts_subtyp_t.

(** Tight typing implies general typing. *)
Lemma tight_to_general:
  (forall G S t T,
     G @@ S ⊢# t : T ->
     G @@ S ⊢ t : T) /\
  (forall G S T U,
     G @@ S ⊢# T <: U ->
     G @@ S ⊢ T <: U).
Proof.
  apply ts_t_mutind; intros; subst; eauto using precise_to_general.
Qed.
