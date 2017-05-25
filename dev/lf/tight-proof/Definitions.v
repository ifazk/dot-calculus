Set Implicit Arguments.

Require Import LibMap LibLN.
Require Import Coq.Program.Equality.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

Parameter typ_label: Set.
Parameter trm_label: Set.

Definition addr := var.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

Inductive avar : Set :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to store or ctx *)

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_ref  : typ -> typ (* Ref T *)
  | typ_rcd  : dec -> typ (* { D } *)
  | typ_and  : typ -> typ -> typ
  | typ_sel  : avar -> typ_label -> typ (* x.L *)
  | typ_bnd  : typ -> typ (* rec(x: T) *)
  | typ_all  : typ -> typ -> typ (* all(x: S)T *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec (* A: S..U *)
  | dec_trm  : trm_label -> typ -> dec (* a: T *).

Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_val  : val -> trm
  | trm_sel  : avar -> trm_label -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm (* let x = t in u *)
  | trm_ref  : avar -> typ -> trm (* ref x T *)
  | trm_deref  : avar -> trm (* !x *)
  | trm_asg  : avar -> avar -> trm (* x := y *)
with val : Set :=
  | val_new  : typ -> defs -> val
  | val_lambda : typ -> trm -> val
  | val_loc : addr -> val
with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> trm -> def
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.

(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Store typing ("Sigma") *)
Definition sigma := env typ.

(** *** Value environment ("sta") *)
Definition stack := env val.

(** *** Store ("sto") *)
Definition store := LibMap.map addr var.

Definition bindsM l x sto := LibBag.binds (A:=addr) (B:=var) sto l x.

Definition emptyM : store := (@empty_impl addr var).

(* ###################################################################### *)
(** ** Definition list membership *)

Definition label_of_def(d: def): label := match d with
| def_typ L _ => label_typ L
| def_trm m _ => label_trm m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ L _ _ => label_typ L
| dec_trm m _ => label_trm m
end.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of_def d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of_def d) ds = Some d.
Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

(* ###################################################################### *)
(** ** Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k)
   by a free variable x. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_ref T      => typ_ref (open_rec_typ k u T)
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_sel x L    => typ_sel (open_rec_avar k u x) L
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1) (open_rec_typ (S k) u T2)
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_trm m T => dec_trm m (open_rec_typ k u T)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_sel v m    => trm_sel (open_rec_avar k u v) m
  | trm_app f a    => trm_app (open_rec_avar k u f) (open_rec_avar k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  | trm_ref a t    => trm_ref (open_rec_avar k u a) (open_rec_typ k u t)
  | trm_deref a    => trm_deref (open_rec_avar k u a)
  | trm_asg l r    => trm_asg (open_rec_avar k u l) (open_rec_avar k u r)
  end
with open_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds   => val_new (open_rec_typ (S k) u T) (open_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (open_rec_typ k u T) (open_rec_trm (S k) u e)
  | val_loc n      => val_loc n
  end
with open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec_typ k u T)
  | def_trm m e => def_trm m (open_rec_trm k u e)
  end
with open_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_typ  u t := open_rec_typ   0 u t.
Definition open_dec  u D := open_rec_dec   0 u D.
Definition open_trm  u e := open_rec_trm   0 u e.
Definition open_val  u v := open_rec_val   0 u v.
Definition open_def  u d := open_rec_def   0 u d.
Definition open_defs u l := open_rec_defs  0 u l.

(* ###################################################################### *)
(** ** Record types *)

Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a T, record_dec (dec_trm a T).

Inductive record_typ : typ -> fset label -> Prop :=
| rt_one : forall D l,
  record_dec D ->
  l = label_of_dec D ->
  record_typ (typ_rcd D) \{l}
| rt_cons: forall T ls D l,
  record_typ T ls ->
  record_dec D ->
  l = label_of_dec D ->
  l \notin ls ->
  record_typ (typ_and T (typ_rcd D)) (union ls \{l}).

Definition record_type T := exists ls, record_typ T ls.

Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
    record_has (typ_rcd D) D
| rh_andl : forall T U D,
    record_has T D ->
    record_has (typ_and T U) D
| rh_andr : forall T U D,
    record_has U D ->
    record_has (typ_and T U) D.

(* ###################################################################### *)
(** ** Free variables *)

Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_ref T      => (fv_typ T)
  | typ_rcd D      => (fv_dec D)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_sel x L    => (fv_avar x)
  | typ_bnd T      => (fv_typ T)
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  end
with fv_dec (D: dec) : vars :=
  match D with
  | dec_typ L T U => (fv_typ T) \u (fv_typ U)
  | dec_trm m T   => (fv_typ T)
  end.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var a       => (fv_avar a)
  | trm_val v        => (fv_val v)
  | trm_sel x m      => (fv_avar x)
  | trm_app f a      => (fv_avar f) \u (fv_avar a)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  | trm_ref a t      => (fv_avar a) \u (fv_typ t)
  | trm_deref a      => (fv_avar a)
  | trm_asg l r      => (fv_avar l) \u (fv_avar r)
  end
with fv_val (v: val) : vars :=
  match v with
  | val_new T ds    => (fv_typ T) \u (fv_defs ds)
  | val_lambda T e  => (fv_typ T) \u (fv_trm e)
  | val_loc n       => \{}
  end
with fv_def (d: def) : vars :=
  match d with
  | def_typ _ T     => (fv_typ T)
  | def_trm _ t     => (fv_trm t)
  end
with fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons tl d   => (fv_defs tl) \u (fv_def d)
  end.

Definition fv_env_types(e: env typ): vars := (fv_in_values (fun T => fv_typ T) e).


(* ###################################################################### *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_env_types x)) in
  let D := gather_vars_with (fun x : sigma     => (dom x) \u (fv_env_types x)) in
  let E := gather_vars_with (fun x : stack     => dom x     ) in
  let F := gather_vars_with (fun x : avar      => fv_avar  x) in
  let G := gather_vars_with (fun x : trm       => fv_trm   x) in
  let H := gather_vars_with (fun x : val       => fv_val   x) in
  let I := gather_vars_with (fun x : def       => fv_def   x) in
  let J := gather_vars_with (fun x : defs      => fv_defs  x) in
  let K := gather_vars_with (fun x : typ       => fv_typ   x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Ltac in_empty_contradiction :=
  solve [match goal with
  | H: _ \in \{} |- _ => rewrite in_empty in H; exfalso; exact H
  end].

Ltac eq_specialize :=
  repeat match goal with
  | H:                 _ = _ -> _ |- _ => specialize (H         eq_refl)
  | H: forall _      , _ = _ -> _ |- _ => specialize (H _       eq_refl)
  | H: forall _ _    , _ = _ -> _ |- _ => specialize (H _ _     eq_refl)
  | H: forall _ _ _  , _ = _ -> _ |- _ => specialize (H _ _ _   eq_refl)
  | H: forall _ _ _ _, _ = _ -> _ |- _ => specialize (H _ _ _ _ eq_refl)
  end.

Ltac crush := eq_specialize; eauto.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

(* ###################################################################### *)
(** ** Operational Semantics *)

Reserved Notation "t1 '/' sta1 '/' sto1 '=>' t2 '/' sta2 '/' sto2" (at level 40, sta1 at level 39, sto1 at level 39, t2 at level 39, sta2 at level 39, sto2 at level 39).

Inductive red : trm -> stack -> store -> trm -> stack -> store -> Prop :=
| red_sel : forall x m sta sto t T ds,
    binds x (val_new T ds) sta ->
    defs_has (open_defs x ds) (def_trm m t) ->
    trm_sel (avar_f x) m / sta / sto => t / sta / sto
| red_app : forall f a sta sto T t,
    binds f (val_lambda T t) sta ->
    trm_app (avar_f f) (avar_f a) / sta / sto => open_trm a t / sta / sto
| red_let : forall v t sta sto x,
    x # sta ->
    trm_let (trm_val v) t / sta / sto => open_trm x t / sta & x ~ v / sto
| red_let_var : forall t sta sto x,
    trm_let (trm_var (avar_f x)) t / sta / sto => open_trm x t / sta / sto
| red_let_tgt : forall t0 t sta sto t0' sta' sto',
    (t0 / sta / sto => t0' / sta' / sto') ->
    trm_let t0 t / sta / sto => trm_let t0' t / sta' / sto'
| red_ref_var : forall x sta sto l T,
    l \notindom sto ->
    trm_ref (avar_f x) T / sta / sto => trm_val (val_loc l) / sta / sto[l :=  x]
| red_asgn : forall x y l sta sto,
    binds x (val_loc l) sta ->
    l \indom sto -> (* TODO is this redundant? *)
    trm_asg (avar_f x) (avar_f y) / sta / sto => trm_var (avar_f y) / sta / sto[l := y]
| red_deref : forall x y (l: addr) sta (sto: store),
    binds x (val_loc l) sta ->
    bindsM l y sto ->
    trm_deref (avar_f x) / sta / sto => trm_var (avar_f y) / sta / sto
where "t1 '/' sta1 '/' sto1 '=>' t2 '/' sta2 '/' sto2" := (red t1 sta1 sto1 t2 sta2 sto2).

(* ###################################################################### *)
(** ** Typing *)

Reserved Notation "G ',' S '|-' t ':' T" (at level 40, S at level 58, t at level 59).
Reserved Notation "G ',' S '|-' T '<:' U" (at level 40, S at level 58, T at level 59).
Reserved Notation "G ',' S '/-' d ':' D" (at level 40, S at level 58, d at level 59).
Reserved Notation "G ',' S '/-' ds '::' D" (at level 40, S at level 58, ds at level 59).

Inductive ty_trm : ctx -> sigma -> trm -> typ -> Prop :=
| ty_var : forall G S x T,
    binds x T G ->
    G, S |- trm_var (avar_f x) : T
| ty_loc : forall G S l T,
    binds l T S ->
    G, S |- trm_val (val_loc l) : typ_ref T
| ty_all_intro : forall L G S T t U,
    (forall x, x \notin L ->
          G & x ~ T, S |- open_trm x t : open_typ x U) ->
    G, S |- trm_val (val_lambda T t) : typ_all T U
| ty_all_elim : forall G S x z V T,
    G, S |- trm_var (avar_f x) : typ_all V T ->
    G, S |- trm_var (avar_f z) : V ->
    G, S |- trm_app (avar_f x) (avar_f z) : open_typ z T
| ty_new_intro : forall L G S T ds,
    (forall x, x \notin L ->
          G & x ~ open_typ x T, S /- open_defs x ds :: open_typ x T) ->
    G, S |- trm_val (val_new T ds) : typ_bnd T
| ty_new_elim : forall G S x m T,
    G, S |- trm_var (avar_f x) : typ_rcd (dec_trm m T) ->
    G, S |- trm_sel (avar_f x) m : T
| ty_let : forall L G S t u T U,
    G, S |- t : T ->
    (forall x, x \notin L ->
      G & x ~ T, S |- open_trm x u : U) ->
    G, S |- trm_let t u : U
| ty_rec_intro : forall G S x T,
    G, S |- trm_var (avar_f x) : open_typ x T ->
    G, S |- trm_var (avar_f x) : typ_bnd T
| ty_rec_elim : forall G S x T,
    G, S |- trm_var (avar_f x) : typ_bnd T ->
    G, S |- trm_var (avar_f x) : open_typ x T
| ty_and_intro : forall G S x T U,
    G, S |- trm_var (avar_f x) : T ->
    G, S |- trm_var (avar_f x) : U ->
    G, S |- trm_var (avar_f x) : typ_and T U
| ty_sub : forall G S t T U,
    G, S |- t : T ->
    G, S |- T <: U ->
    G, S |- t : U
| ty_ref_intro : forall G S x T,
    G, S |- trm_var (avar_f x) : T ->
    G, S |- trm_ref (avar_f x) T : typ_ref T
| ty_ref_elim : forall G S x T,
    G, S |- trm_var (avar_f x) : typ_ref T ->
    G, S |- trm_deref (avar_f x) : T
| ty_asgn : forall G S x y T,
    G, S |- trm_var (avar_f x) : typ_ref T ->
    G, S |- trm_var (avar_f y) : T ->
    G, S |- trm_asg (avar_f x) (avar_f y) : T
where "G ',' S '|-' t ':' T" := (ty_trm G S t T)

with ty_def : ctx -> sigma -> def -> dec -> Prop :=
| ty_def_typ : forall G S A T,
    G, S /- def_typ A T : dec_typ A T T
| ty_def_trm : forall G S a t T,
    G, S |- t : T ->
    G, S /- def_trm a t : dec_trm a T
where "G ',' S '/-' d ':' D" := (ty_def G S d D)

with ty_defs : ctx -> sigma -> defs -> typ -> Prop :=
| ty_defs_one : forall G S d D,
    G, S /- d : D ->
    G, S /- defs_cons defs_nil d :: typ_rcd D
| ty_defs_cons : forall G S ds d T D,
    G, S /- ds :: T ->
    G, S /- d : D ->
    defs_hasnt ds (label_of_def d) ->
    G, S /- defs_cons ds d :: typ_and T (typ_rcd D)
where "G ',' S '/-' ds '::' T" := (ty_defs G S ds T)

with subtyp : ctx -> sigma -> typ -> typ -> Prop :=
| subtyp_top: forall G S T,
    G, S |- T <: typ_top
| subtyp_bot: forall G S T,
    G, S |- typ_bot <: T
| subtyp_refl: forall G S T,
    G, S |- T <: T
| subtyp_trans: forall G S V T U,
    G, S |- V <: T ->
    G, S |- T <: U ->
    G, S |- V <: U
| subtyp_and11: forall G S T U,
    G, S |- typ_and T U <: T
| subtyp_and12: forall G S T U,
    G, S |- typ_and T U <: U
| subtyp_and2: forall G S V T U,
    G, S |- V <: T ->
    G, S |- V <: U ->
    G, S |- V <: typ_and T U
| subtyp_fld: forall G S a T U,
    G, S |- T <: U ->
    G, S |- typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)
| subtyp_typ: forall G S A S1 T1 S2 T2,
    G, S |- S2 <: S1 ->
    G, S |- T1 <: T2 ->
    G, S |- typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)
| subtyp_sel2: forall G S x A V T,
    G, S |- trm_var (avar_f x) : typ_rcd (dec_typ A V T) ->
    G, S |- V <: typ_sel (avar_f x) A
| subtyp_sel1: forall G S x A V T,
    G, S |- trm_var (avar_f x) : typ_rcd (dec_typ A V T) ->
    G, S |- typ_sel (avar_f x) A <: T
| subtyp_all: forall L G S S1 T1 S2 T2,
    G, S |- S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2, S |- open_typ x T1 <: open_typ x T2) ->
    G, S |- typ_all S1 T1 <: typ_all S2 T2
| subtyp_ref: forall G S T U,
    G, S |- T <: U ->
    G, S |- U <: T ->
    G, S |- typ_ref T <: typ_ref U
where "G ',' S '|-' T '<:' U" := (subtyp G S T U).

Reserved Notation "G ',' S '|-!' t ':' T" (at level 40, S at level 58, t at level 59).

Inductive ty_trm_p : ctx -> sigma -> trm -> typ -> Prop :=
| ty_var_p : forall G S x T,
    binds x T G ->
    G, S |-! trm_var (avar_f x) : T
| ty_loc_p : forall G S l T,
    binds l T S ->
    G, S |-! trm_val (val_loc l) : typ_ref T
| ty_all_intro_p : forall L G S T t U,
    (forall x, x \notin L ->
      G & x ~ T, S |- open_trm x t : open_typ x U) ->
    G, S |-! trm_val (val_lambda T t) : typ_all T U
| ty_new_intro_p : forall L G S T ds,
    (forall x, x \notin L ->
      G & (x ~ open_typ x T), S /- open_defs x ds :: open_typ x T) ->
    G, S |-! trm_val (val_new T ds) : typ_bnd T
| ty_rec_elim_p : forall G S x T,
    G, S |-! trm_var (avar_f x) : typ_bnd T ->
    G, S |-! trm_var (avar_f x) : open_typ x T
| ty_and1_p : forall G S x T U,
    G, S |-! trm_var (avar_f x) : typ_and T U ->
    G, S |-! trm_var (avar_f x) : T
| ty_and2_p : forall G S x T U,
    G, S |-! trm_var (avar_f x) : typ_and T U ->
    G, S |-! trm_var (avar_f x) : U
| ty_ref_intro_p : forall G S x T,
    G, S |-! trm_var (avar_f x) : T ->
    G, S |-! trm_ref (avar_f x) T : typ_ref T
| ty_ref_elim_p : forall G S x T,
    G, S |-! trm_var (avar_f x) : typ_ref T ->
    G, S |-! trm_deref (avar_f x) : T
| ty_asgn_p : forall G S x y T,
    G, S |-! trm_var (avar_f x) : typ_ref T ->
    G, S |-! trm_var (avar_f y) : T ->
    G, S |-! trm_asg (avar_f x) (avar_f y) : T
where "G ',' S '|-!' t ':' T" := (ty_trm_p G S t T).

Reserved Notation "G ',' S '|-#' t ':' T" (at level 40, S at level 58, t at level 59).
Reserved Notation "G ',' S '|-#' T '<:' U" (at level 40, S at level 58, T at level 59).

Inductive ty_trm_t : ctx -> sigma -> trm -> typ -> Prop :=
| ty_var_t : forall G S x T,
    binds x T G ->
    G, S |-# trm_var (avar_f x) : T
| ty_loc_t : forall G S l T,
    binds l T S ->
    G, S |-# trm_val (val_loc l) : typ_ref T
| ty_all_intro_t : forall L G S T t U,
    (forall x, x \notin L ->
          G & x ~ T, S |- open_trm x t : open_typ x U) ->
    G, S |-# trm_val (val_lambda T t) : typ_all T U
| ty_all_elim_t : forall G S x z V T,
    G, S |-# trm_var (avar_f x) : typ_all V T ->
    G, S |-# trm_var (avar_f z) : V ->
    G, S |-# trm_app (avar_f x) (avar_f z) : open_typ z T
| ty_new_intro_t : forall L G S T ds,
    (forall x, x \notin L ->
          G & (x ~ open_typ x T), S /- open_defs x ds :: open_typ x T) ->
    G, S |-# trm_val (val_new T ds) : typ_bnd T
| ty_new_elim_t : forall G S x m T,
    G, S |-# trm_var (avar_f x) : typ_rcd (dec_trm m T) ->
    G, S |-# trm_sel (avar_f x) m : T
| ty_let_t : forall L G S t u T U,
    G, S |-# t : T ->
    (forall x, x \notin L ->
          G & x ~ T, S |- open_trm x u : U) ->
    G, S |-# trm_let t u : U
| ty_rec_intro_t : forall G S x T,
    G, S |-# trm_var (avar_f x) : open_typ x T ->
    G, S |-# trm_var (avar_f x) : typ_bnd T
| ty_rec_elim_t : forall G S x T,
    G, S |-# trm_var (avar_f x) : typ_bnd T ->
    G, S |-# trm_var (avar_f x) : open_typ x T
| ty_and_intro_t : forall G S x T U,
    G, S |-# trm_var (avar_f x) : T ->
    G, S |-# trm_var (avar_f x) : U ->
    G, S |-# trm_var (avar_f x) : typ_and T U
| ty_sub_t : forall G S t T U,
    G, S |-# t : T ->
    G, S |-# T <: U ->
    G, S |-# t : U
| ty_ref_intro_t : forall G S x T,
    G, S |-# trm_var (avar_f x) : T ->
    G, S |-# trm_ref (avar_f x) T : typ_ref T
| ty_ref_elim_t : forall G S x T,
    G, S |-# trm_var (avar_f x) : typ_ref T ->
    G, S |-# trm_deref (avar_f x) : T
| ty_asgn_t : forall G S x y T,
    G, S |-# trm_var (avar_f x) : typ_ref T ->
    G, S |-# trm_var (avar_f y) : T ->
    G, S |-# trm_asg (avar_f x) (avar_f y) : T
where "G ',' S '|-#' t ':' T" := (ty_trm_t G S t T)

with subtyp_t : ctx -> sigma -> typ -> typ -> Prop :=
| subtyp_top_t: forall G S T,
    G, S |-# T <: typ_top
| subtyp_bot_t: forall G S T,
    G, S |-# typ_bot <: T
| subtyp_refl_t: forall G S T,
    G, S |-# T <: T
| subtyp_trans_t: forall G S V T U,
    G, S |-# V <: T ->
    G, S |-# T <: U ->
    G, S |-# V <: U
| subtyp_and11_t: forall G S T U,
    G, S |-# typ_and T U <: T
| subtyp_and12_t: forall G S T U,
    G, S |-# typ_and T U <: U
| subtyp_and2_t: forall G S V T U,
    G, S |-# V <: T ->
    G, S |-# V <: U ->
    G, S |-# V <: typ_and T U
| subtyp_fld_t: forall G S a T U,
    G, S |-# T <: U ->
    G, S |-# typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)
| subtyp_typ_t: forall G S A S1 T1 S2 T2,
    G, S |-# S2 <: S1 ->
    G, S |-# T1 <: T2 ->
    G, S |-# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)
| subtyp_sel2_t: forall G S x A T,
    G, S |-! trm_var (avar_f x) : typ_rcd (dec_typ A T T) ->
    G, S |-# T <: typ_sel (avar_f x) A
| subtyp_sel1_t: forall G S x A T,
    G, S |-! trm_var (avar_f x) : typ_rcd (dec_typ A T T) ->
    G, S |-# typ_sel (avar_f x) A <: T
| subtyp_all_t: forall L G S S1 T1 S2 T2,
    G, S |-# S2 <: S1 ->
    (forall x, x \notin L ->
          G & x ~ S2, S |- open_typ x T1 <: open_typ x T2) ->
    G, S |-# typ_all S1 T1 <: typ_all S2 T2
| subtyp_ref_t: forall G S T U,
    G, S |-# T <: U ->
    G, S |-# U <: T ->
    G, S |-# typ_ref T <: typ_ref U
where "G ',' S '|-#' T '<:' U" := (subtyp_t G S T U).


Reserved Notation "G ',' S '~~' sta" (at level 40, S at level 58).

(* well-formed stack *)
Inductive wf_stack: ctx -> sigma -> stack -> Prop :=
| wf_stack_empty: empty, empty ~~ empty
| wf_stack_push: forall G S sta x T v,
    G, S ~~ sta ->
    x # G ->
    x # sta ->
    G, S |- trm_val v : T ->
    G & x ~ T, S ~~ sta & x ~ v
| wf_store_push: forall G S l T sta,
    G, S ~~ sta ->
    l # S ->
    G, S & l ~ T ~~ sta
where "G ',' S '~~' sta" := (wf_stack G S sta).

Reserved Notation "G ',' S '|~' sta" (at level 40, S at level 58).

(* well-typed store *)
Inductive wt_store: ctx -> sigma -> store -> Prop :=
| wt_store_empty: empty, empty |~ emptyM
| wt_store_update: forall G S sto l x T,
    G, S |~ sto ->
    binds l T S ->
    G, S |- trm_var (avar_f x) : T ->
    G, S |~ sto[l := x]
| wt_store_new: forall G S sto l x T,
    G, S |~ sto ->
    l # S ->
    G, S |- trm_var (avar_f x) : T ->
    G, S & l ~ T |~ sto[l := x]
| wt_stack_push: forall G S x T sto,
    G, S |~ sto ->
    x # G ->
    G & x ~ T, S |~ sto
where "G ',' S '|~' sto" := (wt_store G S sto).

(* ###################################################################### *)
(* ###################################################################### *)
(** * Infrastructure *)

(* ###################################################################### *)
(** ** Induction principles *)

Scheme typ_mut := Induction for typ Sort Prop
with   dec_mut := Induction for dec Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
with   val_mut  := Induction for val Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut.

Scheme ty_trm_mut    := Induction for ty_trm    Sort Prop
with   ty_def_mut    := Induction for ty_def    Sort Prop
with   ty_defs_mut   := Induction for ty_defs   Sort Prop.
Combined Scheme ty_mutind from ty_trm_mut, ty_def_mut, ty_defs_mut.

Scheme ts_ty_trm_t_mut := Induction for ty_trm_t Sort Prop
with   ts_subtyp_t     := Induction for subtyp_t Sort Prop.
Combined Scheme ts_mutind_t from ts_ty_trm_t_mut, ts_subtyp_t.

Scheme ts_ty_trm_mut := Induction for ty_trm Sort Prop
with   ts_subtyp     := Induction for subtyp Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm Sort Prop
with   rules_def_mut    := Induction for ty_def Sort Prop
with   rules_defs_mut   := Induction for ty_defs Sort Prop
with   rules_subtyp     := Induction for subtyp Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.

Hint Constructors
  ty_trm ty_def ty_defs subtyp
  ty_trm_p
  ty_trm_t subtyp_t.

Hint Constructors wf_stack wt_store.

Hint Constructors record_has.

Lemma fresh_push_eq_inv: forall A x a (E: env A),
  x # (E & x ~ a) -> False.
Proof.
  intros. rewrite dom_push in H. false H. rewrite in_union.
  left. rewrite in_singleton. reflexivity.
Qed.
