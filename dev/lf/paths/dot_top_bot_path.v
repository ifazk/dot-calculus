Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

Parameter typ_label: Set.
Parameter trm_label: Set.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

Inductive avar : Set :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to store or ctx *)

Inductive pathmode: Set := path_strong | path_general.

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ (* { D } *)
  | typ_and  : typ -> typ -> typ
  | typ_path : path -> typ_label -> typ (* x.a1.a2. ... .an.L *)
  | typ_bnd  : typ -> typ (* rec(x: T) *)
  | typ_all  : typ -> typ -> typ (* all(x: S)T *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec (* A: S..U *)
  | dec_trm  : trm_label -> pathmode -> typ -> dec (* {a: T} or {a:! T} *)
with path : Set :=
  | p_var : avar -> path
  | p_sel : path -> trm_label -> path.

Inductive trm : Set :=
  | trm_val  : val -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm (* let x = t in u *)
  | trm_path : path -> trm
with val : Set :=
  | val_new  : typ -> defs -> val
  | val_lambda : typ -> trm -> val
with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> trm -> def
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.

(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Value environment ("store") *)
Definition sto := env val.

(* ###################################################################### *)
(** ** Definition list membership *)

Definition label_of_def(d: def): label := match d with
| def_typ L _ => label_typ L
| def_trm m _ => label_trm m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ L _ _ => label_typ L
| dec_trm m _ _ => label_trm m
end.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of_def d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of_def d) ds = Some d.
Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
  record_has (typ_rcd D) D
| rh_andl : forall T D,
  record_has (typ_and T (typ_rcd D)) D
| rh_and : forall T D D',
  record_has T D' ->
  record_has (typ_and T D) D'.

(* ###################################################################### *)
(** ** Opening *)

(** Variable opening replaces in some syntax a bound variable with dangling index (k)
   by a free variable x. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_path (k: nat) (u: var) (p: path): path :=
  match p with
  | p_var x   => p_var (open_rec_avar k u x)
  | p_sel q m => p_sel (open_rec_path k u q) m
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_path p L   => typ_path (open_rec_path k u p) L
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1) (open_rec_typ (S k) u T2)
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_trm m p T => dec_trm m p (open_rec_typ k u T)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_path p     => trm_path (open_rec_path k u p)
  | trm_app f a    => trm_app (open_rec_avar k u f) (open_rec_avar k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  end
with open_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds => val_new (open_rec_typ (S k) u T) (open_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (open_rec_typ k u T) (open_rec_trm (S k) u e)
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
Definition open_path u p := open_rec_path  0 u p.

(** Path oopening replaces in some syntax a bound variable with dangling index (k)
   by a path p. *)

Definition open_rec_avar_p (k: nat) (u: path) (a: avar) : path :=
  match a with
  | avar_b i => If k = i then u else p_var (avar_b i)
  | avar_f x => p_var (avar_f x)
  end.

Fixpoint open_rec_path_p (k: nat) (u: path) (p: path): path :=
  match p with
  | p_var x   => open_rec_avar_p k u x
  | p_sel q m => p_sel (open_rec_path_p k u q) m
  end.

Fixpoint open_rec_typ_p (k: nat) (u: path) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec_p k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ_p k u T1) (open_rec_typ_p k u T2)
  | typ_path p L   => typ_path (open_rec_path_p k u p) L
  | typ_bnd T      => typ_bnd (open_rec_typ_p (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ_p k u T1) (open_rec_typ_p (S k) u T2)
  end
with open_rec_dec_p (k: nat) (u: path) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ_p k u T) (open_rec_typ_p k u U)
  | dec_trm m p T => dec_trm m p (open_rec_typ_p k u T)
  end.

Definition open_avar_p u a := open_rec_avar_p  0 u a.
Definition open_typ_p  u t := open_rec_typ_p   0 u t.
Definition open_dec_p  u D := open_rec_dec_p   0 u D.
Definition open_path_p u p := open_rec_path_p  0 u p.


(* ###################################################################### *)
(** ** Free variables *)

Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_path (p: path) : vars :=
  match p with
  | p_var x   => fv_avar x
  | p_sel q L => fv_path q
  end.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_rcd D      => (fv_dec D)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_path p L   => (fv_path p)
  | typ_bnd T      => (fv_typ T)
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  end
with fv_dec (D: dec) : vars :=
  match D with
  | dec_typ L T U => (fv_typ T) \u (fv_typ U)
  | dec_trm m p T => (fv_typ T)
  end.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_val v        => (fv_val v)
  | trm_path p       => (fv_path p)
  | trm_app f a      => (fv_avar f) \u (fv_avar a)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  end
with fv_val (v: val) : vars :=
  match v with
  | val_new T ds    => (fv_typ T) \u (fv_defs ds)
  | val_lambda T e  => (fv_typ T) \u (fv_trm e)
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

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).

(* ###################################################################### *)
(** ** Operational Semantics *)

Inductive red : trm -> sto -> trm -> sto -> Prop :=
| red_sel : forall x m s t T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    red (trm_path (p_sel (p_var (avar_f x)) m)) s t s
| red_pvar : forall x s,
    red (trm_path (p_var (avar_f x))) s (trm_path (p_var (avar_f x))) s
| red_path : forall q m' m s,
    red (trm_path (p_sel (p_sel q m') m)) s (trm_let (trm_path (p_sel q m')) (trm_path (p_sel (p_var (avar_b 0)) m))) s
| red_app : forall f a s T t,
    binds f (val_lambda T t) s ->
    red (trm_app (avar_f f) (avar_f a)) s (open_trm a t) s
| red_let : forall v t s x,
    x # s ->
    red (trm_let (trm_val v) t) s (open_trm x t) (s & x ~ v)
| red_let_var : forall t s x,
    red (trm_let (trm_path (p_var (avar_f x))) t) s (open_trm x t) s
| red_let_tgt : forall t0 t s t0' s',
    red t0 s t0' s' ->
    red (trm_let t0 t) s (trm_let t0' t) s'.

(* ###################################################################### *)
(** ** Typing *)

Inductive tymode: Set := ty_precise | ty_general.
Inductive submode: Set := sub_tight | sub_general.

Inductive ty_trm : tymode -> ctx -> trm -> typ -> Prop :=
| ty_var : forall m1 G x T,
    binds x T G ->
    ty_trm m1 G (trm_path (p_var (avar_f x))) T
| ty_all_intro : forall L m1 G T t U,
    (forall x, x \notin L ->
      ty_trm ty_general (G & x ~ T) (open_trm x t) (open_typ x U)) ->
    ty_trm m1 G (trm_val (val_lambda T t)) (typ_all T U)
| ty_all_elim : forall G x z S T,
    ty_trm ty_general G (trm_path (p_var (avar_f x)))  (typ_all S T) ->
    ty_trm ty_general G (trm_path (p_var (avar_f z)))  S ->
    ty_trm ty_general G (trm_app (avar_f x) (avar_f z)) (open_typ z T)
| ty_new_intro : forall L m1 G T ds,
    (forall x, x \notin L ->
      ty_defs G x (open_typ x T) (open_defs x ds) (open_typ x T)) ->
    ty_trm m1 G (trm_val (val_new T ds)) (typ_bnd T)
| ty_fld_elim : forall G p m1 m m3 T,
    ty_trm m1 G (trm_path p) (typ_rcd (dec_trm m m3 T)) ->
(*    (m1 = ty_precise -> m3 = path_strong) -> *)
    ty_trm m1 G (trm_path (p_sel p m)) T
| ty_let : forall L G t u T U,
    ty_trm ty_general G t T ->
    (forall x, x \notin L ->
      ty_trm ty_general (G & x ~ T) (open_trm x u) U) ->
    ty_trm ty_general G (trm_let t u) U
| ty_rec_intro : forall G x T,
    ty_trm ty_general G (trm_path (p_var (avar_f x)))  (open_typ x T) ->
    ty_trm ty_general G (trm_path (p_var (avar_f x)))  (typ_bnd T)
| ty_rec_elim : forall m1 G p T,
    ty_trm m1 G (trm_path p)  (typ_bnd T) ->
    ty_trm m1 G (trm_path p)  (open_typ_p p T)
| ty_and_intro : forall G p T U,
    ty_trm ty_general G (trm_path p) T ->
    ty_trm ty_general G (trm_path p) U ->
    ty_trm ty_general G (trm_path p) (typ_and T U)
| ty_sub : forall m1 G t T U,
    (m1 = ty_precise -> exists p, t = trm_path p) ->
    ty_trm m1 G t T ->
    subtyp m1 G T U ->
    ty_trm m1 G t U

with ty_def : ctx -> var -> typ -> def -> dec -> Prop := (* Γ; z: U |= d: T U *)
| ty_def_typ : forall x G A T U,
    ty_def G x U (def_typ A T) (dec_typ A T T)
| ty_def_trm : forall x G a t T U,
    ty_trm ty_general (G & x ~ U) t T ->
    ty_def G x U (def_trm a t) (dec_trm a path_general T)
| ty_def_path : forall x G a p U T,
    ty_trm ty_general G (trm_path p) T ->
    norm G p ->
    ty_def G x U (def_trm a (trm_path p)) (dec_trm a path_strong T)
| ty_def_val : forall G x U v T a,
    ty_trm ty_general (G & x ~ U) (trm_val v) T ->
    ty_def G x U (def_trm a (trm_val v)) (dec_trm a path_strong T)
with ty_defs : ctx -> var -> typ -> defs -> typ -> Prop :=
| ty_defs_one : forall x G d D U,
    ty_def G x U d D ->
    ty_defs G x U (defs_cons defs_nil d) (typ_rcd D)
| ty_defs_cons : forall G ds d x T U D,
    ty_defs G x U ds T ->
    ty_def G x U d D ->
    defs_hasnt ds (label_of_def d) ->
    ty_defs G x U (defs_cons ds d) (typ_and T (typ_rcd D))

with norm : ctx -> path -> Prop :=
| norm_var : forall x T G,
    binds x T G ->
    norm G (p_var (avar_f x))
| norm_path : forall p U m G,
    ty_trm ty_general G (trm_path p) (typ_rcd (dec_trm m path_strong U)) ->
    norm G p ->
    norm G (p_sel p m)

with subtyp : tymode -> ctx -> typ -> typ -> Prop :=
| subtyp_top: forall G T,
    subtyp ty_general G T typ_top
| subtyp_bot: forall G T,
    subtyp ty_general G typ_bot T
| subtyp_refl: forall G T,
    subtyp ty_general G T T
| subtyp_trans: forall m1 G S T U,
    subtyp m1 G S T ->
    subtyp m1 G T U ->
    subtyp m1 G S U
| subtyp_and11: forall m1 G T U,
    subtyp m1 G (typ_and T U) T
| subtyp_and12: forall m1 G T U,
    subtyp m1 G (typ_and T U) U
| subtyp_and2: forall G S T U,
    subtyp ty_general G S T ->
    subtyp ty_general G S U ->
    subtyp ty_general G S (typ_and T U)
| subtyp_fld: forall G a T U,
    subtyp ty_general G T U ->
    subtyp ty_general G (typ_rcd (dec_trm a path_general T)) (typ_rcd (dec_trm a path_general U))
| subtyp_typ: forall G A S1 T1 S2 T2,
    subtyp ty_general G S2 S1 ->
    subtyp ty_general G T1 T2 ->
    subtyp ty_general G (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2))
| subtyp_sel2: forall G p A S T,
    ty_trm ty_general G (trm_path p)  (typ_rcd (dec_typ A S T)) ->
    norm G p ->
    subtyp ty_general G S (typ_path p A)
| subtyp_sel1: forall G p A S T,
    ty_trm ty_general G (trm_path p)  (typ_rcd (dec_typ A S T)) ->
    norm G p ->
    subtyp ty_general G (typ_path p A) T
| subtyp_all: forall L G S1 T1 S2 T2,
    subtyp ty_general G S2 S1 ->
    (forall x, x \notin L ->
       subtyp ty_general (G & x ~ S2) (open_typ x T1) (open_typ x T2)) ->
    subtyp ty_general G (typ_all S1 T1) (typ_all S2 T2)
| subtyp_path: forall G a T,
    subtyp ty_general G (typ_rcd (dec_trm a path_strong T)) (typ_rcd (dec_trm a path_general T)).

Inductive wf_sto: ctx -> sto -> Prop :=
| wf_sto_empty: wf_sto empty empty
| wf_sto_push: forall G s x T v,
    wf_sto G s ->
    x # G ->
    x # s ->
    ty_trm ty_precise G (trm_val v) T ->
    wf_sto (G & x ~ T) (s & x ~ v).

Inductive ty_trm_t : tymode -> ctx -> trm -> typ -> Prop :=
| ty_var_t : forall m1 G x T,
    binds x T G ->
    ty_trm_t m1 G (trm_path (p_var (avar_f x))) T
| ty_all_intro_t : forall L m1 G T t U,
    (forall x, x \notin L ->
      ty_trm ty_general (G & x ~ T) (open_trm x t) (open_typ x U)) ->
    ty_trm_t m1 G (trm_val (val_lambda T t)) (typ_all T U)
| ty_all_elim_t : forall G x z S T,
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  (typ_all S T) ->
    ty_trm_t ty_general G (trm_path (p_var (avar_f z)))  S ->
    ty_trm_t ty_general G (trm_app (avar_f x) (avar_f z)) (open_typ z T)
| ty_new_intro_t : forall L m1 G T ds,
    (forall x, x \notin L ->
      ty_defs G x (open_typ x T) (open_defs x ds) (open_typ x T)) ->
    ty_trm_t m1 G (trm_val (val_new T ds)) (typ_bnd T)
| ty_fld_elim_t : forall G p m1 m m3 T,
    ty_trm_t m1 G (trm_path p) (typ_rcd (dec_trm m m3 T)) ->
(*     (m1 = ty_precise -> m3 = path_strong) -> *)
    ty_trm_t m1 G (trm_path (p_sel p m)) T
| ty_let_t : forall L G t u T U,
    ty_trm_t ty_general G t T ->
    (forall x, x \notin L ->
      ty_trm ty_general (G & x ~ T) (open_trm x u) U) ->
    ty_trm_t ty_general G (trm_let t u) U
| ty_rec_intro_t : forall G x T,
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  (open_typ x T) ->
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  (typ_bnd T)
| ty_rec_elim_t : forall m1 G p T,
    ty_trm_t m1 G (trm_path p)  (typ_bnd T) ->
    ty_trm_t m1 G (trm_path p)  (open_typ_p p T)
| ty_and_intro_t : forall G x T U,
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  T ->
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  U ->
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  (typ_and T U)
| ty_sub_t : forall m1 G t T U,
    (m1 = ty_precise -> exists p, t = trm_path p) ->
    ty_trm_t m1 G t T ->
    subtyp_t m1 G T U ->
    ty_trm_t m1 G t U

with norm_t : ctx -> path -> Prop :=
| norm_var_t : forall x T G,
    binds x T G ->
    norm_t G (p_var (avar_f x))
| norm_path_t : forall p U m G,
    ty_trm_t ty_general G (trm_path p) (typ_rcd (dec_trm m path_strong U)) ->
    norm_t G p ->
    norm_t G (p_sel p m)

with subtyp_t : tymode -> ctx -> typ -> typ -> Prop :=
| subtyp_top_t: forall G T,
    subtyp_t ty_general G T typ_top
| subtyp_bot_t: forall G T,
    subtyp_t ty_general G typ_bot T
| subtyp_refl_t: forall G T,
    subtyp_t ty_general G T T
| subtyp_trans_t: forall m1 G S T U,
    subtyp_t m1 G S T ->
    subtyp_t m1 G T U ->
    subtyp_t m1 G S U
| subtyp_and11_t: forall m1 G T U,
    subtyp_t m1 G (typ_and T U) T
| subtyp_and12_t: forall m1 G T U,
    subtyp_t m1 G (typ_and T U) U
| subtyp_and2_t: forall G S T U,
    subtyp_t ty_general G S T ->
    subtyp_t ty_general G S U ->
    subtyp_t ty_general G S (typ_and T U)
| subtyp_fld_t: forall G a T U,
    subtyp_t ty_general G T U ->
    subtyp_t ty_general G (typ_rcd (dec_trm a path_general T)) (typ_rcd (dec_trm a path_general U))
| subtyp_typ_t: forall G A S1 T1 S2 T2,
    subtyp_t ty_general G S2 S1 ->
    subtyp_t ty_general G T1 T2 ->
    subtyp_t ty_general G (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2))
| subtyp_sel2_t: forall G p A T,
    ty_trm ty_precise G (trm_path p) (typ_rcd (dec_typ A T T)) ->
    norm_t G p ->
    subtyp_t ty_general G T (typ_path p A)
| subtyp_sel1_t: forall G p A T,
    ty_trm ty_precise G (trm_path p) (typ_rcd (dec_typ A T T)) ->
    norm_t G p ->
    subtyp_t ty_general G (typ_path p A) T
| subtyp_all_t: forall L G S1 T1 S2 T2,
    subtyp_t ty_general G S2 S1 ->
    (forall x, x \notin L ->
       subtyp ty_general (G & x ~ S2) (open_typ x T1) (open_typ x T2)) ->
    subtyp_t ty_general G (typ_all S1 T1) (typ_all S2 T2)
| subtyp_path_t: forall G a T,
    subtyp_t ty_general G (typ_rcd (dec_trm a path_strong T)) (typ_rcd (dec_trm a path_general T)).

    
(* ###################################################################### *)
(* ###################################################################### *)
(** * Infrastructure *)

(* ###################################################################### *)
(** ** Induction principles *)

Scheme typ_mut := Induction for typ Sort Prop
with   dec_mut := Induction for dec Sort Prop
with   path_mut := Induction for path Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut, path_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
with   val_mut  := Induction for val Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut.

Scheme ty_trm_mut    := Induction for ty_trm    Sort Prop
with   ty_def_mut    := Induction for ty_def    Sort Prop
with   ty_defs_mut   := Induction for ty_defs   Sort Prop
with   norm_mut      := Induction for norm      Sort Prop.
Combined Scheme ty_mutind from ty_trm_mut, ty_def_mut, ty_defs_mut, norm_mut.

Scheme tds_ty_trm_mut  := Induction for ty_trm    Sort Prop
with   tds_ty_def_mut  := Induction for ty_def    Sort Prop
with   tds_ty_defs_mut := Induction for ty_defs   Sort Prop
with   tds_subtyp      := Induction for subtyp    Sort Prop.
Combined Scheme tds_mutind from tds_ty_trm_mut, tds_ty_def_mut, tds_ty_defs_mut, tds_subtyp.

Scheme ts_ty_trm_mut  := Induction for ty_trm    Sort Prop
with   ts_subtyp      := Induction for subtyp    Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme ts_ty_trm_mut_t  := Induction for ty_trm_t    Sort Prop
with   ts_subtyp_t      := Induction for subtyp_t    Sort Prop.
Combined Scheme ts_mutind_t from ts_ty_trm_mut_t, ts_subtyp_t.

Scheme rules_trm_mut    := Induction for ty_trm    Sort Prop
with   rules_def_mut    := Induction for ty_def    Sort Prop
with   rules_defs_mut   := Induction for ty_defs   Sort Prop
with   rules_norm_mut   := Induction for norm      Sort Prop
with   rules_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_norm_mut, rules_subtyp.

(* ###################################################################### *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x : sto       => dom x     ) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let F := gather_vars_with (fun x : trm       => fv_trm   x) in
  let G := gather_vars_with (fun x : val       => fv_val   x) in
  let H := gather_vars_with (fun x : def       => fv_def   x) in
  let I := gather_vars_with (fun x : defs      => fv_defs  x) in
  let J := gather_vars_with (fun x : typ       => fv_typ   x) in
  let K := gather_vars_with (fun x : path      => fv_path  x) in
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

Hint Constructors
  ty_trm ty_def ty_defs subtyp ty_trm_t subtyp_t.

Hint Constructors wf_sto.

Lemma fresh_push_eq_inv: forall A x a (E: env A),
  x # (E & x ~ a) -> False.
Proof.
  intros. rewrite dom_push in H. false H. rewrite in_union.
  left. rewrite in_singleton. reflexivity.
Qed.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Proofs *)

(* ###################################################################### *)
(** ** Weakening *)

Lemma weaken_rules:
  (forall m1 G t T, ty_trm m1 G t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_trm m1 (G1 & G2 & G3) t T) /\
  (forall G x T d D, ty_def G x T d D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3 & x ~ T) ->
    ty_def (G1 & G2 & G3) x T d D) /\
  (forall G x U ds T, ty_defs G x U ds T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3 & x ~ U) ->
    ty_defs (G1 & G2 & G3) x U ds T) /\
  (forall G p, norm G p -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    norm (G1 & G2 & G3) p) /\
  (forall m1 G T U, subtyp m1 G T U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subtyp m1 (G1 & G2 & G3) T U).
Proof.
  apply rules_mutind; try solve [eauto].
  + intros. subst.
    eapply ty_var. eapply binds_weaken; auto.
  + intros. subst.
    apply_fresh ty_all_intro as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    - specialize (H z zL G1 G2 G3). apply* H.
  + intros. subst.
    apply_fresh ty_let as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
  + intros. subst. apply ty_def_trm.
    rewrite <- concat_assoc. apply H; rewrite concat_assoc. reflexivity. assumption.
  + intros. subst. apply ty_def_val.
    rewrite <- concat_assoc. apply H; rewrite concat_assoc. reflexivity. assumption.
  + intros. subst.
    eapply norm_var. eapply binds_weaken; eassumption.
  + intros. subst.
    eapply norm_path. eapply H; eauto.
    eapply H0; auto.
  + intros. subst.
    apply_fresh subtyp_all as z.
    auto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
Qed.

Lemma weaken_ty_trm:  forall m1 G1 G2 t T,
    ty_trm m1 G1 t T ->
    ok (G1 & G2) ->
    ty_trm m1 (G1 & G2) t T.
Proof. 
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_subtyp: forall m1 G1 G2 S U,
  subtyp m1 G1 S U ->
  ok (G1 & G2) ->
  subtyp m1 (G1 & G2) S U.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_norm: forall G G' p,
  norm G p ->
  ok (G & G') ->
  norm (G & G') p.
Proof.
  introv Hn Hok.
  assert (G & G' = G & G' & empty) as EqG by (rewrite* concat_empty_r).
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity. rewrite <- EqG. assumption.
Qed.

Lemma weaken_defs: forall G1 z U ds T G2,
  ty_defs G1 z U ds T ->
  ok (G1 & G2 & z ~ U) -> 
  ty_defs (G1 & G2) z U ds T.
Proof.
  introv Hn Hok.
  assert (G1 & G2 = G1 & G2 & empty) as EqG by (rewrite* concat_empty_r).
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity. rewrite <- EqG. assumption.
Qed.

(* ###################################################################### *)
(** ** Well-formed store *)

Lemma wf_sto_to_ok_s: forall s G,
  wf_sto G s -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_sto_to_ok_G: forall s G,
  wf_sto G s -> ok G.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_sto_to_ok_s wf_sto_to_ok_G.

Lemma ctx_binds_to_sto_binds_raw: forall s G x T,
  wf_sto G s ->
  binds x T G ->
  exists G1 G2 v, G = G1 & (x ~ T) & G2 /\ binds x v s /\ ty_trm ty_precise G1 (trm_val v) T.
Proof.
  introv Wf Bi. gen x T Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) v.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [ds' [Eq [Bi' Tyds]]]]].
      subst. exists G1 (G2 & x ~ T) ds'. rewrite concat_assoc. auto.
Qed.

Lemma ctx_binds_to_sto_binds_typing: forall G s x T,
  wf_sto G s ->
  binds x T G ->
  exists v, binds x v s /\ ty_trm ty_precise G (trm_val v) T.
Proof.
  introv Hwf Bi.
  lets A: (ctx_binds_to_sto_binds_raw Hwf Bi).
  destruct A as [G1 [G2 [v [HeqG [Bis Hty]]]]].
  exists v. split; eauto.
  subst. rewrite <- concat_assoc.
  apply weaken_ty_trm; eauto.
  rewrite concat_assoc.
  eapply wf_sto_to_ok_G; eauto.
Qed.

Lemma sto_binds_to_ctx_binds_raw: forall s G x v,
  wf_sto G s ->
  binds x v s ->
  exists G1 G2 T, G = G1 & (x ~ T) & G2 /\ ty_trm ty_precise G1 (trm_val v) T.
Proof.
  introv Wf Bi. gen x v Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) T.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [T0' [Eq Ty]]]].
      subst. exists G1 (G2 & x ~ T) T0'. rewrite concat_assoc. auto.
Qed.

Lemma typing_implies_bound: forall m1 G x T,
  ty_trm m1 G (trm_path (p_var (avar_f x)))  T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_path (p_var (avar_f x))) as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm; eauto];
    try solve [inversion Heqt; eapply IHty_trm1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.

Lemma typing_implies_bound_t: forall m1 G x T,
  ty_trm_t m1 G (trm_path (p_var (avar_f x)))  T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_path (p_var (avar_f x)))  as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm_t; eauto];
    try solve [inversion Heqt; eapply IHty_trm_t1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.

(* ###################################################################### *)
(** ** Substitution *)

Definition subst_avar (z: var) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => (avar_f (If x = z then u else x))
  end.

Fixpoint subst_path (z: var) (u: var) (p: path) : path :=
  match p with
  | p_var x   => p_var (subst_avar z u x)
  | p_sel p a => p_sel (subst_path z u p) a
  end.

Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_path p L   => typ_path (subst_path z u p) L
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  end
with subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_trm L m U => dec_trm L m (subst_typ z u U)
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_val v        => trm_val (subst_val z u v)
  | trm_path p       => trm_path (subst_path z u p)
  | trm_app x1 x2    => trm_app (subst_avar z u x1) (subst_avar z u x2)
  | trm_let t1 t2    => trm_let (subst_trm z u t1) (subst_trm z u t2)
  end
with subst_val (z: var) (u: var) (v: val) : val :=
  match v with
  | val_new T ds     => val_new (subst_typ z u T) (subst_defs z u ds)
  | val_lambda T t   => val_lambda (subst_typ z u T) (subst_trm z u t)
  end
with subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_typ L T => def_typ L (subst_typ z u T)
  | def_trm L t => def_trm L (subst_trm z u t)
  end
with subst_defs (z: var) (u: var) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (subst_defs z u rest) (subst_def z u d)
  end.

Definition subst_ctx (z: var) (u: var) (G: ctx) : ctx := map (subst_typ z u) G.

(* ###################################################################### *)
(** ** Lemmas for var-by-var substitution *)

Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = a).
Proof.
  intros. destruct* a. simpl. case_var*. simpls. notin_false.
Qed.

Lemma subst_fresh_typ_dec_path: forall x y,
  (forall T : typ  , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec  , x \notin fv_dec  D  -> subst_dec  x y D  = D ) /\
  (forall P : path , x \notin fv_path P  -> subst_path x y P  = P ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply subst_fresh_avar. assumption. 
Qed.

Definition subst_fresh_typ (x y: var) := proj31 (subst_fresh_typ_dec_path x y).
Definition subst_fresh_dec (x y: var) := proj32 (subst_fresh_typ_dec_path x y).
Definition subst_fresh_path(x y: var) := proj33 (subst_fresh_typ_dec_path x y).

Lemma subst_fresh_trm_val_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall v : val , x \notin fv_val  v  -> subst_val  x y v  = v ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
  (apply* subst_fresh_avar || apply* subst_fresh_path || apply* subst_fresh_typ_dec_path).
Qed.

Definition subst_fresh_trm (x y: var) := proj41 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_val (x y: var) := proj42 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_def (x y: var) := proj43 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_defs(x y: var) := proj44 (subst_fresh_trm_val_def_defs x y).

Lemma invert_fv_ctx_types_push: forall x z T G,
  x \notin fv_ctx_types (G & z ~ T) -> x \notin fv_typ T /\ x \notin (fv_ctx_types G).
Proof.
  introv N.
  unfold fv_ctx_types in *.
  unfold fv_in_values in *.
  rewrite <- cons_to_push in *.
  rewrite values_def in *.
  unfold LibList.map in *.
  do 2 rewrite LibList.fold_right_cons in *.
  simpl in *.
  apply notin_union in N. exact N.
Qed.

Lemma subst_fresh_ctx: forall x y G,
  x \notin fv_ctx_types G -> subst_ctx x y G = G.
Proof.
  intros x y.
  apply (env_ind (fun G => x \notin fv_ctx_types G -> subst_ctx x y G = G)).
  + intro N. unfold subst_ctx. apply map_empty.
  + intros G z T IH N.
    apply invert_fv_ctx_types_push in N. destruct N as [N1 N2].
    unfold subst_ctx in *. rewrite map_push.
    rewrite (IH N2).
    rewrite ((proj31 (subst_fresh_typ_dec_path _ _)) _ N1).
    reflexivity.
Qed.

Definition subst_fvar(x y z: var): var := If z = x then y else z.

Lemma subst_open_commute_avar: forall x y u,
  (forall a: avar, forall n: Datatypes.nat,
    subst_avar x y (open_rec_avar n u a)
    = open_rec_avar n (subst_fvar x y u) (subst_avar  x y a)).
Proof.
  intros. unfold subst_fvar, subst_avar, open_avar, open_rec_avar. destruct a.
  + repeat case_if; auto.
  + case_var*.
Qed.

Lemma subst_open_commute_path_p: forall x y u,
  (forall p: path, forall n: nat,
    subst_path x y (open_rec_path_p n u p)
    = open_rec_path_p n (subst_path x y u) (subst_path x y p)).
Proof.
  intros. induction p. 
  - unfold subst_path, open_rec_path_p, open_rec_avar_p. destruct a; simpl.
    + case_if*. 
    + case_var*. 
  - simpl. f_equal. assumption. 
Qed. 

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_dec_path: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec n u D)
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y D)) /\
  (forall p : path, forall n: nat,
     subst_path x y (open_rec_path n u p)
     = open_rec_path n (subst_fvar x y u) (subst_path x y p)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. 
  destruct a; simpl. case_if*. case_var*. 
Qed.

Lemma subst_open_commute_typ: forall x y u T,
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commute_typ_dec_path.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_dec_path_p: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ_p n u t)
     = open_rec_typ_p n (subst_path x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec_p n u D)
     = open_rec_dec_p n (subst_path x y u) (subst_dec x y D)) /\
  (forall p: path, forall n: nat,
    subst_path x y (open_rec_path_p n u p)
    = open_rec_path_p n (subst_path x y u) (subst_path x y p)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. 
  destruct a; simpl. case_if*. case_var*.
Qed.

Lemma subst_open_commute_typ_p: forall x y u T,
  subst_typ x y (open_typ_p u T) = open_typ_p (subst_path x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commute_typ_dec_path_p.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_trm_val_def_defs: forall x y u,
  (forall t : trm, forall n: Datatypes.nat,
     subst_trm x y (open_rec_trm n u t)
     = open_rec_trm n (subst_fvar x y u) (subst_trm x y t)) /\
  (forall v : val, forall n: Datatypes.nat,
     subst_val x y (open_rec_val n u v)
     = open_rec_val n (subst_fvar x y u) (subst_val x y v)) /\
  (forall d : def , forall n: Datatypes.nat,
     subst_def x y (open_rec_def n u d)
     = open_rec_def n (subst_fvar x y u) (subst_def x y d)) /\
  (forall ds: defs, forall n: Datatypes.nat,
     subst_defs x y (open_rec_defs n u ds)
     = open_rec_defs n (subst_fvar x y u) (subst_defs x y ds)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal*;
    (apply* subst_open_commute_avar || apply* subst_open_commute_typ_dec_path).
Qed.

Lemma subst_open_commute_trm: forall x y u t,
  subst_trm x y (open_trm u t) = open_trm (subst_fvar x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commute_trm_val_def_defs.
Qed.

Lemma subst_open_commute_defs: forall x y u ds,
  subst_defs x y (open_defs u ds) = open_defs (subst_fvar x y u) (subst_defs x y ds).
Proof.
  intros. apply* subst_open_commute_trm_val_def_defs.
Qed.

(* "Introduce a substitution after open": Opening a term t with a var u is the
   same as opening t with x and then replacing x by u. *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) ->
  open_trm u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_trm.
  destruct (@subst_fresh_trm_val_def_defs x u) as [Q _]. rewrite* (Q t).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) ->
  open_defs u ds = subst_defs x u (open_defs x ds).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_defs.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [_ [_ Q]]]. rewrite* (Q ds).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) ->
  open_typ u T = subst_typ x u (open_typ x T).
Proof.
  introv Fr. unfold open_typ. rewrite* subst_open_commute_typ.
  destruct (@subst_fresh_typ_dec_path x u) as [Q _]. rewrite* (Q T).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_label_of_def: forall x y d,
  label_of_def d = label_of_def (subst_def x y d).
Proof.
  intros. destruct d; simpl; reflexivity.
Qed.

Lemma subst_defs_hasnt: forall x y l ds,
  defs_hasnt ds l ->
  defs_hasnt (subst_defs x y ds) l.
Proof.
  intros x y l ds. unfold defs_hasnt. induction ds; introv Eq.
  - simpl. reflexivity.
  - unfold get_def. simpl. rewrite <- subst_label_of_def.
    simpl in Eq. case_if. apply (IHds Eq).
Qed.

Lemma binds_destruct: forall {A} x (v:A) E,
  binds x v E ->
  exists E' E'', E = E' & x ~ v & E''.
Proof.
  introv Hb. induction E using env_ind. false* binds_empty_inv.
  destruct (binds_push_inv Hb) as [[Hx HT] | [Hn Hbx]]; subst.
  - exists E (@empty A). rewrite concat_empty_r. reflexivity.
  - apply binds_push_neq_inv in Hb. destruct (IHE Hb) as [E' [E'' HE]]. subst.
    exists E' (E'' & x0 ~ v0). rewrite concat_assoc. reflexivity. assumption.
Qed.

Lemma double_binds_false: forall E1 E2 x (v v' : typ),
  ok (E1 & x ~ v & E2 & x ~ v') -> False.
Proof.
  intros.
  apply ok_push_inv in H. destruct H as [H Hnot].
  assert (binds x v (E1 & x ~ v & E2)) as HBi. {
    lets Ht: (binds_tail x v E1).
    apply (binds_concat_left_ok H Ht).
  }
  false (binds_fresh_inv HBi Hnot).
Qed.

Lemma binds_middle: forall E1 E2 E1' E2' x (v v' : typ), 
  ok (E1 & x ~ v & E2) ->
  E1 & x ~ v & E2 = E1' & x ~ v' & E2' ->
  E1 = E1' /\ v = v' /\ E2 = E2'.
Proof.
  introv Hok. gen E1' E2'. induction E2 using env_ind; intros.
  - rewrite concat_empty_r in H.
    destruct E2' using env_ind.
    + rewrite concat_empty_r in H. apply eq_push_inv in H.
      destruct H as [_ [Hv Hs]]. auto.
    + rewrite concat_assoc in H. rewrite concat_empty_r in Hok.
      lets Heq: (eq_push_inv H).
      destruct Heq as [Hx [Hv Hs]]. subst.
      false (double_binds_false Hok).
  - destruct E2' using env_ind.
    + rewrite concat_empty_r in H. rewrite concat_assoc in H. apply eq_push_inv in H.
      destruct H as [Hx [Hv Hs]]. subst.
      rewrite concat_assoc in Hok.
      false (double_binds_false Hok).
    + repeat rewrite concat_assoc in H.
      apply eq_push_inv in H. destruct H as [Hx [Hv Hs]]. subst.
      rewrite concat_assoc in Hok. apply ok_push_inv_ok in Hok.
      specialize (IHE2 Hok E1' E2' Hs).
      destruct IHE2 as [Hs' [Hv Hs'']]. subst. auto.
Qed.

(* ###################################################################### *)
(** ** The substitution principle *)

Lemma subst_rules: forall y S,
  (forall m1 G t T, ty_trm m1 G t T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general (G1 & (subst_ctx x y G2)) (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    m1 = ty_general ->
    ty_trm m1 (G1 & (subst_ctx x y G2)) (subst_trm x y t) (subst_typ x y T)) /\
  (forall G z T d D, ty_def G z T d D -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2 & z ~ T) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general (G1 & (subst_ctx x y G2)) (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    ty_def (G1 & (subst_ctx x y G2)) z (subst_typ x y T) (subst_def x y d) (subst_dec x y D)) /\
  (forall G z T ds U, ty_defs G z T ds U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2 & z ~ T) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general (G1 & (subst_ctx x y G2)) (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    ty_defs (G1 & (subst_ctx x y G2)) z (subst_typ x y T) (subst_defs x y ds) (subst_typ x y U)) /\
  (forall G p, norm G p -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general (G1 & (subst_ctx x y G2)) (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    norm (G1 & (subst_ctx x y G2)) (subst_path x y p)) /\
  (forall m1 G T U, subtyp m1 G T U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general (G1 & (subst_ctx x y G2))  (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    m1 = ty_general ->
    subtyp m1 (G1 & (subst_ctx x y G2)) (subst_typ x y T) (subst_typ x y U)).
Proof.
  intros y S. apply rules_mutind; intros; subst.
  - (* ty_var *)
    simpl. case_if.
    + apply binds_middle_eq_inv in b. subst. assumption. assumption.
    + apply subst_fresh_ctx with (y:=y) in H1.
      apply binds_subst in b.
      apply ty_var. rewrite <- H1.
      unfold subst_ctx. rewrite <- map_concat.
      apply binds_map. assumption. assumption.
  - (* ty_all_intro *)
    simpl.
    apply_fresh ty_all_intro as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    rewrite <- A at 3. rewrite <- subst_open_commute_typ.
    assert (subst_ctx x y G2 & z ~ subst_typ x y T = subst_ctx x y (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
  - (* ty_all_elim *)
    simpl. rewrite subst_open_commute_typ.
    eapply ty_all_elim.
    simpl in H.
    apply H; eauto.
    apply H0; eauto.
  - (* ty_new_intro *)
    simpl.
    apply_fresh ty_new_intro as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- A at 3. rewrite <- A at 4.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_defs.
    
    assert (subst_ctx x y G2 & z ~ subst_typ x y (open_typ z T) = subst_ctx x y (G2 & z ~ open_typ z T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    } 
    apply H; eauto.
  - (* ty_fld_elim *)
    simpl. eapply ty_fld_elim. apply H; eauto. 
  - (* ty_let *)
    simpl.
    apply_fresh ty_let as z; eauto.
    assert (subst_ctx x y G2 & z ~ subst_typ x y T = subst_ctx x y (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    apply H0 with (x0:=z); eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
  - (* ty_rec_intro *)
    simpl. apply ty_rec_intro.
    assert (trm_path (p_var (avar_f (If x = x0 then y else x))) 
        = subst_trm x0 y (trm_path (p_var (avar_f x))) ) as A. {
      simpl. reflexivity.
    }
    rewrite A.
    assert (open_typ (If x = x0 then y else x) (subst_typ x0 y T) = subst_typ x0 y (open_typ x T)) as B. {
      rewrite subst_open_commute_typ. unfold subst_fvar. reflexivity.
    }
    rewrite B. apply* H.
  - (* ty_rec_elim *)
    simpl. rewrite subst_open_commute_typ_p.
    apply ty_rec_elim.
    apply H; eauto.
  - (* ty_and_intro *)
    simpl.
    apply ty_and_intro; eauto.
  - (* ty_sub *)
    eapply ty_sub; eauto.
    intro Contra. inversion Contra.
  - (* ty_def_typ *)
    simpl. eapply ty_def_typ; eauto.
  - (* ty_def_trm *)
    simpl. apply ty_def_trm.
    assert (G1 & subst_ctx x0 y G2 & x ~ subst_typ x0 y U = G1 & subst_ctx x0 y (G2 & x ~ U)) as Hs. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. rewrite concat_assoc. 
      reflexivity.
    }
    rewrite Hs.
    assert (x <> x0) as Hn. {
      rewrite <- concat_assoc in H1.
      apply ok_middle_inv_r in H1. unfold not. intro Hx. subst. unfold notin in H1.
      unfold not in H1. simpl_dom.
      assert (x0 \in \{ x0} \u dom G2) as Hx. {
        rewrite in_union. left. rewrite in_singleton. reflexivity.
      }
      apply H1 in Hx. false.
    }
    apply H; auto. rewrite concat_assoc. reflexivity. rewrite concat_assoc.
    assumption.
    assert (subst_ctx x0 y (G2 & x ~ U) = (subst_ctx x0 y G2) & x ~ (subst_typ x0 y U)). {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite H0. rewrite concat_assoc. apply weaken_ty_trm.
    apply H3. 
    assert (subst_ctx x0 y G2 & x ~ subst_typ x0 y U = subst_ctx x0 y (G2 & x ~ U)) as Hsu by auto.
    rewrite <- concat_assoc. rewrite Hsu. apply ok_concat_map. rewrite <- concat_assoc in H1.
    apply ok_remove in H1. assumption.
  - (* ty_def_path *)
    simpl. apply ty_def_path. apply* H. auto.
  - (* ty_def_val *)
    simpl. apply ty_def_val. specialize (H G1 (G2 & x ~ U) x0). 
    replace (G1 & subst_ctx x0 y G2 & x ~ subst_typ x0 y U) with (G1 & subst_ctx x0 y (G2 & x ~ U)).
    + apply H; auto; try rewrite* concat_assoc. unfold subst_ctx. rewrite map_concat. 
      rewrite concat_assoc. unfold subst_ctx in H3. apply* weaken_ty_trm. 
      apply ok_concat_map. rewrite <- concat_assoc in H1. 
      apply ok_remove in H1. rewrite concat_assoc in H1. apply ok_push. 
      * apply* ok_concat_map. 
      * apply ok_push_inv in H1. destruct* H1. 
    + unfold subst_ctx. rewrite map_concat. rewrite concat_assoc. rewrite* map_single.
  - (* ty_defs_one *)
    simpl. apply* ty_defs_one.
  - (* ty_defs_cons *)
    simpl. apply* ty_defs_cons. rewrite <- subst_label_of_def. apply subst_defs_hasnt. assumption.
  - (* norm_var *)
    destruct (typing_implies_bound H2) as [U Hb].
    simpl. case_if.
    * apply* norm_var.
    * destruct (binds_concat_inv b) as [b' | [Hx  b']]; clear b. 
      + unfold subst_ctx. eapply norm_var. eauto.
      + lets Hp: (binds_push_neq_inv b' H).
        eapply norm_var. eapply binds_concat_left. eassumption.
        unfold notin. intro. unfolds subst_ctx. simpl_dom. false.
  - (* norm_path *)
    apply* norm_path. apply* H.
  - (* subtyp_top *)
    apply subtyp_top.
  - (* subtyp_bot *)
    apply subtyp_bot.
  - (* subtyp_refl *)
    apply subtyp_refl.
  - (* subtyp_trans *)
    eapply subtyp_trans; eauto.
  - (* subtyp_and11 *)
    eapply subtyp_and11; eauto.
  - (* subtyp_and12 *)
    eapply subtyp_and12; eauto.
  - (* subtyp_and2 *)
    eapply subtyp_and2; eauto.
  - (* subtyp_fld *)
    eapply subtyp_fld; eauto.
  - (* subtyp_typ *)
    eapply subtyp_typ; eauto.
  - (* subtyp_sel2 *)
    eapply subtyp_sel2; eauto.
    eapply H; eauto.
  - (* subtyp_sel1 *)
    eapply subtyp_sel1; eauto.
    eapply H; eauto.
  - (* subtyp_all *)
    simpl. apply_fresh subtyp_all as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- A at 3.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_typ.
    assert (subst_ctx x y G2 & z ~ subst_typ x y S2 = subst_ctx x y (G2 & z ~ S2)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    apply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
  - (* subtyp_path *)
    apply subtyp_path.
Qed.

Lemma subst_ty_trm: forall y S G x t T,
    ty_trm ty_general (G & x ~ S) t T -> 
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    ty_trm ty_general G (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    ty_trm ty_general G (subst_trm x y t) (subst_typ x y T).
Proof.
  intros.
  apply (proj51 (subst_rules y S)) with (G1:=G) (G2:=empty) (x:=x) in H.
  unfold subst_ctx in H. rewrite map_empty in H. rewrite concat_empty_r in H.
  apply H.
  rewrite concat_empty_r. reflexivity.
  rewrite concat_empty_r. assumption.
  assumption.
  unfold subst_ctx. rewrite map_empty. rewrite concat_empty_r. assumption.
  reflexivity.
Qed.

Lemma subst_ty_defs: forall y S G x ds z U T,
    ty_defs (G & x ~ S) z U ds T ->
    ok (G & x ~ S & z ~ U) ->
    x \notin fv_ctx_types G ->
    ty_trm ty_general G (trm_path (p_var (avar_f y))) (subst_typ x y S) ->
    ty_defs G z (subst_typ x y U) (subst_defs x y ds) (subst_typ x y T).
Proof.
  intros.
  apply (proj53 (subst_rules y S)) with (G1:=G) (G2:=empty) (x:=x) in H.
  unfold subst_ctx in H. rewrite map_empty in H. rewrite concat_empty_r in H.
  apply H.
  rewrite concat_empty_r. reflexivity.
  rewrite concat_empty_r. assumption.
  assumption.
  unfold subst_ctx. rewrite map_empty. rewrite concat_empty_r. assumption. 
Qed.

(* ###################################################################### *)
(** Renaming *)

Lemma ok_extend: forall E F x (v: typ),
  ok (E & F) ->
  x # (E & F) ->
  ok (E & x ~ v & F).
Proof.
  introv Hok Hn.
  induction F using env_ind; introv;
  autorewrite with rew_env_map; rew_env_concat.
  rewrite concat_empty_r in *. apply* ok_push.
  rewrite concat_assoc in *.
  apply ok_push; auto.
  intro. clear IHF. simpl_dom.
  rewrite in_union in H. destruct H. rewrite in_union in H. destruct H.
  - destruct (ok_push_inv Hok) as [_ Hnef].
    simpl_dom. rewrite notin_union in Hnef. destruct Hnef as [Hne _]. auto.
  - rewrite in_singleton in H. subst.
    rewrite notin_union in Hn. destruct Hn. apply notin_same in H. auto.
  - destruct (ok_push_inv Hok) as [_ Hnef].
    simpl_dom. rewrite notin_union in Hnef. destruct Hnef as [_ Hnf]. auto.
Qed.

Lemma fv_typ_ctx: forall x y T G,
  binds x T G ->
  y \in fv_typ T ->
  y \in fv_ctx_types G.
Proof.
  intros. induction G using env_ind.
  - false* binds_empty_inv.
  - destruct (binds_push_inv H) as [[Hx0 Hv] | [Hn Hb]];
    unfolds fv_ctx_types; unfolds fv_in_values;
    rewrite values_def, concat_def, single_def in *; simpl; subst; rewrite* in_union.
Qed.

Definition rename_var (x y z : var)  := If z = x then y else z.

Definition rename_ctx x y G := subst_ctx x y (map_keys (rename_var x y) G).

Lemma map_keys_notin: forall x y (G:ctx),
  x # G ->
  map_keys (rename_var x y) G = G.
Proof.
  intros. induction G using env_ind. rewrite map_keys_empty. reflexivity.
  rewrite map_keys_push. rewrite* IHG. assert (x <> x0) as Hxx0. {
    simpl_dom. rewrite notin_union in H. destruct H as [H _]. auto. 
  }
  unfold rename_var. case_if. reflexivity.
Qed.

Lemma binds_map_keys: forall x y G' (T:typ) G'',
  ok (G' & x ~ T & G'') ->
  map_keys (rename_var x y) (G' & x ~ T & G'') = G' & y ~ T & G''.
Proof.
  intros. rewrite map_keys_concat. rewrite map_keys_push.
  destruct (ok_middle_inv H) as [H1 H2]. repeat rewrite* map_keys_notin.
  unfold rename_var. case_if. reflexivity.
Qed.  

Lemma map_other_keys: forall x y z (G:ctx),
  z <> y ->
  z # G ->
  z # map_keys (rename_var x y) G.
Proof.
  intros. induction G using env_ind.
  rewrite map_keys_empty. assumption.
  rewrite map_keys_push. simpl_dom. rewrite notin_union. split.
  unfold rename_var. case_if*. auto.
Qed.

Lemma rename_ctx_other_var: forall x y z T (G: ctx),
    x <> z -> rename_ctx x y G & z ~ subst_typ x y T = rename_ctx x y (G & z ~ T).
Proof.
  intros. unfold rename_ctx. unfold subst_ctx. rewrite map_keys_concat.
  replace (map_keys (rename_var x y) (z ~ T)) with (z ~ T). 
  - rewrite map_push. reflexivity.
  - rewrite* map_keys_notin.
Qed.

Lemma renaming_gen: forall x y,
  (forall m1 G t T, ty_trm m1 G t T ->
    ok G ->
    m1 = ty_general ->
    y # G ->
    ty_trm m1 (rename_ctx x y G) (subst_trm x y t) (subst_typ x y T)) /\
  (forall G z U d D, ty_def G z U d D ->
    ok (G & z ~ U) ->
    y # (G & z ~ U) ->
    ty_def (rename_ctx x y G) (rename_var x y z) (subst_typ x y U) 
          (subst_def x y d) (subst_dec x y D)) /\
  (forall G z U ds T, ty_defs G z U ds T ->
    ok (G & z ~ U) ->
    y # (G & z ~ U) ->
    ty_defs (rename_ctx x y G) (rename_var x y z) (subst_typ x y U) 
          (subst_defs x y ds) (subst_typ x y T)) /\
  (forall G p, norm G p ->
    ok G ->
    y # G ->
    norm (rename_ctx x y G) (subst_path x y p)) /\
  (forall m1 G T U, subtyp m1 G T U ->
    ok G ->
    m1 = ty_general ->
    y # G ->
    subtyp m1 (rename_ctx x y G) (subst_typ x y T) (subst_typ x y U)).
Proof.
  intros. apply rules_mutind; intros; subst; simpl; try (econstructor; apply* H); eauto.
  - (* ty_var *)
    constructor. unfold rename_ctx. unfold subst_ctx.
    destruct (binds_destruct b) as [G' [G'' HG]]. subst. case_if. rewrite* binds_map_keys.
    apply binds_map. rewrite map_keys_concat. rewrite map_keys_push.
    destruct (ok_middle_inv H) as [Hl Hr].
    assert (x0 <> y) as Hx0y. {
      simpl_dom. repeat rewrite notin_union in H1. destruct H1 as [[_ Hy] _]. auto.
    }
    lets Ho: (map_other_keys Hx0y Hr (x:=x)). unfold rename_var. case_if. apply binds_middle_eq. auto.
  - (* ty_all_intro *)
    apply_fresh ty_all_intro as z. assert (z \notin L) as Lz by auto. specialize (H z Lz). 
    rewrite subst_open_commute_trm in H. rewrite subst_open_commute_typ in H.
    unfold subst_fvar in H. assert (z <> x) as Hzx by auto. case_if. 
    rewrite* rename_ctx_other_var.
  - (* ty_all_elim *)
    rewrite subst_open_commute_typ. apply ty_all_elim with (S:=(subst_typ x y S)); auto.
  - (* ty_new_intro *)
    apply_fresh ty_new_intro as z. assert (Lz: z \notin L) by auto. specialize (H z Lz). 
    rewrite subst_open_commute_typ in H. rewrite subst_open_commute_defs in H.
    unfold rename_var in H. unfold subst_fvar in H. assert (Hzx: z <> x) by auto. 
    case_if. apply* H.
  - (* ty_let *)
    apply_fresh ty_let as z; auto. assert (Lz: z \notin L) by auto. specialize (H0 z Lz). 
    rewrite subst_open_commute_trm in H0. 
    unfold subst_fvar in H0. assert (Hzx: z <> x) by auto. case_if.
    rewrite* rename_ctx_other_var.
  - (* ty_rec_intro *)
    apply ty_rec_intro. simpl in H. rewrite subst_open_commute_typ in H. unfold subst_fvar in H. apply* H.
  - (* ty_rec_elim. *) 
    rewrite subst_open_commute_typ_p. apply ty_rec_elim. unfold subst_typ in H.
    apply* H.
  - (* ty_sub *)
    apply ty_sub with (T:=(subst_typ x y T)); auto.
    + intros. inversion H2.
  - (* ty_def_trm *)
    apply ty_def_trm. 
    replace (rename_ctx x y G & rename_var x y x0 ~ subst_typ x y U) with (rename_ctx x y (G & x0 ~ U)).
    + apply* H.
    + unfold rename_ctx. rewrite map_keys_concat. rewrite map_keys_single. 
      unfold subst_ctx. apply map_push.
  - (* ty_def val *)
    apply ty_def_val.
     replace (rename_ctx x y G & rename_var x y x0 ~ subst_typ x y U) with (rename_ctx x y (G & x0 ~ U)).
    + apply* H.
    + unfold rename_ctx. rewrite map_keys_concat. rewrite map_keys_single. 
      unfold subst_ctx. apply map_push.
  - (* ty_defs_cons *)
    apply* ty_defs_cons. apply subst_defs_hasnt. rewrite <- subst_label_of_def. assumption.
  - (* norm_var *)
    apply norm_var with (T:=(subst_typ x y T)). unfold rename_ctx. unfold subst_ctx. 
    apply binds_map. destruct (binds_destruct b) as [G' [G'' HG]]. subst.
    destruct (ok_middle_inv H) as [Hl Hr]. case_if. 
    + rewrite* binds_map_keys.
    + repeat rewrite map_keys_concat. rewrite map_keys_single. 
      replace (rename_var x y x0) with x0.
      * apply binds_middle_eq. apply* map_other_keys. 
        simpl_dom. repeat rewrite notin_union in H0. destruct* H0 as [[_ Hy] _]. 
      * unfold rename_var. case_if*.
  - (* norm_path *)
    eapply norm_path; eauto. apply* H.
  - (* subtyp_sel2 *)
    apply subtyp_sel2 with (T:=(subst_typ x y T)); auto. 
  - (* subtyp_sel1 *)
    apply subtyp_sel1 with (S:=(subst_typ x y S)); auto.
  - (* subtyp_all *)
    apply_fresh subtyp_all as z; auto. specialize (H0 z). assert (Hzx: z <> x) by auto.
    rewrite rename_ctx_other_var; auto. repeat rewrite subst_open_commute_typ in H0. 
    unfold subst_fvar in H0. case_if. apply* H0. 
Qed.

Lemma renaming_def: forall G z U ds T y,
  ty_defs G z U ds T ->
  ok (G & z ~ U) ->
  y # (G & z ~ U) ->
  z \notin fv_ctx_types G ->
  ty_defs G y (subst_typ z y U) (subst_defs z y ds) (subst_typ z y T).
Proof.
  introv Hds Hok Hy Hz.
  assert (HG: G = subst_ctx z y G) by (rewrite (subst_fresh_ctx y G Hz); reflexivity).
  destruct (ok_push_inv Hok) as [_ Hn].
  assert (HG': G = (map_keys (rename_var z y) G)) by rewrite* map_keys_notin.
  assert (Hrg: G = rename_ctx z y G). {
    unfold rename_ctx. rewrite <- HG'. assumption.
  }    
  lets Hr: (proj53 (renaming_gen z y)). specialize (Hr G z U ds T Hds Hok Hy).
  rewrite Hrg. 
  assert (Hyz: y = (rename_var z y z)). {
    unfold rename_var. case_if. reflexivity.
  }
   rewrite <- Hyz in Hr. assumption.
Qed.

(* ###################################################################### *)
(** ** Some Lemmas *)

Lemma corresponding_types: forall G s x T,
  wf_sto G s ->
  binds x T G ->
  ((exists S U t, binds x (val_lambda S t) s /\
                  ty_trm ty_precise G (trm_val (val_lambda S t)) (typ_all S U) /\
                  T = typ_all S U) \/
   (exists S ds, binds x (val_new S ds) s /\
                 ty_trm ty_precise G (trm_val (val_new S ds)) (typ_bnd S) /\
                 T = typ_bnd S)).
Proof.
  introv H Bi. induction H.
  - false* binds_empty_inv.
  - unfolds binds. rewrite get_push in *. case_if.
    + inversions Bi. inversion H2; subst.
      * left. exists T0. exists U. exists t.
        split. auto. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        reflexivity.
      * right. exists T0. exists ds.
        split. auto. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        reflexivity.
      * assert (ty_precise = ty_precise) as Hp by reflexivity. destruct (H3 Hp) as [p Hn]. inversion Hn.
    + specialize (IHwf_sto Bi).
      inversion IHwf_sto as [IH | IH].
      * destruct IH as [S [U [t [IH1 [IH2 IH3]]]]].
        left. exists S. exists U. exists t.
        split. assumption. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        assumption.
      * destruct IH as [S [ds [IH1 [IH2 IH3]]]].
        right. exists S. exists ds.
        split. assumption. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        assumption.
Qed.

Lemma unique_rec_subtyping: forall G S T,
  subtyp ty_precise G (typ_bnd S) T ->
  T = typ_bnd S.
Proof.
  introv Hsub.
  remember (typ_bnd S) as T'.
  remember ty_precise as m1.
  induction Hsub; try solve [inversion Heqm1].
  - specialize (IHHsub1 HeqT' Heqm1). subst.
    apply IHHsub2; reflexivity.
  - inversion HeqT'.
  - inversion HeqT'.
Qed.

Lemma unique_all_subtyping: forall G S U T,
  subtyp ty_precise G (typ_all S U) T ->
  T = typ_all S U.
Proof.
  introv Hsub.
  remember (typ_all S U) as T'.
  remember ty_precise as m1.
  induction Hsub; try solve [inversion Heqm1].
  - specialize (IHHsub1 HeqT' Heqm1). subst.
    apply IHHsub2; reflexivity.
  - inversion HeqT'.
  - inversion HeqT'.
Qed.

Lemma unique_lambda_typing: forall G x S U T,
  binds x (typ_all S U) G ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x)))  T ->
  T = typ_all S U.
Proof.
  introv Bi Hty.
  remember (trm_path (p_var (avar_f x)))  as t.
  remember ty_precise as m1.
  remember sub_general as m2.
  induction Hty; try solve [inversion Heqt; inversion Heqm1].
  - inversions Heqt.
    unfold binds in Bi. unfold binds in H.
    rewrite H in Bi. inversion Bi.
    reflexivity.
  - specialize (IHHty Bi Heqt Heqm1).
    inversion IHHty. 
  - specialize (IHHty Bi Heqt Heqm1). destruct (H Heqm1).
    rewrite IHHty in H0. rewrite Heqm1 in H0.
    apply unique_all_subtyping in H0. apply H0.
Qed.

Lemma lambda_not_rcd: forall G x S U A T,
  binds x (typ_all S U) G ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x)))  (typ_rcd (dec_typ A T T)) ->
  False.
Proof.
  introv Bi Hty.
  assert (typ_rcd (dec_typ A T T) = typ_all S U) as Contra. {
    eapply unique_lambda_typing; eassumption.
  }
  inversion Contra.
Qed.

Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a m T, record_dec (dec_trm a m T)
.

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
  record_typ (typ_and T (typ_rcd D)) (union ls \{l})
.

Definition record_type T := exists ls, record_typ T ls.

Lemma open_dec_preserves_label: forall D x i,
  label_of_dec D = label_of_dec (open_rec_dec i x D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

Lemma open_dec_preserves_label_p: forall D x i,
  label_of_dec D = label_of_dec (open_rec_dec_p i x D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open_dec x D).
Proof.
  intros. inversion H; unfold open_dec; simpl; constructor.
Qed.

Lemma open_record_dec_p: forall D x,
  record_dec D -> record_dec (open_dec_p x D).
Proof.
  intros. inversion H; unfold open_dec_p; simpl; constructor.
Qed.

Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (open_typ x T) ls.
Proof.
  intros. induction H.
  - unfold open_typ. simpl.
    apply rt_one.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
  - unfold open_typ. simpl.
    apply rt_cons; try assumption.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
Qed.

Lemma open_record_typ_p: forall T p ls,
  record_typ T ls -> record_typ (open_typ_p p T) ls.
Proof.
  intros. induction H.
  - unfold open_typ_p. simpl.
    apply rt_one.
    apply open_record_dec_p. assumption.
    rewrite <- open_dec_preserves_label_p. assumption.
  - unfold open_typ_p. simpl.
    apply rt_cons; try assumption.
    apply open_record_dec_p. assumption.
    rewrite <- open_dec_preserves_label_p. assumption.
Qed.

Lemma open_eq_avar: forall x i a1 a2,
  x \notin fv_avar a1 -> x \notin fv_avar a2 ->
  open_rec_avar i x a1 = open_rec_avar i x a2 ->
  a1 = a2.
Proof.
  introv Fr1 Fr2 H. induction a1; induction a2; simpl in H; inversion H.
  - case_if; case_if.
    + reflexivity.
    + inversion H. subst. reflexivity.
  - case_if.
    inversion H. subst. false.
    apply notin_same in Fr2. assumption.
  - case_if.
    inversion H. subst. false.
    apply notin_same in Fr1. assumption.
  - subst. reflexivity.
Qed.

Lemma open_eq_typ_dec_path: forall x,
  (forall T1, x \notin fv_typ T1 ->
   forall T2, x \notin fv_typ T2 ->
   forall i, open_rec_typ i x T1 = open_rec_typ i x T2 ->
   T1 = T2) /\
  (forall D1, x \notin fv_dec D1 ->
   forall D2, x \notin fv_dec D2 ->
   forall i, open_rec_dec i x D1 = open_rec_dec i x D2 ->
   D1 = D2) /\ 
  (forall P1, x \notin fv_path P1 -> 
   forall P2, x \notin fv_path P2 ->
   forall i, open_rec_path i x P1 = open_rec_path i x P2 ->
   P1 = P2).
Proof.
  intros. apply typ_mutind; intros.
  - simpl in H1. induction T2; simpl in H1; inversion H1.
    reflexivity.
  - simpl in H1. induction T2; simpl in H1; inversion H1.
    reflexivity.
  - simpl in H2. induction T2; simpl in H2; inversion H2.
    f_equal. eapply H; eauto.
  - simpl in H3; induction T2; simpl in H3; inversion H3.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
  - simpl in H2. induction T2; simpl in H2; inversion H2.
    f_equal.
    eapply H; eauto.
  - simpl in H2. induction T2; simpl in H2; inversion H2. 
    f_equal. eapply H; eauto.
  - simpl in H1. induction T2; inversion H3.
    f_equal.
    + eapply H; eauto using notin_union_r1.
    + eapply H0; eauto using notin_union_r2.
  - simpl in H3. induction D2; simpl in H3; inversion H3.
    subst.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
  - simpl in H2. induction D2; simpl in H2; inversion H2.
    subst.
    f_equal.
    eapply H; eauto.
  - simpl in H1. induction P2; simpl in H1; inversion H1. 
    f_equal. eauto using open_eq_avar.
  - simpl in H2. induction P2; simpl in H2; inversion H2.
    f_equal. eapply H; eauto.
Qed.

Lemma open_eq_typ: forall x i T1 T2,
  x \notin fv_typ T1 -> x \notin fv_typ T2 ->
  open_rec_typ i x T1 = open_rec_typ i x T2 ->
  T1 = T2.
Proof.
  introv Fr1 Fr2 Heq.
  destruct (open_eq_typ_dec_path x) as [HT HD HP].
  eapply HT; eauto.
Qed.

Lemma open_record_dec_rev: forall D x,
  x \notin fv_dec D ->
  record_dec (open_dec x D) -> record_dec D.
Proof.
  introv Fr H. remember (open_dec x D) as DX.
  generalize dependent D.
  inversion H; intros.
  - destruct D; unfold open_dec in HeqDX; simpl in HeqDX; inversion HeqDX.
    assert (t0 = t1) as Heq. {
      eapply open_eq_typ; eauto using notin_union_r1, notin_union_r2.
    }
    subst. constructor.
  - destruct D; unfold open_dec in HeqDX; simpl in HeqDX; inversion HeqDX.
    subst. constructor.
Qed.

Lemma open_record_typ_rev: forall T x ls,
   x \notin fv_typ T ->
  record_typ (open_typ x T) ls -> record_typ T ls.
Proof.
  introv Fr H. remember (open_typ x T) as TX.
  generalize dependent T.
  induction H; intros.
  - destruct T; unfold open_typ in HeqTX; simpl in HeqTX; inversion HeqTX.
    subst.
    rewrite <- open_dec_preserves_label.
    apply rt_one; eauto.
    eapply open_record_dec_rev; eauto.
  - destruct T0; unfold open_typ in HeqTX; simpl in HeqTX; inversion HeqTX.
    subst.
    destruct T0_2; unfold open_typ in H5; simpl in H5; inversion H5.
    subst.
    rewrite <- open_dec_preserves_label.
    apply rt_cons; try assumption.
    eapply IHrecord_typ; eauto using notin_union_r1.
    eapply open_record_dec_rev; eauto using notin_union_r2.
    eauto.
    rewrite <- open_dec_preserves_label in H2. apply H2.
Qed.

Lemma open_record_type: forall T x,
  record_type T -> record_type (open_typ x T).
Proof.
  intros. destruct H as [ls H]. exists ls. eapply open_record_typ.
  eassumption.
Qed.

Lemma open_record_type_p: forall T p,
  record_type T -> record_type (open_typ_p p T).
Proof.
  intros. destruct H as [ls H]. exists ls. eapply open_record_typ_p.
  eassumption.
Qed.

Lemma open_record_type_rev: forall T x,
  x \notin fv_typ T ->
  record_type (open_typ x T) -> record_type T.
Proof.
  introv Fr H. destruct H as [ls H]. exists ls. eapply open_record_typ_rev; eauto.
Qed.

Lemma label_same_typing: forall G d z U D,
  ty_def  G z U d D -> label_of_def d = label_of_dec D.
Proof.
  intros. inversion H; subst; simpl; reflexivity.
Qed.

Lemma open_var_eq_p_typ_dec_path: forall x,
    (forall T : typ, forall n : nat,
          open_rec_typ n x T = open_rec_typ_p n (p_var (avar_f x)) T) /\
    (forall D : dec, forall n : nat,
          open_rec_dec n x D = open_rec_dec_p n (p_var (avar_f x)) D) /\
    (forall P : path, forall n : nat,
          open_rec_path n x P = open_rec_path_p n (p_var (avar_f x)) P).
Proof.
  intros. apply typ_mutind; unfold open_typ, open_typ_p; simpl; intros; auto. 
  - (* typ_rcd *)
    f_equal*. 
  - (* typ_and *)
    rewrite H. rewrite* H0.
  - (* typ_path *)
    rewrite* H.
  - (* typ_bnd *)
    f_equal*. 
  - (* typ_all *)
    rewrite H. rewrite* H0.
  - (* dec_typ *)
    rewrite H. rewrite* H0. 
  - (* dec_trm *)
    rewrite* H.
  - (* p_var *)
    unfold open_rec_avar, open_rec_avar_p. destruct a; simpl. case_if*. f_equal*. 
  - (* p_sel *)
    rewrite* H.
Qed.
      
Lemma open_var_path_typ_eq: forall x T,
  open_typ x T = open_typ_p (p_var (avar_f x)) T.
Proof.
  intros. apply open_var_eq_p_typ_dec_path.
Qed.
    
Lemma record_defs_typing_rec: forall G ds S z U,
  ty_defs  G z U ds S ->
  exists ls, record_typ S ls /\ forall l, l \notin ls <-> defs_hasnt ds l.
Proof.
  intros. induction H.
  - eexists. split.
    apply rt_one.
    inversion H; subst; constructor.
    reflexivity.
    apply label_same_typing in H. rewrite <- H.
    intros. split; intro A.
    + unfold defs_hasnt. simpl.
      apply notin_singleton in A.
      rewrite If_r. reflexivity. eauto.
    + unfold defs_hasnt in A. unfold get_def in A.
      case_if. apply notin_singleton. eauto.
  - destruct IHty_defs as [ls [IH1 IH2]].
    eexists. split.
    apply rt_cons; try eassumption.
    inversion H0; subst; constructor.
    reflexivity.
    apply label_same_typing in H0. rewrite <- H0.
    specialize (IH2 (label_of_def d)).
    destruct IH2 as [IH2A IH2B].
    apply IH2B. assumption.
    intros. split; intro A.
    + specialize (IH2 l).
      destruct IH2 as [IH2A IH2B].
      unfold defs_hasnt. simpl.
      rewrite If_r. unfold defs_hasnt in IH2A. apply IH2A.
      apply notin_union in A. destruct A as [A1 A2]. assumption.
      apply notin_union in A. destruct A as [A1 A2]. apply notin_singleton in A2.
      apply label_same_typing in H0. rewrite <- H0 in A2. eauto.
    + apply notin_union. split.
      * specialize (IH2 l).
        destruct IH2 as [IH2A IH2B].
        apply IH2B. inversion A.
        case_if. unfold defs_hasnt. assumption.
      * apply label_same_typing in H0. rewrite <- H0.
        unfold defs_hasnt in A. unfold get_def in A.
        case_if in A.
        apply notin_singleton. eauto.
Qed.

Lemma record_defs_typing: forall G ds z U S,
  ty_defs  G z U ds S ->
  record_type S.
Proof.
  intros.
  assert (exists ls, record_typ S ls /\ forall l, l \notin ls <-> defs_hasnt ds l) as A.
  eapply record_defs_typing_rec; eauto.
  destruct A as [ls [A1 A2]].
  exists ls. apply A1.
Qed.

Lemma record_new_typing: forall G S ds,
  ty_trm ty_precise G (trm_val (val_new S ds)) (typ_bnd S) ->
  record_type S.
Proof.
  intros.
  inversion H; subst.
  + pick_fresh x.
    apply open_record_type_rev with (x:=x).
    eauto.
    eapply record_defs_typing. eapply H3. eauto.
  + assert (ty_precise = ty_precise) as Hp by reflexivity. destruct (H0 Hp). inversion H3.
Qed.

Inductive record_sub : typ -> typ -> Prop :=
| rs_refl: forall T,
  record_sub T T
| rs_dropl: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) (typ_rcd D)
| rs_drop: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) T'
| rs_pick: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) (typ_and T' (typ_rcd D))
.

Lemma record_typ_sub_closed : forall T T' ls,
  record_sub T T' ->
  record_typ T ls ->
  exists ls', record_typ T' ls' /\ subset ls' ls.
Proof.
  introv Hsub Htyp. generalize dependent ls.
  induction Hsub; intros.
  - exists ls. split. assumption. apply subset_refl.
  - inversion Htyp; subst.
    eexists. split.
    eapply rt_one. assumption. reflexivity.
    rewrite <- union_empty_l with (E:=\{ label_of_dec D}) at 1.
    apply subset_union_2. apply subset_empty_l. apply subset_refl.
  - inversion Htyp; subst.
    specialize (IHHsub ls0 H1). destruct IHHsub as [ls' [IH1 IH2]].
    exists ls'. split. assumption.
    rewrite <- union_empty_r with (E:=ls').
    apply subset_union_2. assumption. apply subset_empty_l.
  - inversion Htyp; subst.
    specialize (IHHsub ls0 H1). destruct IHHsub as [ls0' [IH1 IH2]].
    exists (ls0' \u \{ label_of_dec D }). split.
    apply rt_cons; eauto.
    unfold "\c" in IH2. unfold "\notin". intro I.
    specialize (IH2 (label_of_dec D) I). eauto.
    apply subset_union_2. assumption. apply subset_refl.
Qed.

Lemma record_type_sub_closed : forall T T',
  record_sub T T' ->
  record_type T ->
  record_type T'.
Proof.
  introv Hsub Htype. destruct Htype as [ls Htyp].
  apply record_typ_sub_closed with (ls:=ls) in Hsub; try assumption.
  destruct Hsub as [ls' [Htyp' ?]].
  exists ls'. apply Htyp'.
Qed.

Lemma record_sub_trans: forall T1 T2 T3,
  record_sub T1 T2 ->
  record_sub T2 T3 ->
  record_sub T1 T3.
Proof.
  introv H12 H23. generalize dependent T3.
  induction H12; intros.
  - assumption.
  - inversion H23; subst. eapply rs_dropl. eassumption.
  - apply rs_drop. apply IHrecord_sub. assumption.
  - inversion H23; subst.
    + apply rs_pick. assumption.
    + eapply rs_dropl. eassumption.
    + apply rs_drop. apply IHrecord_sub. assumption.
    + apply rs_pick. apply IHrecord_sub. assumption.
Qed.

Lemma record_subtyping: forall G T T',
  subtyp ty_precise G T T' ->
  record_type T ->
  record_sub T T'.
Proof.
  introv Hsub Hr. generalize dependent Hr. dependent induction Hsub.
  - intros HS.
    apply record_sub_trans with (T2:=T).
    apply IHHsub1. apply HS.
    apply IHHsub2.
    eapply record_type_sub_closed. apply IHHsub1. apply HS. apply HS.
  - intros Htype. destruct Htype as [ls Htyp].
    inversion Htyp; subst.
    apply rs_drop. apply rs_refl.
  - intros Htype. destruct Htype as [ls Htyp].
    inversion Htyp; subst.
    eapply rs_dropl. apply rs_refl.
Qed.

Lemma record_typ_sub_label_in: forall T D ls,
  record_typ T ls ->
  record_sub T (typ_rcd D) ->
  label_of_dec D \in ls.
Proof.
  introv Htyp Hsub. generalize dependent D. induction Htyp; intros.
  - inversion Hsub. subst. apply in_singleton_self.
  - inversion Hsub; subst.
    + rewrite in_union. right. apply in_singleton_self.
    + rewrite in_union. left. apply IHHtyp. assumption.
Qed.

Lemma unique_rcd_typ: forall T A T1 T2,
  record_type T ->
  record_sub T (typ_rcd (dec_typ A T1 T1)) ->
  record_sub T (typ_rcd (dec_typ A T2 T2)) ->
  T1 = T2.
Proof.
  introv Htype Hsub1 Hsub2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Hsub1; inversion Hsub2; subst.
  - inversion H5. subst. reflexivity.
  - inversion H9. subst. reflexivity.
  - apply record_typ_sub_label_in with (D:=dec_typ A T2 T2) in Htyp.
    simpl in Htyp. simpl in H1. unfold "\notin" in H1. unfold not in H1.
    specialize (H1 Htyp). inversion H1.
    assumption.
  - apply record_typ_sub_label_in with (D:=dec_typ A T1 T1) in Htyp.
    simpl in Htyp. simpl in H1. unfold "\notin" in H1. unfold not in H1.
    specialize (H1 Htyp). inversion H1.
    assumption.
  - eapply IHHtyp; eassumption.
Qed.

Lemma record_type_sub_not_rec: forall S T p,
  record_sub (open_typ_p p S) (typ_bnd T) ->
  record_type S ->
  False.
Proof.
  introv Hsub Htype. remember (open_typ_p p S) as Sx.
  apply open_record_type_p with (p:=p) in Htype.
  rewrite <- HeqSx in Htype. clear HeqSx.
  destruct Htype as [ls Htyp]. induction Htyp.
  - inversion Hsub.
  - inversion Hsub; subst. apply IHHtyp. assumption.
Qed.

Lemma shape_new_typing: forall G x S T,
  binds x (typ_bnd S) G ->
  record_type S ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x))) T ->
  T = typ_bnd S \/ record_sub (open_typ x S) T.
Proof.
  introv Bi HS Hx. dependent induction Hx.
  - unfold binds in H. unfold binds in Bi. rewrite H in Bi. inversion Bi.
    left. reflexivity.
  - assert (typ_bnd T = typ_bnd S \/ record_sub (open_typ x S) (typ_bnd T)) as A. {
      eapply IHHx; eauto.
    }
    destruct A as [A | A].
    + inversion A. right. rewrite open_var_path_typ_eq.
      apply rs_refl.
    + rewrite open_var_path_typ_eq in A.
    apply record_type_sub_not_rec in A. inversion A. assumption.
  - assert (T = typ_bnd S \/ record_sub (open_typ x S) T) as A. {
      eapply IHHx; eauto.
    }
    destruct A as [A | A].
    + subst. left. apply (unique_rec_subtyping H0).
    + right. eapply record_sub_trans. eassumption. apply (record_subtyping H0).
      apply (record_type_sub_closed A). apply open_record_type. assumption.
Qed.

Lemma sto_binds_to_ctx_binds: forall G s x v,
  wf_sto G s -> binds x v s -> exists S, binds x S G.
Proof.
  introv Hwf Bis.
  remember Hwf as Hwf'. clear HeqHwf'.
  apply sto_binds_to_ctx_binds_raw with (x:=x) (v:=v) in Hwf.
  destruct Hwf as [G1 [G2 [T [EqG Hty]]]].
  subst.
  exists T.
  eapply binds_middle_eq. apply wf_sto_to_ok_G in Hwf'.
  apply ok_middle_inv in Hwf'. destruct Hwf'. assumption.
  assumption.
Qed.

Lemma val_new_typing: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  ty_trm ty_precise G (trm_val (val_new T ds)) (typ_bnd T).
Proof.
  introv Hwf Bis.
  assert (exists T, binds x T G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [T0 Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [S [U [t [Bis' [Ht EqT]]]]].
    false.
  - destruct H as [T' [ds' [Bis' [Ht EqT]]]]. subst.
    unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis.
    inversion Bis. subst.
    assumption.
Qed.

Lemma wf_sto_val_new_in_G: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  binds x (typ_bnd T) G.
Proof.
  introv Hwf Bis.
  assert (exists S, binds x S G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [S Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [? [? [? [Bis' _]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis in Bis'. inversion Bis'.
  - destruct H as [T' [ds' [Bis' [Hty Heq]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
    assumption.
Qed.

Lemma var_new_typing: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x)))  (open_typ x T).
Proof.
  intros.
  rewrite open_var_path_typ_eq.
  apply ty_rec_elim. apply ty_var. eapply wf_sto_val_new_in_G; eauto.
Qed.

Lemma wf_sto_sub: forall G G' G'' s s' s'' x T v,
  wf_sto G s ->
  G = G' & x ~ T & G'' ->
  s = s' & x ~ v & s'' ->
  wf_sto (G' & x ~ T) (s' & x ~ v).
Proof.
  introv Hwf HG Hs. gen G G' s s' s''.
  induction G'' using env_ind; intros G G' HG s Hwf s' s'' Hs; destruct s'' using env_ind.
  - rewrite concat_empty_r in *. subst. assumption.
  - rewrite concat_assoc in Hs. subst. rewrite concat_empty_r in Hwf.
    assert (x <> x0) as Hxn. {
      lets Hok: (wf_sto_to_ok_s Hwf). destruct (ok_push_inv Hok) as [_ Hn].
      simpl_dom. auto.
    }
    inversion Hwf. false* empty_push_inv.
    destruct (eq_push_inv H0) as [Hx _]. destruct (eq_push_inv H) as [Hx' _]. subst. subst.
    false* Hxn.
  - rewrite concat_assoc in HG. subst. rewrite concat_empty_r in Hwf.
    assert (x <> x0) as Hxn. {
      lets Hok: (wf_sto_to_ok_G Hwf). destruct (ok_push_inv Hok) as [_ Hn].
      simpl_dom. auto.
    }
    inversion Hwf. false* empty_push_inv.
    destruct (eq_push_inv H0) as [Hx _]. destruct (eq_push_inv H) as [Hx' _]. subst. subst.
    false* Hxn.
  - assert (G' & x ~ T & G'' = G' & x ~ T & G'') as Hobv by reflexivity.
    assert (wf_sto (G' & x ~ T & G'') (s' & x ~ v & s'')) as Hwf'. {
      subst. inversion Hwf.
      * false* empty_middle_inv.
      * rewrite concat_assoc in *.
        destruct (eq_push_inv H) as [Hx [Ht Hg]]. destruct (eq_push_inv H0) as [Hx' [Hv Hs']]. 
        subst. subst. assumption.
    }
    assert (s' & x ~ v & s'' = s' & x ~ v & s'') as Hobv' by reflexivity.
    specialize (IHG'' (G' & x ~ T & G'') G' Hobv (s' & x ~ v & s'') Hwf' s' s'' Hobv').
    apply IHG''.
Qed.

Lemma wf_sto_new_typing: forall G s x T ds,
  wf_sto (G & x ~ (typ_bnd T)) (s & x ~ (val_new T ds)) ->
  ty_trm ty_precise G (trm_val (val_new T ds)) (typ_bnd T).
Proof.
  introv Hwf. inversion Hwf.
  - false* empty_push_inv.
  - destruct (eq_push_inv H) as [Hx [HT HG]]. destruct (eq_push_inv H0) as [Hx' [Hv Hs]]. subst.
    assumption.
Qed.

Lemma new_ty_defs: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  exists G' G'',
    G = G' & x ~ (typ_bnd T) & G'' /\
    ty_defs G' x (open_typ x T) (open_defs x ds) (open_typ x T).
Proof.
  introv Hwf Bis.
  assert (exists s' s'', s = s' & x ~ (val_new T ds) & s'') as Hs by (apply* (binds_destruct Bis)).
  destruct Hs as [s' [s'' Hs]].
  lets Bis': (binds_push_eq x (val_new T ds) s').
  destruct (sto_binds_to_ctx_binds_raw Hwf Bis) as [G' [G'' [T0 [HG _]]]].
  exists G' G''.

  assert (T0 = typ_bnd T) as Ht. {
    lets Hb: (wf_sto_val_new_in_G Hwf Bis).
    apply wf_sto_to_ok_G in Hwf. rewrite HG in Hwf.
    assert (x # G'') as Hx by (apply* ok_middle_inv_r).
    assert (binds x T0 (G' & x ~ T0 & G'')) as Hxt by (apply* binds_middle_eq).
    rewrite <- HG in Hxt. apply (binds_func Hxt Hb).
  }
  subst T0. split. assumption.
  lets Hwf': (wf_sto_sub Hwf HG Hs).
  lets Hn: (wf_sto_new_typing Hwf').
  inversion Hn; subst. 
  - pick_fresh y. lets Hok': (wf_sto_to_ok_G Hwf'). 
    rewrite subst_intro_typ with (x:=y). rewrite subst_intro_defs with (x:=y).
    apply* renaming_def. auto. auto.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H as [? Contra]. inversion Contra.
Qed.

Lemma record_has_sub: forall T D G,
  record_has T D ->
  T = typ_rcd D \/ subtyp ty_precise G T (typ_rcd D).
Proof.
  introv Hr. dependent induction Hr; auto.
  destruct IHHr as [IHHr | IHHr]; right.
  - subst. auto.
  - apply subtyp_trans with (T:=T); auto.
Qed.

Lemma precise_to_general:
  (forall m1 G t T,
     ty_trm m1 G t T ->
     m1 = ty_precise ->
     ty_trm ty_general G t T) /\
  (forall m1 G S U,
     subtyp m1 G S U ->
     m1 = ty_precise ->
     subtyp ty_general G S U).
Proof.
  apply ts_mutind; intros; subst; eauto.
Qed.

Lemma precise_to_general_subtyping: forall G S U,
  subtyp ty_precise G S U ->
  subtyp ty_general G S U.
Proof.
  intros. apply* precise_to_general.
Qed.

Lemma record_has_open: forall x T D,
  record_has T D -> record_has (open_typ x T) (open_dec x D).
Proof.
  introv H. gen D. induction T; intros; inversion H; subst; unfold open_typ; simpl; constructor. 
  apply* IHT1.
Qed.

Lemma unique_tight_bounds: forall G s x T1 T2 A,
  wf_sto G s ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A T1 T1)) ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A T2 T2)) ->
  T1 = T2.
Proof.
  introv Hwf Hty1 Hty2.
  assert (exists T, binds x T G) as Bi. {
    eapply typing_implies_bound. eassumption.
  }
  destruct Bi as [T Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [S [U [t [Bis [Ht EqT]]]]].
    false.
    eapply lambda_not_rcd.
    subst. eassumption. eassumption.
  - destruct H as [S [ds [Bis [Ht EqT]]]]. subst.
    assert (record_type S) as Htype. {
      eapply record_new_typing. eassumption.
    }
    destruct (shape_new_typing Bi Htype Hty1) as [Contra1 | A1].
    inversion Contra1.
    destruct (shape_new_typing Bi Htype Hty2) as [Contra2 | A2].
    inversion Contra2.
    assert (record_type (open_typ x S)) as HXtype. {
      apply open_record_type. assumption.
    }
    eapply unique_rcd_typ.
    apply HXtype.
    eassumption.
    eassumption.
Qed.

(* ###################################################################### *)
(** ** Precise flow *)
(* Ifaz's precise flow lemmas, adjusted to paths *)

(*
Definition (Precise flow of a variable)

For a variable x, environment G, type T, the set Pf(x,G,T) is the set of all
precise types that x can have if G(x)=T. More "precisely":

If G(x)=T, then T is in Pf(x,G,T).
If rec(x:U) is in Pf(x,G,T), then U is in Pf(x,G,T).
If (U1 & U2) is in Pf(x,G,T), then U1 is in Pf(x,G,T).
If (U1 & U2) is in Pf(x,G,T), then U2 is in Pf(x,G,T).

*)
Inductive precise_flow : var -> ctx -> typ -> typ -> Prop :=
  | pf_bind : forall x G T,
      binds x T G ->
      precise_flow x G T T
  | pf_open : forall x G T U,
      precise_flow x G T (typ_bnd U) ->
      precise_flow x G T (open_typ x U)
  | pf_and1 : forall x G T U1 U2,
      precise_flow x G T (typ_and U1 U2) ->
      precise_flow x G T U1
  | pf_and2 : forall x G T U1 U2,
      precise_flow x G T (typ_and U1 U2) ->
      precise_flow x G T U2
.

Hint Constructors precise_flow.

Lemma precise_flow_lemma : forall T U G x,
    binds x T G ->
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) U ->
    precise_flow x G T U.
Proof.
  introv Bis Htyp.
  dependent induction Htyp.
  - rewrite (binds_func H Bis).
    constructor. assumption.
  - assert (H : precise_flow x G T (typ_bnd T0)).
    { apply IHHtyp; auto. }
    rewrite <- open_var_path_typ_eq. auto.
  - rename H into H1.
    assert (H : precise_flow x G T T0).
    { apply IHHtyp; auto. }
    dependent induction H0.
    + apply IHsubtyp2; auto.
      * apply ty_sub with S; auto.
      * intros. rewrite <- H0.
        inversion H2.
        rewrite <- H4.
        apply IHsubtyp1; auto.
    + econstructor; eauto.
    + apply pf_and2 with T0; auto.
Qed.

Lemma precise_flow_lemma' : forall U G x,
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) U ->
    exists T, precise_flow x G T U.
Proof.
  introv H.
  pose proof (typing_implies_bound H) as [T H1].
  exists T. apply precise_flow_lemma; auto.
Qed.

Lemma precise_flow_implies_bound : forall T U G x,
    precise_flow x G T U ->
    binds x T G.
Proof.
  introv H. induction H; auto.
Qed.

Lemma precise_flow_lemma'' : forall U G x,
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) U ->
    exists T, binds x T G /\ precise_flow x G T U.
Proof.
  introv H.
  pose proof (precise_flow_lemma' H) as [T Hpf].
  pose proof (precise_flow_implies_bound Hpf) as Bis.
  exists T. auto.
Qed.

Lemma precise_flow_lemma_rev : forall T U G x,
    precise_flow x G T U ->
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) U.
Proof.
  introv H.
  pose proof (precise_flow_implies_bound H) as H1.
  induction H.
  - auto.
  - rewrite open_var_path_typ_eq. auto.
  - pose proof (IHprecise_flow H1) as H2.
    eapply ty_sub.
    + intros H3. exists (p_var (avar_f x)). reflexivity.
    + eauto.
    + eauto.
  - pose proof (IHprecise_flow H1) as H2.
    eapply ty_sub.
    + intros H3. exists (p_var (avar_f x)). reflexivity.
    + eauto.
    + eauto.
Qed.

Lemma ty_precise_var_and_inv1 : forall x G T U,
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_and T U) ->
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) T.
Proof.
  introv H.
  destruct (precise_flow_lemma' H) as [T' Hpf].
  apply pf_and1 in Hpf.
  apply (precise_flow_lemma_rev Hpf).
Qed.

Lemma ty_precise_var_and_inv2 : forall x G T U,
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_and T U) ->
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) U.
Proof.
  introv H.
  destruct (precise_flow_lemma' H) as [T' Hpf].
  apply pf_and2 in Hpf.
  apply (precise_flow_lemma_rev Hpf).
Qed.

Lemma precise_flow_all_inv : forall x G S T U,
    precise_flow x G (typ_all S T) U ->
    U = (typ_all S T).
Proof.
  introv Hpf.
  dependent induction Hpf.
  - reflexivity.
  - inversion IHHpf.
  - inversion IHHpf.
  - inversion IHHpf.
Qed.

Lemma precise_flow_bnd_inv'' : forall x G T,
    record_type T ->
    (forall U, precise_flow x G (typ_bnd T) U ->
          (exists U', U = (typ_bnd U') /\ record_type U') \/ record_type U).
Proof.
  introv [ls Hrt].
  induction Hrt. intros U.
  - intros Hpf.
    dependent induction Hpf.
    + left. exists (typ_rcd D).
      split.
      * reflexivity.
      * exists \{ label_of_dec D}.
        constructor; auto.
    + destruct (IHHpf H) as [[U' [IH1 IH2]] | [ls IH]].
      * inversion IH1. right.
        apply open_record_type. auto.
      * inversion IH.
    + destruct (IHHpf H) as [[U' [IH1 IH2]] | [ls IH]].
      * inversion IH1.
      * inversion IH. right. exists ls0. auto.
    + destruct (IHHpf H) as [[U' [IH1 IH2]] | [ls IH]].
      * inversion IH1.
      * inversion IH. right. exists \{ l}.
        constructor; auto.
  - intros U Hpf.
    dependent induction Hpf.
    + left. exists (typ_and T (typ_rcd D)).
      split.
      * reflexivity.
      * remember (label_of_dec D) as l.
        exists (union ls \{l}).
        apply rt_cons; auto.
    + specialize (IHHpf H1 H T Hrt IHHrt (eq_refl _)).
      destruct IHHpf as [[U' [IH1 IH2]] | [ls' IH]].
      * assert (H2 : U'=U).
        { inversion IH1; auto. }
        rewrite H2 in IH2.
        right. apply open_record_type.
        assumption.
      * inversion IH.
    + specialize (IHHpf H1 H T Hrt IHHrt (eq_refl _)).
      destruct IHHpf as [[U' [IH1 IH2]] | [ls' IH]].
      * inversion IH1.
      * right. inversion IH.
        exists ls0. apply H3.
    + specialize (IHHpf H1 H T Hrt IHHrt (eq_refl _)).
      destruct IHHpf as [[U' [IH1 IH2]] | [ls' IH]].
      * inversion IH1.
      * right. inversion IH.
        exists \{ l}. constructor; auto.
Qed.

Lemma precise_flow_bnd_inv' : forall x G T U,
    record_type T ->
    precise_flow x G (typ_bnd T) (typ_bnd U) ->
    record_type U.
Proof.
  introv Hrt Hpf.
  pose proof (precise_flow_bnd_inv'' Hrt Hpf) as Hbnd.
  destruct Hbnd as [[U' [IH1 IH2]] | [ls contra]]; try solve [inversion contra].
  - inversion IH1. subst; auto.
Qed.

Lemma precise_flow_bnd_inv : forall x G T U,
    record_type T ->
    precise_flow x G (typ_bnd T) (typ_bnd U) ->
    (T = U).
Proof.
  introv Hrt Hpf.
  pose proof (precise_flow_bnd_inv'' Hrt Hpf) as Hbnd.
  dependent induction Hpf.
  - reflexivity.
  - pose proof (precise_flow_bnd_inv' Hrt Hpf).
    pose proof (open_record_type x0 H) as H1.
    rewrite x in H1.
    destruct H1 as [ls H1].
    inversion H1.
  - pose proof (precise_flow_bnd_inv'' Hrt Hpf) as H.
    destruct H as [[U' [H1 H2]] | [ls H]].
    + inversion H1.
    + inversion H.
      inversion H2.
  - pose proof (precise_flow_bnd_inv'' Hrt Hpf) as H.
    destruct H as [[U' [H1 H2]] | [ls H]].
    + inversion H1.
    + inversion H.
Qed.

Lemma record_dec_precise_and_inv : forall x G D T,
    record_dec D ->
    precise_flow x G (typ_bnd (typ_rcd D)) T ->
    (forall T1 T2, T = (typ_and T1 T2) ->
              False).
Proof.
  introv Hrec.
  assert (H: record_type (typ_rcd D)).
  { exists \{ (label_of_dec D)}. constructor; auto. }
  introv Hpf.
  dependent induction Hpf.
  - introv Heq. inversion Heq.
  - pose proof (precise_flow_bnd_inv H Hpf) as H1.
    rewrite <- H1. introv Heq. inversion Heq.
  - specialize (IHHpf Hrec H). false.
  - specialize (IHHpf Hrec H). false.
Qed.

Lemma record_precise_dec_implies_record_dec : forall x G T D,
    record_type T ->
    precise_flow x G (typ_bnd T) (typ_rcd D) ->
    record_dec D.
Proof.
  introv Hrt Hpf.
  pose proof (precise_flow_bnd_inv'' Hrt Hpf) as [[U [Contra H1]] | [ls H1]].
  - inversion Contra.
  - inversion H1. assumption.
Qed.

Lemma record_dec_precise_open : forall x G D1 D2,
    record_dec D1 ->
    precise_flow x G (typ_bnd (typ_rcd D1)) (typ_rcd D2) ->
    open_dec x D1 = D2.
Proof.
  introv Hrec Hpf.
  assert (H: record_type (typ_rcd D1)).
  { exists \{ (label_of_dec D1)}. constructor; auto. }
  dependent induction Hpf.
  - pose proof (precise_flow_bnd_inv H Hpf) as H1.
    rewrite <- H1 in x.
    unfold open_typ in x.
    simpl in x. inversion x.
    unfold open_dec. reflexivity.
  - pose proof (record_dec_precise_and_inv Hrec Hpf) as H1.
    false.
  - pose proof (record_dec_precise_and_inv Hrec Hpf) as H1.
    false.
Qed.

Lemma record_typ_sub_and_inv1 : forall T,
    record_type T ->
    (forall U1 U2, record_sub T (typ_and U1 U2) ->
           record_sub T U1).
Proof.
  intros T [ls Hrt].
  induction Hrt.
  - intros U1 U2 Hrsub.
    inversion Hrsub.
  - intros U1 U2 Hrsub.
    inversion Hrsub.
    + constructor. constructor.
    + apply IHHrt in H5.
      apply rs_drop. auto.
    + apply rs_drop. auto.
Qed.

Lemma record_typ_sub_and_inv2 : forall T,
    record_type T ->
    (forall U1 U2, record_sub T (typ_and U1 U2) ->
           record_sub T U2).
Proof.
  intros T [ls Hrt].
  induction Hrt.
  - intros U1 U2 Hrsub.
    inversion Hrsub.
  - intros U1 U2 Hrsub.
    inversion Hrsub.
    + econstructor. constructor.
    + apply IHHrt in H5.
      apply rs_drop. auto.
    + eapply rs_dropl. eauto.
Qed.

Lemma precise_flow_record_sub : forall x G T,
    record_type T ->
    (forall T', precise_flow x G (typ_bnd T) T' ->
           (T' = typ_bnd T) \/ record_sub (open_typ x T) T').
Proof.
  introv Hrt.
  introv Hpf.
  dependent induction Hpf.
  - left. reflexivity.
  - destruct (IHHpf Hrt) as [IH | IH].
    + inversion IH.
      right. constructor.
    + right. apply (precise_flow_bnd_inv Hrt) in Hpf.
      rewrite Hpf. constructor.
  - destruct (IHHpf Hrt) as [IH | IH].
    + inversion IH.
    + right. eapply record_typ_sub_and_inv1.
      * apply open_record_type. auto.
      * eauto.
  - destruct (IHHpf Hrt) as [IH | IH].
    + inversion IH.
    + right. eapply record_typ_sub_and_inv2.
      * apply open_record_type. auto.
      * eauto.
Qed.

Lemma record_unique_tight_bounds : forall G x T A,
    record_type T ->
    ( forall T1 T2,
        precise_flow x G (typ_bnd T) (typ_rcd (dec_typ A T1 T1)) ->
        precise_flow x G (typ_bnd T) (typ_rcd (dec_typ A T2 T2)) ->
        T1 = T2).
Proof.
  introv Hrt Hpf1 Hpf2.
  pose proof (precise_flow_record_sub Hrt Hpf1) as [H1 | H1].
  inversion H1.
  pose proof (precise_flow_record_sub Hrt Hpf2) as [H2 | H2].
  inversion H2.
  apply open_record_type with (x:=x) in Hrt.
  eapply (unique_rcd_typ Hrt); eauto.
Qed.

(* ###################################################################### *)
(** ** Good types *)
(* Ifaz's and Paul's good-types definitions adjusted to paths *)

(* Definition (Good types)

A type is good if it of the form
  all(x: S)T
  rec(x: T), where T is a record type
 *)

Inductive good_typ : typ -> Prop :=
  | good_typ_all : forall S T, good_typ (typ_all S T) (* all(x: S)T *)
  | good_typ_bnd : forall T,
      (* a record type is ands of record decs *)
      record_type T ->
      good_typ (typ_bnd T). (* rec(x:T) *)

(* Definition (Good context)

A context is good if it is of the form
  {}
  G, x : T where G is a good context and T is a good type *)

Inductive good : ctx -> Prop :=
  | good_empty : good empty
  | good_all : forall pre x T,
      good pre ->
      good_typ T ->
      good (pre & x ~ T).

Lemma wf_good : forall G s, wf_sto G s -> good G.
Proof.
  intros. induction H.
  - apply good_empty.
  - apply good_all.
    + assumption.
    + dependent induction H2.
      * apply good_typ_all.
      * apply good_typ_bnd. pick_fresh z. apply open_record_type_rev with (x:=z); auto.
        apply record_defs_typing with (G:=G) (z:=z) (U:=open_typ z T) (ds:= open_defs z ds); auto. 
      * assert (ty_precise = ty_precise) by reflexivity. apply H4 in H5.
        destruct H5. inversion H5.
Qed.

(* Good contexts bind good:
If G |- x : T and G is a good context then T is a good type. *)

Lemma binds_good : forall G x T,
    binds x T G ->
    good G ->
    good_typ T.
Proof.
  introv Bi Hgood. induction Hgood.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi).
    + destruct H0. subst. assumption.
    + destruct H0. apply (IHHgood H1).
Qed.

Lemma good_binds : forall G x T,
    good G ->
    binds x T G ->
    good_typ T.
Proof.
  introv Bi Hgd.
  eapply binds_good; eauto.
Qed.

Lemma good_typ_bnd_record : forall G x T,
    good G ->
    binds x (typ_bnd T) G ->
    record_type T.
Proof.
  introv Bi Hgd.
  pose proof (good_binds Bi Hgd).
  dependent induction H.
  assumption.
Qed.

Lemma binds_typ_bnd_precise : forall G x T,
    binds x (typ_bnd T) G ->
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_bnd T).
Proof.
  introv Bi.
  auto.
Qed.

Lemma good_binds_bot : forall G x,
    good G ->
    binds x typ_bot G ->
    False.
Proof.
  intros G x Hgd Hbd.
  apply binds_good in Hbd.
  - inversion Hbd.
  - assumption.
Qed.

Lemma good_unique_tight_bounds' : forall G x T T1 T2 A,
    good_typ T ->
    precise_flow x G T (typ_rcd (dec_typ A T1 T1)) ->
    precise_flow x G T (typ_rcd (dec_typ A T2 T2)) ->
    T1 = T2.
Proof.
  introv Hgt Hpf1 Hpf2.
  induction Hgt.
  - apply precise_flow_all_inv in Hpf1.
    inversion Hpf1.
  - apply (record_unique_tight_bounds H Hpf1 Hpf2).
Qed.

Lemma good_unique_tight_bounds: forall G x T1 T2 A,
  good G ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A T1 T1)) ->
  ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A T2 T2)) ->
  T1 = T2.
Proof.
  introv Hgd Hty1 Hty2.
  assert (exists T, binds x T G) as Bi. {
    eapply typing_implies_bound. eassumption.
  }
  destruct Bi as [T Bi].
  pose proof (good_binds Hgd Bi) as Hgt.
  pose proof (precise_flow_lemma Bi Hty1) as H1.
  pose proof (precise_flow_lemma Bi Hty2) as H2.
  apply (good_unique_tight_bounds' Hgt H1 H2).
Qed.

Lemma good_precise_bot : forall T G x,
    good G ->
    binds x T G ->
    precise_flow x G T typ_bot ->
    False.
Proof.
  intros T G x Hgd Bis Hpf.
  pose proof (binds_good Bis Hgd) as Hgtyp.
  induction Hgtyp.
  - apply precise_flow_all_inv in Hpf.
    inversion Hpf.
  - dependent induction Hpf.
    + pose proof (precise_flow_bnd_inv H Hpf) as H1.
      unfold open_typ in x.
      assert (U = typ_bot) as HUb. {
        destruct U; subst; inversion x. reflexivity.
      }
      subst.
      inversion H. inversion H0.
    + pose proof (precise_flow_bnd_inv'' H Hpf) as H1.
      destruct H1 as [[U' [H11 H12]] | [ls H1]]; try false.
      inversion H1. inversion H3.
    + pose proof (precise_flow_bnd_inv'' H Hpf) as H1.
      destruct H1 as [[U' [H11 H12]] | [ls H1]]; try false.
      inversion H1.
Qed.

Lemma good_ty_precise_bot' : forall T G x,
    good G ->
    binds x T G ->
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) typ_bot ->
    False.
Proof.
  intros.
  pose proof (precise_flow_lemma H0 H1) as H2.
  eapply good_precise_bot; eauto.
Qed.

Lemma good_ty_precise_bot : forall G x,
    good G ->
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) typ_bot ->
    False.
Proof.
  intros.
  pose proof (typing_implies_bound H0) as [T HT].
  apply (good_ty_precise_bot' H HT H0).
Qed.

Lemma good_precise_sel_inv : forall G x p A,
    good G ->
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_path p A) ->
    False.
Proof.
  introv Hgd Hpt.
  pose proof (typing_implies_bound Hpt) as [T Bis].
  pose proof (good_binds Hgd Bis) as Hgt.
  pose proof (precise_flow_lemma Bis Hpt) as Hpf.
  induction Hgt.
  - apply (precise_flow_all_inv) in Hpf.
    inversion Hpf.
  - pose proof (precise_flow_bnd_inv'' H Hpf) as [[U [Contra H1]] | [ls Contra]]; inversion Contra.
Qed.

Lemma good_precise_dec_implies_record_dec : forall G x D,
    good G ->
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd D) ->
    record_dec D.
Proof.
  introv Hgd Hpt.
  pose proof (typing_implies_bound Hpt) as [T' Bis].
  pose proof (good_binds Hgd Bis) as Hgt.
  pose proof (precise_flow_lemma Bis Hpt) as Hpf.
  induction Hgt.
  - apply (precise_flow_all_inv) in Hpf.
    inversion Hpf.
  - apply (record_precise_dec_implies_record_dec H Hpf).
Qed.

Lemma good_precise_dec_typ_inv : forall G x A S U,
    good G ->
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A S U)) ->
    S = U.
Proof.
  introv Hgd Hpt.
  pose proof (good_precise_dec_implies_record_dec Hgd Hpt) as Hrec.
  inversion Hrec.
  reflexivity.
Qed.

Lemma record_type_new: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  record_type (open_typ x T).
Proof.
  introv Hwf Bis.
  destruct (sto_binds_to_ctx_binds Hwf Bis) as [S Bi].
  destruct (corresponding_types Hwf Bi) as [Hlambda | Hnew].
  destruct Hlambda as [? [? [? [Bis' ?]]]].
  unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
  destruct Hnew as [? [? [Bis' [? ?]]]]. subst.
  unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
  apply record_new_typing in H.
  apply open_record_type. assumption.
Qed.

(* ###################################################################### *)
(** ** Narrowing *)


Definition subenv(G1 G2: ctx) :=
  forall x T2, binds x T2 G2 ->
    binds x T2 G1 \/
    exists T1,
      binds x T1 G1 /\ subtyp ty_general G1 T1 T2.

Lemma subenv_push: forall G G' x T,
  subenv G' G ->
  ok (G' & x ~ T) ->
  subenv (G' & x ~ T) (G & x ~ T).
Proof.
  intros.
  unfold subenv. intros xb Tb Bi. apply binds_push_inv in Bi.
  destruct Bi as [Bi | Bi].
  + destruct Bi as [Bi1 Bi2]. subst.
    left. eauto.
  + destruct Bi as [Bi1 Bi2].
    unfold subenv in H. specialize (H xb Tb Bi2). destruct H as [Bi' | Bi'].
    * left. eauto.
    * right. destruct Bi' as [T' [Bi1' Bi2']].
      exists T'. split. eauto. apply weaken_subtyp. assumption. eauto.
Qed.

Lemma subenv_last: forall G x S U,
  subtyp ty_general G S U ->
  ok (G & x ~ S) ->
  subenv (G & x ~ S) (G & x ~ U).
Proof.
  intros. unfold subenv. intros y T Bi.
  apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
  - destruct Bi. subst. right. exists S. split; eauto.
    apply weaken_subtyp; eauto.
  - destruct Bi. left. eauto.
Qed.

Lemma narrow_rules:
  (forall m1 G t T, ty_trm m1 G t T -> forall G',
    m1 = ty_general ->
    ok G' ->
    subenv G' G ->
    ty_trm m1 G' t T)
/\ (forall G z U d D, ty_def  G z U d D -> forall G',
    ok (G' & z ~ U) ->
    subenv G' G ->
    ty_def  G' z U d D)
/\ (forall G z U ds T, ty_defs  G z U ds T -> forall G',
    ok (G' & z ~ U) ->
    subenv G' G ->
    ty_defs  G' z U ds T)
/\ (forall G p, norm G p -> forall G',
    ok G' ->
    subenv G' G ->
    norm G' p)
/\ (forall m1 G S U, subtyp m1 G S U -> forall G',
    m1 = ty_general ->
    ok G' ->
    subenv G' G ->
    subtyp m1 G' S U).
Proof.
  apply rules_mutind; intros; eauto.
  - (* ty_var *)
    subst. unfold subenv in H1. specialize (H1 x T b).
    destruct H1.
    + eauto.
    + destruct H as [T' [Bi Hsub]].
      eapply ty_sub; eauto.
  - (* ty_all_intro *)
    subst.
    apply_fresh ty_all_intro as y; eauto.
    eapply H; eauto. apply subenv_push; eauto.
  - (* ty_new_intro *)
    subst.
    apply_fresh ty_new_intro as z. apply H; auto.
  - (* ty_let *)
    subst.
    apply_fresh ty_let as y; eauto.
    apply H0 with (x:=y); eauto. apply subenv_push; eauto.
  - (* ty_def_path *)
    constructor. apply H; auto. apply subenv_push. assumption. assumption.
  - (* ty_def_val *)
    constructor. apply H; auto. apply subenv_push. assumption. assumption.
  - (* norm_var *)
    unfold subenv in H0. destruct (H0 x T b) as [Hb | [T1 [Hb Hs]]].
    econstructor. eassumption.
    econstructor. eassumption.
  - (* norm_path *)
    econstructor; eauto.
  - (* subtyp_all *)
    subst.
    apply_fresh subtyp_all as y; eauto.
    apply H0; eauto. apply subenv_push; eauto.
Qed. 

Lemma narrow_typing: forall G G' t T,
  ty_trm ty_general G t T ->
  subenv G' G -> ok G' ->
  ty_trm ty_general G' t T.
Proof.
  intros. apply* narrow_rules.
Qed.

Lemma narrow_subtyping: forall G G' S U,
  subtyp ty_general G S U ->
  subenv G' G -> ok G' ->
  subtyp ty_general G' S U.
Proof.
  intros. apply* narrow_rules.
Qed.

(*

(* ###################################################################### *)
(** * Has member *)

Inductive has_member: ctx -> var -> typ -> typ_label -> typ -> typ -> Prop :=
| has_any : forall G x T A S U,
  ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  T ->
  has_member_rules G x T A S U ->
  has_member G x T A S U
with has_member_rules: ctx -> var -> typ -> typ_label -> typ -> typ -> Prop :=
| has_refl : forall G x A S U,
  has_member_rules G x (typ_rcd (dec_typ A S U)) A S U
| has_and1 : forall G x T1 T2 A S U,
  has_member G x T1 A S U ->
  has_member_rules G x (typ_and T1 T2) A S U
| has_and2 : forall G x T1 T2 A S U,
  has_member G x T2 A S U ->
  has_member_rules G x (typ_and T1 T2) A S U
| has_bnd : forall G x T A S U,
  has_member G x (open_typ x T) A S U ->
  has_member_rules G x (typ_bnd T) A S U
| has_sel : forall G x p B T' A S U,
  ty_trm ty_precise G (trm_path p) (typ_rcd (dec_typ B T' T')) ->
  has_member G x T' A S U ->
  has_member_rules G x (typ_path p B) A S U
| has_bot  : forall G x A S U,
  has_member_rules G x typ_bot A S U.

Scheme has_mut := Induction for has_member Sort Prop
with hasr_mut := Induction for has_member_rules Sort Prop.
Combined Scheme has_mutind from has_mut, hasr_mut.

Lemma has_member_rules_inv: forall G x T A S U, has_member_rules G x T A S U ->
  (T = typ_rcd (dec_typ A S U)) \/
  (exists T1 T2, T = typ_and T1 T2 /\
    (has_member G x T1 A S U \/
     has_member G x T2 A S U)) \/
  (exists T', T = typ_bnd T' /\
    has_member G x (open_typ x T') A S U) \/
  (exists p B T', T = typ_path p B /\
    ty_trm ty_precise G (trm_path p) (typ_rcd (dec_typ B T' T')) /\
    has_member G x T' A S U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst.
  - left. eauto.
  - right. left. exists T1 T2. eauto.
  - right. left. exists T1 T2. eauto.
  - right. right. left. exists T0. eauto.
  - right. right. right. left. exists p B T'. split. reflexivity.
    split. assumption. split. assumption. assumption.
  - right. right. right. right. reflexivity.
Qed.

Lemma rcd_typ_eq_bounds: forall T A S U,
  record_type T ->
  record_sub T (typ_rcd (dec_typ A S U)) ->
  S = U.
Proof.
  introv Htype Hsub.
  generalize dependent U. generalize dependent S. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Hsub; subst.
  - inversion H; subst. reflexivity.
  - inversion H; subst. reflexivity.
  - apply IHHtyp with (A:=A); eauto.
Qed.

Lemma has_member_inv: forall G x T A S U, has_member G x T A S U ->
  (T = typ_rcd (dec_typ A S U)) \/
  (exists T1 T2, T = typ_and T1 T2 /\
    (has_member G x T1 A S U \/
     has_member G x T2 A S U)) \/
  (exists T', T = typ_bnd T' /\
    has_member G x (open_typ x T') A S U) \/
  (exists p y B T', T = typ_path p B /\
    ty_trm ty_general G (trm_path p) (typ_sngl (avar_f y)) /\
    ty_trm ty_precise G (trm_path (p_var (avar_f y))) (typ_rcd (dec_typ B T' T')) /\
    has_member G x T' A S U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst. apply has_member_rules_inv in H1. apply H1.
Qed.

Lemma has_member_rcd_typ_sub2_mut:
  (forall G x T A S U,
    has_member G x T A S U ->
    record_type T ->
    T = (typ_rcd (dec_typ A S U)) \/ subtyp ty_precise G T (typ_rcd (dec_typ A S U)))  /\
  (forall G x T A S U,
    has_member_rules G x T A S U ->
    record_type T ->
    T = (typ_rcd (dec_typ A S U)) \/ subtyp ty_precise G T (typ_rcd (dec_typ A S U))).
Proof.
  apply has_mutind; intros.
  - apply H; eauto.
  - left. reflexivity.
  - inversion H0; subst. inversion H1; subst.
    assert (record_type T1) as Htyp1. { exists ls. assumption. }
    specialize (H Htyp1). destruct H as [H | H].
    + subst. right. apply subtyp_and11.
    + right.
      eapply subtyp_trans. eapply subtyp_and11. apply H.
  - inversion H0; subst. inversion H1; subst. inversion h; subst. inversion H3; subst.
    right. eapply subtyp_and12.
  - inversion H0. inversion H1.
  - inversion H0. inversion H1.
  - destruct H as [ls H]. inversion H.
Qed.

(* ###################################################################### *)
(** ** Good Has Member *)
(* Ifaz's good-has-member lemmas adjusted to paths *)

Lemma has_member_rcd_typ_sub_mut:
  (forall G x T A S U,
    has_member G x T A S U ->
    record_type T ->
    record_sub T (typ_rcd (dec_typ A S U))) /\
  (forall G x T A S U,
    has_member_rules G x T A S U ->
    record_type T ->
    record_sub T (typ_rcd (dec_typ A S U))).
Proof.
  apply has_mutind; intros.
  - apply H; eauto.
  - apply rs_refl.
  - inversion H0; subst. inversion H1; subst. apply rs_drop.
    apply H; eauto.
    exists ls. assumption.
  - inversion H0; subst. inversion H1; subst. inversion h; subst. inversion H3; subst.
    eapply rs_dropl. eapply rs_refl.
  - inversion H0. inversion H1.
  - inversion H0. inversion H1.
  - destruct H as [ls H]. inversion H.
Qed.

Lemma good_has_member_tightness: forall G x T A S U,
  good G ->
  binds x (typ_bnd T) G ->
  has_member G x (typ_bnd T) A S U ->
  S = U.
Proof.
  introv Hgd Bis Hmem.
  assert (record_type T) as Htype. {
    eapply good_typ_bnd_record; eauto.
  }
  assert (record_type (open_typ x T)) as Htypex. {
    apply open_record_type. assumption.
  }
  assert (has_member G x (open_typ x T) A S U) as Hmemx. {
    inversion Hmem; subst. inversion H0; subst. assumption.
  }
  assert (record_sub (open_typ x T) (typ_rcd (dec_typ A S U))) as Hsub. {
    destruct has_member_rcd_typ_sub_mut as [HL _].
    eapply HL; eauto.
  }
  eapply rcd_typ_eq_bounds. eapply Htypex. eapply Hsub.
Qed.


Lemma paths_singleton_typing: forall G x T p,
  ty_trm ty_precise G (trm_path (p_var (avar_f x))) T ->
  ty_trm_t ty_general G (trm_path p) (typ_sngl (avar_f x)) ->
  ty_trm ty_general G (trm_path p) T.
Proof.
  introv Hx Hp. gen T. dependent induction Hp; intros; eauto.
  - apply precise_to_general in Hx. apply (ty_var ty_general) in H.
    eapply ty_sngl_elim; eauto. reflexivity.
  - constructor.
    apply ty_sub with (T:=typ_rcd (dec_trm m path_general (typ_sngl (avar_f x)))).
    intro. inversion H.
    
Admitted.

Lemma tight_to_general:
  (forall m1 G t T,
     ty_trm_t m1 G t T ->
     m1 = ty_general ->
     ty_trm ty_general G t T) /\
  (forall m1 G S U,
     subtyp_t m1 G S U ->
     m1 = ty_general ->
     subtyp ty_general G S U) /\
  (forall G p,
     norm_t G p ->
     norm G p).
Proof.
  apply ts_mutind_t; intros; subst; eauto.
  - eapply subtyp_sel2.
    apply H in H1. apply* paths_singleton_typing. assumption.
  - eapply subtyp_sel1.
    apply H in H1. apply* paths_singleton_typing. assumption.
  - eapply norm_var. eapply b.
  - eapply norm_path. apply* H. assumption.
Qed.

Lemma good_has_member_covariance: forall G T1 T2 x A S2 U2,
  good G ->
  subtyp_t ty_general G T1 T2 ->
  ty_trm_t ty_general G (trm_path (p_var (avar_f x))) T1 ->
  has_member G x T2 A S2 U2 ->
  exists S1 U1, has_member G x T1 A S1 U1 /\
                subtyp_t ty_general G S2 S1 /\
                subtyp_t ty_general G U1 U2.
Proof.
  introv Hgd Hsub Hty Hmem.
  generalize dependent U2.
  generalize dependent S2.
  dependent induction Hsub; subst; intros.
  - (* top *)
    inversion Hmem; subst. inversion H0.
  - (* bot *)
    exists S2 U2. split.
    apply has_any. assumption. apply has_bot.
    split; apply subtyp_refl_t.
  - (* refl *)
    exists S2 U2. eauto.
  - (* trans *)
    assert (ty_trm_t ty_general G (trm_path (p_var (avar_f x))) T) as HS. {
      eapply ty_sub_t. intros Hp. subst. eexists; eauto.
      eapply Hty.
      eassumption.
    }
    specialize (IHHsub2 Hgd HS S2 U2 Hmem).
    destruct IHHsub2 as [S3 [U3 [Hmem3 [Hsub31 Hsub32]]]].
    specialize (IHHsub1 Hgd Hty S3 U3 Hmem3).
    destruct IHHsub1 as [S1 [U1 [Hmem1 [Hsub11 Hsub12]]]].
    exists S1 U1. split. apply Hmem1. split; eauto.
  - (* and11 *)
    exists S2 U2. split.
    inversion Hmem; subst. apply has_any. assumption. eapply has_and1. assumption.
    split; eauto.
  - (* and12 *)
    exists S2 U2. split.
    inversion Hmem; subst. apply has_any. assumption. eapply has_and2. assumption.
    split; eauto.
  - (* and2 *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1 [T2 [Heq [Hmem | Hmem]]]]; inversions Heq.
      * specialize (IHHsub1 Hgd Hty S2 U2 Hmem). apply IHHsub1.
      * specialize (IHHsub2 Hgd Hty S2 U2 Hmem). apply IHHsub2.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [p [y [B [T' [Heq _]]]]]. inversion Heq.
    + inversion Hmem.
  - (* fld *)
    inversion Hmem; subst. inversion H0; subst.
  - (* typ *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversions Hmem.
      exists S1 T1. split.
      apply has_any. assumption. apply has_refl.
      split; assumption.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [p [y [B [T' [Heq _]]]]]. inversion Heq.
    + inversion Hmem.
  - (* sel2 *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [q [y [B [T' [Heq [Hsngl [Hpr Has]]]]]]]. inversions Heq.
      assert (T' = T) as HeqT. {
        eapply good_unique_tight_bounds; eauto. admit.
      }
      subst. eauto.
    + inversion Hmem.
  - (* sel1 *)
    exists S2 U2. split.
    eapply has_any. assumption. eapply has_sel. eassumption. apply* tight_to_general. eassumption.
    eauto.
  - inversion Hmem; subst. inversion H2; subst.
  - inversion Hmem; subst. inversion H0; subst.
Qed.

Lemma good_has_member_monotonicity: forall G x T0 T A S U,
    good G ->
    binds x (typ_bnd T0) G ->
    has_member G x T A S U ->
    exists T1, has_member G x (typ_bnd T0) A T1 T1 /\
          subtyp_t ty_general G S T1 /\
          subtyp_t ty_general G T1 U.
Proof.
  introv Hgd Bis Hmem. inversion Hmem; subst.
  generalize dependent U. generalize dependent S.
  dependent induction H; intros.
  - (* var *)
    pose proof (binds_func H Bis) as H1.
    rewrite H1 in Hmem.
    pose proof (good_has_member_tightness Hgd Bis Hmem) as H2.
    exists U. subst. auto.
  - (* rec_intro *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversions Heq.
      apply IHty_trm_t; eauto.
      inversions H0. assumption.
      inversions H0. inversions H4. assumption.
    + destruct Hmem as [p [y [B [T' [Heq [Htyb Hmem]]]]]]. inversion Heq.
    + inversion Hmem.
  - (* rec_elim *)
    apply IHty_trm_t; eauto.
    apply has_any. assumption. apply has_bnd. assumption.
    apply has_bnd. assumption.
  - (* and_intro *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq [Hmem | Hmem]]]];
      inversions Heq; inversions H1; inversions H9.
      apply IHty_trm_t1; eauto.
      apply IHty_trm_t2; eauto. apply has_any; assumption.
      apply IHty_trm_t1; eauto. apply has_any; assumption.
      apply IHty_trm_t2; eauto.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [p [y [B [T' [Heq [Htyb Hmem]]]]]]. inversion Heq.
    + inversion Hmem.
  - (* sngl_intro *)
    apply has_member_inv in Hmem. 
    admit.
  - (* sngl_elim *)
    apply has_member_inv in Hmem. 
    admit.
  - (* sub *)
    destruct (good_has_member_covariance Hgd H1 H0 Hmem) as [S' [U' [Hmem' [Hsub1' Hsub2']]]].
    inversion Hmem'; subst.
    specialize (IHty_trm_t Hgd Bis S' U' Hmem' H4).
    destruct IHty_trm_t as [T1 [Hmem1 [Hsub1 Hsub2]]].
    exists T1. eauto.
Qed.

Lemma good_tight_bound_completeness : forall G x T A S U,
    good G ->
    binds x (typ_bnd T) G ->
    ty_trm_t ty_general G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A S U)) ->
    subtyp_t ty_general G (typ_path (p_var (avar_f x)) A) U /\
    subtyp_t ty_general G S (typ_path (p_var (avar_f x)) A).
Proof.
  introv Hgd Bis Hty.
  assert (has_member G x (typ_rcd (dec_typ A S U)) A S U) as Hmem. {
    apply has_any. assumption. apply has_refl.
  }
  apply good_has_member_monotonicity with (T0:=T) in Hmem.
  destruct Hmem as [T1 [Hmem [Hsub1 Hsub2]]].
  assert (has_member G x (open_typ x T) A T1 T1) as Hmemx. {
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq Hmem]]. inversions Heq. assumption.
    + destruct Hmem as [p [y [B [T' [Heq [Htyb Hmem]]]]]]. inversion Heq.
    + inversion Hmem.
  }
  assert (record_type T) as Htype. {
    eapply good_typ_bnd_record; eauto.
  }
  assert (record_type (open_typ x T)) as Htypex. {
    apply open_record_type. assumption.
  }
  assert (open_typ x T = (typ_rcd (dec_typ A T1 T1)) \/ subtyp ty_precise G (open_typ x T) (typ_rcd (dec_typ A T1 T1))) as Hsub. {
    destruct has_member_rcd_typ_sub2_mut as [HE _].
    eapply HE; eauto.
  }
  assert (ty_trm ty_precise G (trm_path (p_var (avar_f x))) (open_typ x T)) as Htypx. {
    eapply ty_rec_elim.
    eapply ty_var.
    assumption.
  }
  assert (ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A T1 T1))) as Htyp. {
    destruct Hsub as [Heq | Hsub].
    - rewrite Heq in Htypx. apply Htypx.
    - eapply ty_sub.
      intro. eexists. reflexivity.
      eapply Htypx. eapply Hsub.
  }
  split.
  eapply subtyp_trans_t. eapply subtyp_sel1_t. eapply Htyp. eauto. apply* norm_var_t. eapply Hsub2.
  eapply subtyp_trans_t. eapply Hsub1. eapply subtyp_sel2_t. eapply Htyp. eauto. apply* norm_var_t.
  eapply Hgd. eapply Bis.
Qed. *)

(* ###################################################################### *)
(** ** Tight Possible types *)

(*
Definition (Tight Possible types)

For a variable x, environment G, the set TPT(G, x) of simplified possible types
of x defined as v in G is the smallest set SS such that:

t_pt_precise   If G |-! x:T then T in SS(x).
t_pt_dec_trm   If {a: T} in SS(p) and G |-# T<:T' then {a:T'} in SS(p).
t_pt_dec_typ   If {A:T..U} in SS(p), G |-# T'<:T and G |-# U<:U' then {A:T'..U'} in SS(p).
t_pt_dec_bnd   If S in SS(x) then rec(x: S) in SS(x).
t_pt_all       If all(x: S)T in SS(p), G |-# S'<:S and G, x: S' |-# T<:T' then all(x: S')T' in SS(x).
t_pt_and       If S1 in SS(p) and S2 in SS(p) then (S1 & S2) in SS(p).
t_pt_path      If S in SS(q) and G |-! y: {A: S..S} and G |- p: y.type and G |- norm p then y.A in SS(q).
t_pt_sngl      If x in dom G then x.type in SS(x).
t_pt_sel       If {a :strong T} in SS(p) then T in SS(p)
t_pt_top       top in SS(p)
 *)

Inductive tight_pt : ctx -> path -> typ -> Prop :=
  (* Precise typing *)
| tpt_precise : forall G p T,
  ty_trm ty_precise G (trm_path p) T ->
  tight_pt G p T
  (* Term member subtyping *)
| tpt_fld_sub : forall G p a T T',
  tight_pt G p (typ_rcd (dec_trm a path_general T)) ->
  subtyp_t ty_general G T T' ->
  tight_pt G p (typ_rcd (dec_trm a path_general T'))
(* Strong typing *)
| tpt_fld_strong_sub: forall G p a T,
  tight_pt G p (typ_rcd (dec_trm a path_strong T)) ->
  tight_pt G p (typ_rcd (dec_trm a path_general T))
  (* Type member subtyping *)
| tpt_typ : forall G p A T T' U' U,
  tight_pt G p (typ_rcd (dec_typ A T U)) ->
  subtyp_t ty_general G T' T ->
  subtyp_t ty_general G U U' ->
  tight_pt G p (typ_rcd (dec_typ A T' U'))
  (* Recursive Types *)
| tpt_rec : forall G x S S',
  tight_pt G (p_var (avar_f x)) S ->
  S = open_typ x S' ->
  tight_pt G (p_var (avar_f x)) (typ_bnd S')
  (* Forall *)
| tpt_all : forall L G p S T S' T',
  tight_pt G p (typ_all S T) ->
  subtyp_t ty_general G S' S ->
  (forall y, y \notin L ->
   subtyp ty_general (G & y ~ S') (open_typ y T) (open_typ y T')) ->
  tight_pt G p (typ_all S' T')
  (* And *)
| tpt_and : forall G p S1 S2,
  tight_pt G p S1 ->
  tight_pt G p S2 ->
  tight_pt G p (typ_and S1 S2)
  (* Tight Selection *)
| tpt_typ_sel : forall G q p A S,
  tight_pt G q S ->
  ty_trm ty_precise G (trm_path p) (typ_rcd (dec_typ A S S)) ->
  norm_t G p ->
  tight_pt G q (typ_path p A)
  (* Top *)
| tpt_top : forall G p T,
  tight_pt G p T ->
  tight_pt G p typ_top
.

Hint Constructors tight_pt.

Lemma tight_to_precise_dec: forall G s p a U,
  wf_sto G  s ->
  ty_trm_t ty_general G (trm_path p) (typ_rcd (dec_trm a path_general U)) ->
  norm_t G p ->
  exists V, ty_trm ty_precise G (trm_path p) (typ_rcd (dec_trm a path_general V)) /\
            subtyp_t ty_general G V U.
Proof.
  introv Hwf Ht Hn. dependent induction Ht.
  - apply (ty_var ty_precise) in H. exists U. split*. 
  - Admitted.

(*
Scheme tsn_ty_trm_mut_t  := Induction for ty_trm_t    Sort Prop
with   tsn_subtyp_t      := Induction for subtyp_t    Sort Prop
with   tsn_norm_t        := Induction for norm_t      Sort Prop.
Combined Scheme tsn_mutind_t from tsn_ty_trm_mut_t, tsn_subtyp_t, tsn_norm_t.

Lemma tight_to_general:
  (forall m1 G t T,
     ty_trm_t m1 G t T ->
     m1 = ty_general ->
     ty_trm ty_general G t T) /\
  (forall m1 G S U,
     subtyp_t m1 G S U ->
     m1 = ty_general ->
     subtyp ty_general G S U) /\
  (forall G p,
     norm_t G p ->
     norm G p).
Proof.
  apply tsn_mutind_t; intros; subst; eauto.
  - eapply subtyp_sel2. apply* precise_to_general. assumption.
  - eapply subtyp_sel1. apply* precise_to_general. assumption.
  - apply* norm_var.
  - apply* norm_path.
Qed.

Lemma avar_b_typing_false: forall G s n T,
  wf_sto G s ->
  ty_trm ty_precise G (trm_path (p_var (avar_b n))) T ->
  False.
Proof.
  introv Hwf Ht. dependent induction Ht; eauto.
Qed.

Lemma tight_to_general_typing: forall G t T,
  ty_trm_t ty_general G t T ->
  ty_trm ty_general G t T.
Proof.
  intros. apply* tight_to_general. 
Qed.

Lemma good_precise_sel_inv_p : forall G s p q A,
    wf_sto G s ->
    ty_trm ty_precise G (trm_path p) (typ_path q A) ->
    False.
Proof.
  introv Hwf Hpt. gen q A. induction p; intros; lets Hgd: (wf_good Hwf); eauto.
  - destruct a. false* avar_b_typing_false. 
    pose proof (typing_implies_bound Hpt) as [T Bis].
    pose proof (good_binds Hgd Bis) as Hgt.
    pose proof (precise_flow_lemma Bis Hpt) as Hpf.
    induction Hgt.
    * apply (precise_flow_all_inv) in Hpf.
      inversion Hpf.
    * pose proof (precise_flow_bnd_inv'' H Hpf) as [[U [Contra H1]] | [ls Contra]]; inversion Contra.
  - inversions Hpt.
    * 
Qed.*)

Lemma t_pt_lemma: 
  (forall m1 G t T, ty_trm_t m1 G t T -> forall s p,
    wf_sto G s ->
    m1 = ty_general ->
    t = trm_path p ->
    norm_t G p ->
    tight_pt G p T) /\
  (forall m1 G T U, subtyp_t m1 G T U -> forall s p,
    wf_sto G s ->
    norm_t G p ->
    tight_pt G p T ->
    m1 = ty_general ->
    tight_pt G p U).
Proof.
  apply ts_mutind_t; intros; subst; try solve [inversion H1 | inversion H2 | inversion H3]; eauto.
  - (* ty_var *)
    destruct p; inversions H1. auto.
  - (* ty_fld_elim *)
    destruct p0; inversions H2. assert (ty_general = ty_general) as Hg by reflexivity.
    assert (trm_path p0 = trm_path p0) as Hp0 by reflexivity.
    inversions H3.
    specialize (H s p0 H0 Hg Hp0 H6).
    inversions H.
    * apply tpt_precise. apply* ty_fld_elim.
    * lets Htp: (tight_to_precise_dec H0 t H6). destruct Htp as [V [Hpr Hsub]].
      apply ty_fld_elim in Hpr. apply tpt_precise in Hpr.
      apply* tpt_precise.
    * lets Htp: (tight_to_precise_dec H0 t H6). destruct Htp as [V [Hpr Hsub]].
      apply ty_fld_elim in Hpr. apply* tpt_precise.
  - (* ty_rec_intro *)
    destruct p; inversions H2. eapply tpt_rec. apply* H. reflexivity.
  - (* ty_rec_elim *)
    inversions H2. assert (tight_pt G p0 (typ_bnd T)) as Ht. apply* H.
    inversions Ht. apply ty_rec_elim in H1. auto. rewrite <- open_var_path_typ_eq. assumption.
  - (* subtyp_bot *)
    admit.
  - (* subtyp_and11 *)
    inversions H1; eauto.
  - (* subtyp_and12 *)
    inversions H1; eauto.
  - (* subtyp_sel *)
    inversions H1.
    * 
Qed.

Lemma tight_possible_types_closure_tight: forall G p T U s,
  wf_sto G s ->
  norm_t G p ->
  tight_pt G p T ->
  subtyp_t ty_general G T U ->
  tight_pt G p U.
Proof.
  introv Hwf Hn HT Hsub. gen p s. 
  induction Hsub; intros; lets Hgd: (wf_good Hwf); eauto.
  - (* subtyp_bot_t *)
    false* tpt_bot.
  - (* subtyp_and11_t *)
    inversions HT; eauto.
    assert (subtyp_t ty_general G (typ_and T U) T) as Hsub by constructor.
    destruct m.
      * apply t_pt_dec_trm_strong in H.
        lets Ht: (t_pt_dec_trm H Hsub). apply* t_pt_sel. 
      * lets Ht: (t_pt_dec_trm H Hsub). apply* t_pt_sel. 
  - (* subtyp_and12_t *)
    inversions HT; eauto.
    (*analogous to prev case*) admit.
  - (* subtyp_sel1_t *)
    inversions HT.
    + false* good_precise_sel_inv.
    + admit.
    + admit.
Qed.

Lemma tight_possible_types_lemma :
  forall G U x,
    good G -> (* G good *)
    ty_trm_t ty_general G (trm_path (p_var (avar_f x)))  U -> (* G |-# x : U *)
    tight_pt G x U (* U \in TPT(G,x,T) *).
Proof.
  intros G U x Hgd Hty.
  dependent induction Hty; auto.
  - specialize (IHHty Hgd).
    eapply t_pt_bnd.
    apply IHHty.
    reflexivity.
  - specialize (IHHty Hgd).
    inversion IHHty; subst; auto.
  - apply* t_pt_sngl.
  - lets Hs: (IHHty2 Hgd). inversions Hs.
    * false* good_precise_sngl_inv.
    * apply* IHHty1.
  - eapply tight_possible_types_closure_tight; auto.
Qed.

(* ###################################################################### *)
(** * Misc Inversions *)

Lemma all_intro_inversion: forall G S t U,
  ty_trm ty_precise G (trm_val (val_lambda S t)) U ->
  exists T, U = typ_all S T.
Proof.
  intros. dependent induction H.
  - eexists. reflexivity.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
Qed.

Lemma new_intro_inversion: forall G T ds U,
  ty_trm ty_precise G (trm_val (val_new T ds)) U ->
  U = typ_bnd T /\ record_type T.
Proof.
  intros. inversion H; subst.
  - apply record_new_typing in H. split; eauto.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H0 Heqm1). destruct H0. inversion H0.
Qed.

(* ###################################################################### *)
(** ** Tight to precise *)

(* Lemma 1 *)
Lemma tight_to_precise_typ_dec: forall G s x A S U,
  wf_sto G s ->
  ty_trm_t ty_general G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A S U)) ->
  exists T,
    ty_trm ty_precise G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A T T)) /\
    subtyp_t ty_general G T U /\
    subtyp_t ty_general G S T.
Proof.
  introv Hwf Ht.
  assert (good G) as HG by (apply* wf_good).
  lets Htp: (tight_possible_types_lemma HG Ht). clear Ht.
  dependent induction Htp.
  - lets Hp: (good_precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHtp Hwf HG). destruct IHHtp as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.

Lemma tight_to_precise_path: forall G x p A S U s,
  wf_sto G s ->
  ty_trm_t ty_general G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A S U)) ->
  ty_trm ty_general G (trm_path p) (typ_sngl (avar_f x)) ->
  exists T,
    ty_trm ty_precise G (trm_path p) (typ_rcd (dec_typ A T T)) /\
    subtyp_t ty_general G T U /\
    subtyp_t ty_general G S T.
Proof.
  introv Hwf Hx Hp. 
  assert (good G) as HG by (apply* wf_good).
  lets Htp: (tight_possible_types_lemma HG Hx). clear Hx.
  dependent induction Htp.
  - lets Hp: (good_precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHtp Hwf HG). destruct IHHtp as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.


(* Lemma 2 *)
Lemma tight_subtyping_sel: forall G s x A S U,
    wf_sto G s ->
    ty_trm_t ty_general G (trm_path (p_var (avar_f x))) (typ_rcd (dec_typ A S U)) ->
    (subtyp_t ty_general G (typ_path (p_var (avar_f x)) A) U /\
     subtyp_t ty_general G S (typ_path (p_var (avar_f x)) A)).
Proof.
  introv Hwf Hty. 
  lets H: (tight_to_precise_typ_dec Hwf Hty). destruct H as [T [Ht [Hs1 Hs2]]].
  split.
  - destruct (typing_implies_bound Ht) as [V Hb].
    eapply subtyp_sel1_t in Ht. eapply subtyp_trans_t; eauto.
    eapply ty_sngl_intro_t. eassumption. eapply norm_var_t. eassumption.
  - destruct (typing_implies_bound Ht) as [V Hb].
    eapply subtyp_sel2_t in Ht. eapply subtyp_trans_t; eauto.
    eapply ty_sngl_intro_t. eassumption. eapply norm_var_t. eassumption.
Qed.

(* Theorem 1 *)
Lemma general_to_tight: forall G0 s0,
  wf_sto G0 s0 ->
  (forall m1 G t T,
     ty_trm m1 G t T ->
     G = G0 ->
     m1 = ty_general ->
     ty_trm_t ty_general G t T) /\
  (forall m1 G S U,
     subtyp m1 G S U ->
     G = G0 ->
     m1 = ty_general ->
     subtyp_t ty_general G S U).
Proof.
  intros G0 s0 Hwf.
  apply ts_mutind; intros; subst; eauto. 
  - lets Hc:
  
  (*
- assert (exists S ds, binds x (val_new S ds) s0) as Bis. {
      eapply tight_ty_rcd_typ__new; eauto.
    }
    destruct Bis as [? [? Bis]].
    eapply proj2. eapply tight_bound_completeness; eauto.
  - assert (exists S ds, binds x (val_new S ds) s0) as Bis. {
      eapply tight_ty_rcd_typ__new; eauto.
    }
    destruct Bis as [? [? Bis]].
    eapply proj1. eapply tight_bound_completeness; eauto.
*)
Qed.

Lemma general_to_tight_typing: forall G s t T,
  wf_sto G s ->
  ty_trm ty_general G t T ->
  ty_trm_t ty_general G t T.
Proof.
  intros. apply* general_to_tight.
Qed.

Lemma general_to_tight_subtyping: forall G s S U,
   wf_sto G s ->
  subtyp ty_general G S U ->
  subtyp_t ty_general G S U.
Proof.
  intros. apply* general_to_tight.
Qed.


(*
Lemma (Canonical forms 1)
If G ~ s and G |- x: all(x: T)U then s(x) = lambda(x: T')t where G |- T <: T' and G, x: T |- t: U.
 *)
Lemma canonical_forms_1: forall G s x T U,
  wf_sto G s ->
  ty_trm ty_general G (trm_path (p_var (avar_f x)))  (typ_all T U) ->
  (exists L T' t, binds x (val_lambda T' t) s /\ subtyp ty_general G T T' /\
  (forall y, y \notin L -> ty_trm ty_general (G & y ~ T) (open_trm y t) (open_typ y U))).
Proof.
Admitted.

(*
Lemma (Canonical forms 2)

If G ~ s and G |- x: {a: T} then s(x) = new(x: S)d for some type S, definition d such that G |- d: S and d contains a definition {a = t} where G |- t: T. *)


Lemma canonical_forms_2: forall G s x a T m,
  wf_sto G s ->
  ty_trm ty_general G (trm_path (p_var (avar_f x)))  (typ_rcd (dec_trm a m T)) ->
  (exists S ds t G' G'' z,
    G = G' & z ~ typ_bnd S & G'' /\
    binds x (val_new S ds) s /\ 
    ty_defs G' z (open_typ z S) (open_defs z ds) (open_typ z S) /\ 
    defs_has (open_defs x ds) (def_trm a t) /\ 
    ty_trm ty_general G t T).
Proof.
Admitted.

(* ###################################################################### *)
(** * Misc *)

Lemma val_typing: forall G v T,
  ty_trm ty_general G (trm_val v) T ->
  exists T', ty_trm ty_precise G (trm_val v) T' /\
             subtyp ty_general G T' T.
Proof.
  intros. dependent induction H.
  - exists (typ_all T U). split.
    apply ty_all_intro with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_bnd T). split.
    apply ty_new_intro with (L:=L); eauto. apply subtyp_refl.
  - destruct IHty_trm as [T' [Hty Hsub]].
    exists T'. split; eauto.
Qed.

Lemma var_typing_implies_avar_f: forall G a T,
  ty_trm ty_general G (trm_path (p_var a)) T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply IHty_trm.
Qed.


(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_path (p_var x))
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.

(*
Let G |- t: T and G ~ s. Then either

- t is a normal form, or
- there exists a store s', term t' such that s | t -> s' | t', and for any such s', t' there exists an environment G'' such that, letting G' = G, G'' one has G' |- t': T and G' ~ s'.
The proof is by a induction on typing derivations of G |- t: T.
*)

Lemma safety: forall G s t T,
  wf_sto G s ->
  ty_trm ty_general G t T ->
  (normal_form t \/ (exists s' t' G' G'', red t s t' s' /\ G' = G & G'' /\ ty_trm ty_general G' t' T /\ wf_sto G' s')).
Proof.
  introv Hwf H. dependent induction H; try solve [left; eauto].
  - (* All-E *) right.
    lets C: (canonical_forms_1 Hwf H).
    destruct C as [L [T' [t [Bis [Hsub Hty]]]]].
    exists s (open_trm z t) G (@empty typ).
    split.
    apply red_app with (T:=T'). assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
    eapply subst_ty_trm. eapply Hty.
    apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
    rewrite subst_fresh_typ.
    apply ty_sub with (T:=S).
    intro Contra. inversion Contra.
    assumption. apply subtyp_refl.
    eauto. eauto. eauto. eauto.
  - (* New-E *) right. destruct p.
    * destruct (var_typing_implies_avar_f H) as [x Hv]. subst.
      lets C: (canonical_forms_2 Hwf H).
      destruct C as [S [ds [t [G' [G'' [z [HG [Bis [Tyds [Has Ty]]]]]]]]]].
      exists s t G (@empty typ).
      split.
      apply red_sel with (T:=S) (ds:=ds); try assumption.
      split. rewrite concat_empty_r. reflexivity.
      split. assumption. assumption.
    * exists s (trm_let (trm_path (p_sel p t)) (trm_path (p_sel (p_var (avar_b 0)) m))) G (@empty typ).
      split. constructor. split. rewrite concat_empty_r. reflexivity. split.
      + pick_fresh x. lets L:  ((((dom G \u fv_ctx_types G) \u dom s) \u fv_typ T) \u fv_path p).
        apply ty_let with (L:=L) (T:=typ_rcd (dec_trm m m3 T)). assumption.
        intros.
        assert (open_trm x0 (trm_path (p_sel (p_var (avar_b 0)) m)) = trm_path (p_sel (p_var (avar_f x0)) m)) as Hop. {
          unfold open_trm. simpl. case_if. reflexivity.
        }
        rewrite Hop. eauto.
      + assumption.
  - (* Let *) right.
    destruct t.
    + lets Hv: (val_typing H).
      destruct Hv as [T' [Htyp Hsub]].
      pick_fresh x. assert (x \notin L) as FrL by auto. specialize (H0 x FrL).
      exists (s & x ~ v) (open_trm x u) (G & (x ~ T')) (x ~ T').
      split.
      apply red_let. eauto.
      split. reflexivity. split.
      apply narrow_typing with (G:=G & x ~ T).
      assumption.
      apply subenv_last. assumption.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      apply wf_sto_push. assumption. eauto. eauto. assumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + (* Path *)
      destruct p.
      * assert (exists x, a = avar_f x) as A. {
          eapply var_typing_implies_avar_f. eassumption.
        }
        destruct A as [x A]. subst a.
        exists s (open_trm x u) G (@empty typ).
        split.
        apply red_let_var.
        split.
        rewrite concat_empty_r. reflexivity.
        split.
        pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H0 y FrL).
        rewrite subst_intro_trm with (x:=y).
        rewrite <- subst_fresh_typ with (x:=y) (y:=x).
        eapply subst_ty_trm. eapply H0.
        apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
        rewrite subst_fresh_typ. assumption. eauto. eauto. eauto. eauto.
      * specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]. inversion IH.
        destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
        exists s' (trm_let t' u) G' G''.
        split. apply red_let_tgt. assumption.
        split. assumption. split.
        apply ty_let with (L:=L \u dom G') (T:=T); eauto.
        intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
        rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
        rewrite IH2.
        rewrite <- IH2. eauto.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH].
    + left. assumption.
    + right. destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' t' G' G''.
      split; try split; try split; try assumption.
      apply ty_sub with (T:=T).
      intro Contra. inversion Contra.
      assumption.
      rewrite IH2. apply weaken_subtyp. assumption.
      rewrite <- IH2. eapply wf_sto_to_ok_G. eassumption.
Qed.
