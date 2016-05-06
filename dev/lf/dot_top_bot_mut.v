Set Implicit Arguments.

Require Import Coq.Setoids.Setoid.
Require Import LibFset LibList LibLN.
Require Import Coq.Program.Equality.

Close Scope nat_scope. Close Scope comp_scope. Close Scope list_scope.

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
  | avar_f : var -> avar. (* free var ("name"), refers to stack or ctx *)

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
  | trm_ref  : avar -> trm (* ref x *)
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


(** *** Typing environment (Γ) *)
Definition ctx := env typ.

(** *** Store typing (Σ) *)
(* Definition sigma := loc_env typ. *)
Definition sigma := env typ.
(* todo: should I keep my own env, since I'm binding locs and not vars? *)

(** *** Value environment (s) *)
Definition stack := env val.

(** *** Store  (σ) *)
Definition store := env val.

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
  | trm_ref a      => trm_ref (open_rec_avar k u a)
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
  | trm_var a        => (fv_avar a)
  | trm_val v        => (fv_val v)
  | trm_sel x m      => (fv_avar x)
  | trm_app f a      => (fv_avar f) \u (fv_avar a)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  | trm_ref a        => (fv_avar a)
  | trm_deref a        => (fv_avar a)
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
(** ** Operational Semantics *)

Inductive updated : store -> addr -> val -> store -> Prop:=
  | upd_exist : forall s l v s' s'' v',
    s = s' & l ~ v' & s'' ->
    updated s l v (s' & l ~ v & s'').


Inductive red : trm -> stack -> store -> trm -> stack -> store -> Prop :=
| red_sel : forall x m s sto t T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    red (trm_sel (avar_f x) m) s sto t s sto
| red_app : forall f a s sto T t,
    binds f (val_lambda T t) s ->
    red (trm_app (avar_f f) (avar_f a)) s sto (open_trm a t) s sto
| red_let : forall v t s sto x,
    x # s ->
    red (trm_let (trm_val v) t) s sto (open_trm x t) (s & x ~ v) sto         
| red_let_var : forall t s sto x,
    red (trm_let (trm_var (avar_f x)) t) s sto (open_trm x t) s sto
| red_let_tgt : forall t0 t s sto t0' s' sto',
    red t0 s sto t0' s' sto' ->
    red (trm_let t0 t) s sto (trm_let t0' t) s' sto'
| red_ref_var : forall x v s sto l,
    binds x v s ->
    l # sto ->
    red (trm_ref (avar_f x)) s sto (trm_val (val_loc l)) s (sto & l ~ v)
| red_asgn : forall x y l v s sto sto',
    binds x (val_loc l) s ->
    binds y v s ->
    updated sto l v sto' ->
    red (trm_asg (avar_f x) (avar_f y)) s sto (trm_var (avar_f y)) s sto'
| red_deref : forall x l s v sto,
    binds x (val_loc l) s ->
    binds l v sto ->
    red (trm_deref (avar_f x)) s sto (trm_val v) s sto.

(* ###################################################################### *)
(** ** Typing *)

Inductive tymode: Set := ty_precise | ty_general.
Inductive submode: Set := sub_tight | sub_general.

Inductive ty_trm : tymode -> submode -> ctx -> sigma -> trm -> typ -> Prop :=
| ty_var : forall m1 m2 G S x T,
    binds x T G ->
    ty_trm m1 m2 G S (trm_var (avar_f x)) T
| ty_loc : forall m1 m2 G S l T,
    binds l T S ->
    ty_trm m1 m2 G S (trm_val (val_loc l)) (typ_ref T)
| ty_all_intro : forall L m1 m2 G S T t U,
    (forall x, x \notin L ->
      ty_trm ty_general sub_general (G & x ~ T) S (open_trm x t) (open_typ x U)) ->
    ty_trm m1 m2 G S (trm_val (val_lambda T t)) (typ_all T U)
| ty_all_elim : forall m2 G S x z U T,
    ty_trm ty_general m2 G S (trm_var (avar_f x)) (typ_all U T) ->
    ty_trm ty_general m2 G S (trm_var (avar_f z)) U ->
    ty_trm ty_general m2 G S (trm_app (avar_f x) (avar_f z)) (open_typ z T)
| ty_new_intro : forall L m1 m2 G S T ds,
    (forall x, x \notin L ->
      ty_defs (G & x ~ (open_typ x T)) S (open_defs x ds) (open_typ x T)) ->
    ty_trm m1 m2 G S (trm_val (val_new T ds)) (typ_bnd T)
| ty_new_elim : forall m2 G S x m T,
    ty_trm ty_general m2 G S (trm_var (avar_f x)) (typ_rcd (dec_trm m T)) ->
    ty_trm ty_general m2 G S (trm_sel (avar_f x) m) T
| ty_let : forall L m2 G S t u T U,
    ty_trm ty_general m2 G S t T ->
    (forall x, x \notin L ->
      ty_trm ty_general sub_general (G & x ~ T) S (open_trm x u) U) ->
    ty_trm ty_general m2 G S (trm_let t u) U
| ty_rec_intro : forall m2 G S x T,
    ty_trm ty_general m2 G S (trm_var (avar_f x)) (open_typ x T) ->
    ty_trm ty_general m2 G S (trm_var (avar_f x)) (typ_bnd T)
| ty_rec_elim : forall m1 m2 G S x T,
    ty_trm m1 m2 G S (trm_var (avar_f x)) (typ_bnd T) ->
    ty_trm m1 m2 G S (trm_var (avar_f x)) (open_typ x T)
| ty_and_intro : forall m2 G S x T U,
    ty_trm ty_general m2 G S (trm_var (avar_f x)) T ->
    ty_trm ty_general m2 G S (trm_var (avar_f x)) U ->
    ty_trm ty_general m2 G S (trm_var (avar_f x)) (typ_and T U)
| ty_sub : forall m1 m2 G S t T U,
    (m1 = ty_precise -> exists x, t = trm_var (avar_f x)) ->
    ty_trm m1 m2 G S t T ->
    subtyp m1 m2 G S T U ->
    ty_trm m1 m2 G S t U
| ty_ref : forall m1 m2 G S x T,
    ty_trm ty_precise m2 G S (trm_var (avar_f x)) T ->
    ty_trm m1 m2 G S (trm_ref (avar_f x)) (typ_ref T)
| ty_deref : forall m1 m2 G S x T,
    ty_trm m1 m2 G S (trm_var (avar_f x)) (typ_ref T) ->
    ty_trm m1 m2 G S (trm_deref (avar_f x)) T
| ty_asgn : forall m1 m2 G S x y T,
    ty_trm m1 m2 G S (trm_var (avar_f x)) (typ_ref T) ->
    ty_trm m1 m2 G S (trm_var (avar_f y)) T ->
    ty_trm m1 m2 G S (trm_asg (avar_f x) (avar_f y)) T

with ty_def : ctx -> sigma -> def -> dec -> Prop :=
| ty_def_typ : forall G S A T,
    ty_def G S (def_typ A T) (dec_typ A T T)
| ty_def_trm : forall G S a t T,
    ty_trm ty_general sub_general G S t T ->
    ty_def G S (def_trm a t) (dec_trm a T)
with ty_defs : ctx -> sigma -> defs -> typ -> Prop :=
| ty_defs_one : forall G S d D,
    ty_def G S d D ->
    ty_defs G S (defs_cons defs_nil d) (typ_rcd D)
| ty_defs_cons : forall G S ds d T D,
    ty_defs G S ds T ->
    ty_def G S d D ->
    defs_hasnt ds (label_of_def d) ->
    ty_defs G S (defs_cons ds d) (typ_and T (typ_rcd D))

with subtyp : tymode -> submode -> ctx -> sigma -> typ -> typ -> Prop :=
| subtyp_top: forall m2 G S T,
    subtyp ty_general m2 G S T typ_top
| subtyp_bot: forall m2 G S T,
    subtyp ty_general m2 G S typ_bot T
| subtyp_refl: forall m2 G S T,
    subtyp ty_general m2 G S T T
| subtyp_trans: forall m1 m2 G S V T U,
    subtyp m1 m2 G S V T ->
    subtyp m1 m2 G S T U ->
    subtyp m1 m2 G S V U
| subtyp_and11: forall m1 m2 G S T U,
    subtyp m1 m2 G S (typ_and T U) T
| subtyp_and12: forall m1 m2 G S T U,
    subtyp m1 m2 G S (typ_and T U) U
| subtyp_and2: forall m2 G S V T U,
    subtyp ty_general m2 G S V T ->
    subtyp ty_general m2 G S V U ->
    subtyp ty_general m2 G S V (typ_and T U)
| subtyp_fld: forall m2 G S a T U,
    subtyp ty_general m2 G S T U ->
    subtyp ty_general m2 G S (typ_rcd (dec_trm a T)) (typ_rcd (dec_trm a U))
| subtyp_typ: forall m2 G S A S1 T1 S2 T2,
    subtyp ty_general m2 G S S2 S1 ->
    subtyp ty_general m2 G S T1 T2 ->
    subtyp ty_general m2 G S (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2))
| subtyp_sel2: forall G S x A U T,
    ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A U T)) ->
    subtyp ty_general sub_general G S U (typ_sel (avar_f x) A)
| subtyp_sel1: forall G S x A U T,
    ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A U T)) ->
    subtyp ty_general sub_general G S (typ_sel (avar_f x) A) T
| subtyp_sel2_tight: forall G S x A T,
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T T)) ->
    subtyp ty_general sub_tight G S T (typ_sel (avar_f x) A)
| subtyp_sel1_tight: forall G S x A T,
    ty_trm ty_precise sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_typ A T T)) ->
    subtyp ty_general sub_tight G S (typ_sel (avar_f x) A) T
| subtyp_all: forall L m2 G S S1 T1 S2 T2,
    subtyp ty_general m2 G S S2 S1 ->
    (forall x, x \notin L ->
       subtyp ty_general sub_general (G & x ~ S2) S (open_typ x T1) (open_typ x T2)) ->
    subtyp ty_general m2 G S (typ_all S1 T1) (typ_all S2 T2).

Inductive envmode : Set := env_stack | env_store .

Definition get_ctx (m: envmode) (env1 env2: env typ) :=
  match m with
  | env_stack => env1
  | env_store => env2
  end.

Definition get_sigma (m: envmode) (env1 env2: env typ) :=
  match m with
  | env_store => env1
  | env_stack => env2
  end.

Lemma gen_ty_trm_ctx: forall m1 m2 G S t T,
  ty_trm m1 m2 G S t T = ty_trm m1 m2 (get_ctx env_stack G S) (get_sigma env_stack G S) t T.
Proof.
  intros. reflexivity.
Qed.

Lemma gen_ty_trm_sigma: forall m1 m2 G S t T,
  ty_trm m1 m2 G S t T = ty_trm m1 m2 (get_ctx env_store S G) (get_sigma env_store S G) t T.
Proof.
  intros. reflexivity.
Qed.

Lemma gen_subtyp_ctx: forall m1 m2 G S T U,
  subtyp m1 m2 G S T U = subtyp m1 m2 (get_ctx env_stack G S) (get_sigma env_stack G S) T U.
Proof.
  intros. reflexivity.
Qed.

Lemma gen_subtyp_sigma: forall m1 m2 G S T U,
  subtyp m1 m2 G S T U = subtyp m1 m2 (get_ctx env_store S G) (get_sigma env_store S G) T U.
Proof.
  intros. reflexivity.
Qed.


(* equivalence between exists and setoids for setoid_rewrite in `gen_env` ltac *)
Add Parametric Morphism (A : Type) : (@ex A)
  with signature ((eq ==> iff) ==> iff)
  as ex_intro_eq.
Proof.
  intros.
  split; intros;
  destruct H0;
  exists x0;
  specialize (H x0 x0 eq_refl);
  apply H;
  assumption.
Qed. 


(* todo is this right? *)
(* generalization of well-formedness for stacks/stores
 * e1 denotes the main environment (for env_stack, it's ctx, for env_store, it's sigma),
 * and e2 the other environment *)
Inductive wf: envmode -> env typ -> env typ -> env val -> Prop :=
| wf_empty: forall m,
    wf m empty empty empty
| wf_push: forall m e1 e2 s x T v,
    wf m e1 e2 s ->
    x # e1 ->
    x # s ->
    (* x \notin fv_env_types e2 -> (* todo is this necessary? *) *)
    ty_trm ty_precise sub_general (get_ctx m e1 e2) (get_sigma m e1 e2) (trm_val v) T ->
    wf m (e1 & x ~ T) e2 (s & x ~ v)
| wf_push_e2: forall m e1 e2 s x T,
    wf m e1 e2 s ->
    x # e2 ->
    wf m e1 (e2 & x ~ T) s.

Definition wf_stack (G: ctx) (S: sigma) (s: stack): Prop :=
  wf env_stack G S s.
Hint Unfold wf_stack.

Definition wf_store (G: ctx) (S: sigma) (s: store): Prop :=
  wf env_store S G s.
Hint Unfold wf_store.

Lemma wf_rewrite_ctx : forall G S s, wf_stack G S s = wf env_stack G S s.
Proof. reflexivity. Qed.

Lemma wf_rewrite_sigma : forall G S s, wf_store G S s = wf env_store S G s.
Proof. reflexivity. Qed.

Ltac gen_env m :=
  match goal with
  | |- context ctx [ty_trm ?m1 ?m2 ?G ?S ?t ?T] =>
      match G with
      | get_ctx _ _ _ => fail 1
      | _             =>
        let c := match m with
        | env_stack => 
          context ctx[ty_trm m1 m2 (get_ctx env_stack G S) (get_sigma env_stack G S) t T]
        | env_store =>
          context ctx[ty_trm m1 m2 (get_ctx env_store S G) (get_sigma env_store S G) t T]
        end
        in change c
      end
  | |- context ctx [subtyp ?m1 ?m2 ?G ?S ?T ?U] =>
      match G with
      | get_ctx _ _ _ => fail 1
      | _             =>
        let c := match m with
        | env_stack =>
          context ctx[subtyp m1 m2 (get_ctx env_stack G S) (get_sigma env_stack G S) T U]
        | env_store =>
          context ctx[subtyp m1 m2 (get_ctx env_store S G) (get_sigma env_store S G) T U]
        end
        in change c
      end
  | |- ex (fun x =>_ ) =>
      match m with
      | env_stack =>
        setoid_rewrite gen_ty_trm_ctx ||
        setoid_rewrite gen_subtyp_ctx ||
        setoid_rewrite wf_rewrite_ctx
      | env_store =>
        setoid_rewrite gen_ty_trm_sigma ||
        setoid_rewrite gen_subtyp_sigma ||
        setoid_rewrite wf_rewrite_sigma
      end
  | _ => fail "Couldn't find non-generalized terms in goal"
  end.

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

Scheme ts_ty_trm_mut := Induction for ty_trm    Sort Prop
with   ts_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm    Sort Prop
with   rules_def_mut    := Induction for ty_def    Sort Prop
with   rules_defs_mut   := Induction for ty_defs   Sort Prop
with   rules_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.

(* ###################################################################### *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_env_types x)) in
  let D := gather_vars_with (fun x : stack     => dom x     ) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let F := gather_vars_with (fun x : trm       => fv_trm   x) in
  let G := gather_vars_with (fun x : val       => fv_val   x) in
  let H := gather_vars_with (fun x : def       => fv_def   x) in
  let I := gather_vars_with (fun x : defs      => fv_defs  x) in
  let J := gather_vars_with (fun x : typ       => fv_typ   x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J).

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
  ty_trm ty_def ty_defs
  subtyp.

Hint Constructors wf.

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

Lemma weaken_rules_ctx:
  (forall m1 m2 G S t T, ty_trm m1 m2 G S t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_trm m1 m2 (G1 & G2 & G3) S t T) /\
  (forall G S d D, ty_def G S d D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_def (G1 & G2 & G3) S d D) /\
  (forall G S ds T, ty_defs G S ds T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_defs (G1 & G2 & G3) S ds T) /\
  (forall m1 m2 G S T U, subtyp m1 m2 G S T U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subtyp m1 m2 (G1 & G2 & G3) S T U).
 Proof.
  apply rules_mutind; try solve [eauto].
  + intros. subst.
    eapply ty_var. eapply binds_weaken; eauto.
  + intros. subst.
    apply_fresh ty_all_intro as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply H. auto. auto.
  + intros. subst.
    apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    - specialize (H z zL G1 G2 (G3 & z ~ open_typ z T)).
      repeat rewrite concat_assoc in H.
      apply* H.
  + intros. subst.
    apply_fresh ty_let as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H0.
    apply H0. auto. auto.
  + intros. subst.
    apply_fresh subtyp_all as z.
    eauto.
    eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
    repeat rewrite concat_assoc in H0.
    apply H0. auto. auto.
Qed.

Lemma weaken_rules_sigma:
  (forall m1 m2 G S t T, ty_trm m1 m2 G S t T -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    ty_trm m1 m2 G (S1 & S2 & S3) t T) /\ 
  (forall G S d D, ty_def G S d D -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    ty_def G (S1 & S2 & S3) d D) /\
  (forall G S ds T, ty_defs G S ds T -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    ty_defs G (S1 & S2 & S3) ds T) /\
  (forall m1 m2 G S T U, subtyp m1 m2 G S T U -> forall S1 S2 S3,
    S = S1 & S3 ->
    ok (S1 & S2 & S3) ->
    subtyp m1 m2 G (S1 & S2 & S3) T U).
Proof.
  apply rules_mutind; try solve [eauto].
  intros. subst.
  eapply ty_loc. eapply binds_weaken; eauto.
Qed.

Lemma weaken_ty_trm: forall m m1 m2 e1 e1' e2 t T,
  ty_trm m1 m2 (get_ctx m e1 e2) (get_sigma m e1 e2) t T ->
  ok (e1 & e1') ->
  ty_trm m1 m2 (get_ctx m (e1 & e1') e2) (get_sigma m (e1 & e1') e2) t T.
Proof.
  intros.
  assert (e1 & e1' = e1 & e1' & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG.
  destruct m.
  - apply* weaken_rules_ctx; rewrite concat_empty_r; auto.
  - apply* weaken_rules_sigma; rewrite concat_empty_r; auto.
Qed.

Lemma weaken_ty_trm2: forall m m1 m2 e1 e2 e2' t T,
  ty_trm m1 m2 (get_ctx m e1 e2) (get_sigma m e1 e2) t T ->
  ok (e2 & e2') ->
  ty_trm m1 m2 (get_ctx m e1 (e2 & e2')) (get_sigma m e1 (e2 & e2')) t T.
Proof.
  intros.
  assert (e2 & e2' = e2 & e2' & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG.
  destruct m.
  - apply* weaken_rules_sigma; rewrite concat_empty_r; auto.
  - apply* weaken_rules_ctx; rewrite concat_empty_r; auto.
Qed.

Ltac weaken_ty_trm_ctx :=
  gen_env env_stack; apply* weaken_ty_trm || apply* weaken_ty_trm2.

Ltac weaken_ty_trm_sigma :=
  gen_env env_store; apply* weaken_ty_trm || apply* weaken_ty_trm2.

Lemma weaken_subtyp: forall m m1 m2 e1 e1' e2 T U,
  subtyp m1 m2 (get_ctx m e1 e2) (get_sigma m e1 e2) T U ->
  ok (e1 & e1') ->
  subtyp m1 m2 (get_ctx m (e1 & e1') e2) (get_sigma m (e1 & e1') e2) T U.
Proof.
  intros.
  assert (e1 & e1' = e1 & e1' & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. destruct m.
  - apply* weaken_rules_ctx. rewrite concat_empty_r. reflexivity. rewrite <- EqG. assumption.
  - apply* weaken_rules_sigma. rewrite concat_empty_r. reflexivity. rewrite <- EqG. assumption.
Qed.

Ltac weaken_subtyp_ctx :=
  gen_env env_stack; apply* weaken_subtyp.

Ltac weaken_subtyp_sigma :=
  gen_env env_store; apply* weaken_subtyp.

(* ###################################################################### *)
(** ** Well-formed stack and store *)

Lemma wf_to_ok_s: forall m e1 e2 s,
  wf m e1 e2 s -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_to_ok_e1: forall m e1 e2 s,
  wf m e1 e2 s -> ok e1.
Proof. intros. induction H; jauto. Qed.

Lemma wf_to_ok_e2: forall m e1 e2 s,
  wf m e1 e2 s -> ok e2.
Proof. intros. induction H; jauto. Qed.


Hint Resolve wf_to_ok_s wf_to_ok_e1 wf_to_ok_e2.

Lemma binds_update: forall s s' l v l' v',
  ok s ->
  updated s l v s' ->
  binds l' v' s ->
  If l = l' then binds l' v s' else binds l' v' s'.
Proof.
  introv Hok Hup Hbi. case_if.
  - inversion Hup; subst. apply binds_middle_eq.
    lets Hmi: (ok_middle_inv Hok). destruct Hmi. assumption.
  - inversion Hup. subst.
    apply binds_concat_inv in Hbi. destruct Hbi.
    + apply binds_concat_right. assumption.
    + inversion H0. apply binds_push_inv in H2. destruct H2.
      * inversion H2. false. 
      * destruct H2. apply binds_concat_left.
        apply binds_push_neq. assumption. assumption. assumption.
Qed.

Lemma double_binds_false: forall {A} (E1 E2 : env A) x v v',
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

Lemma binds_middle: forall {A} (E1 E2 E1' E2' : env A) (x : var) (v v' : A),
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

(* TODO there must be a simpler way to prove this *)
Lemma eq_middle_inv : forall {A} x x' (v v' : A) s s',
  x ~ v = s & x' ~ v' & s' -> s = empty /\ s' = empty /\ v = v'.
Proof.
  introv H. 
  assert (x ~ v = empty & x ~ v) as He. { rewrite concat_empty_l. reflexivity. }
  destruct s using env_ind.
  - rewrite concat_empty_l in H. destruct s' using env_ind.
    * rewrite concat_empty_r in H. apply eq_single_inv in H. destruct H as [Hx Hv]. subst. auto.
    * rewrite concat_assoc in H.
      rewrite He in H. apply eq_push_inv in H. destruct H as [Hx [Hv He']]. subst.
      rewrite <- concat_empty_l in He'. rewrite concat_assoc in He'. apply empty_middle_inv in He'. false.
  - destruct s' using env_ind.
    * rewrite concat_empty_r in H. rewrite He in H.
      apply eq_push_inv in H. destruct H as [Hx [Hv Hs]]. apply empty_push_inv in Hs. false.
    * rewrite He in H. rewrite concat_assoc in H.
      apply eq_push_inv in H. destruct H as [Hx [Hv Hs]]. apply empty_middle_inv in Hs. false.
Qed.          

Lemma update_to_wf_store: forall G S s s' l v T,
  wf_store G S s ->
  updated s l v s' ->
  forall S1 S2 s1 s2 vOld,
  s = s1 & l ~ vOld & s2 ->
  S = S1 & l ~ T & S2 ->
  ty_trm ty_precise sub_general G S1 (trm_val vOld) T ->
  ty_trm ty_precise sub_general G S1 (trm_val v) T ->
  wf_store G S s'.
Proof.
  introv Hwf. gen s' l T. unfold wf_store in Hwf. dependent induction Hwf; unfold wf_store in *; introv Hup.
  - inversion Hup. false* empty_middle_inv.
  - intros. rename e1 into S.
    inversion Hup. subst.
    assert ((l = x /\ s'' = empty) \/ (l <> x /\ exists s''' v0, s'' = s''' & x ~ v0)). {
      admit.
    }
    destruct H7.
    lets Hok: (wf_to_ok_s Hwf).
    + destruct H7; subst.
      assert (s0 & x ~ v0 & empty = s'0 & x ~ v' & empty). {
        rewrite concat_empty_r. assumption.
      } clear H6.
      assert (ok (s0 & x ~ v0 & empty)) as Hoks0. {
        rewrite concat_empty_r. constructor. assumption. assumption.
      }
      apply (binds_middle Hoks0) in H7. destruct H7 as [Hs [Hv _]]. subst.
      rewrite concat_empty_r. constructor; try assumption.
      apply wf_to_ok_e1 in Hwf.
      assert (ok (S & x ~ T & empty)) as Hoks. rewrite concat_empty_r. constructor. assumption. assumption.
      assert (S & x ~ T & empty = S1 & x ~ T0 & S2) as Heq. {
        rewrite concat_empty_r. assumption.
      }
      apply (binds_middle Hoks) in Heq. destruct Heq as [HS [HT He]]. subst. assumption.
    + destruct H7 as [Hne [s''' [v1 Hs]]]. subst.
      rewrite concat_assoc in *.
      pick_fresh y. destruct S using env_ind.
      * rewrite concat_empty_l in H3. apply eq_middle_inv in H3. destruct H3 as [Hs1 [Hs2 Ht]]. subst.
        apply eq_push_inv in H6. destruct H6 as [Hx [Hv Hs]]. subst.
        lets Hok: 
      * specialize (IHHwf (G & y ~ T) ()).

Lemma env_binds_to_st_binds_raw: forall m (st: env val) (env1: env typ) (env2: env typ) x T,
  wf m env1 env2 st ->
  binds x T env1 ->
  exists env1' env1'' v, 
    env1 = env1' & (x ~ T) & env1'' /\
    binds x v st /\ 
    ty_trm ty_precise sub_general (get_ctx m env1' env2) (get_sigma m env1' env2) (trm_val v) T.
Proof.
  introv Wf Bi. 
  induction Wf.
  - false* binds_empty_inv.
  - unfolds binds. rewrite get_push in *. case_if.
    + inversions Bi. exists e1 (@empty typ) v. 
      rewrite concat_empty_r. split.
      * auto.
      * auto.
    + apply IHWf in Bi; clear IHWf.
      destruct Bi as [e1' [e2' [ds [Eq [Bi Tyds]]]]]. subst.
      exists e1'. exists (e2' & x0 ~ T0). exists ds. split.
      * rewrite concat_assoc. reflexivity.
      * split. assumption. assumption.
  - apply IHWf in Bi; clear IHWf.
    destruct Bi as [env1' [env1'' [v [Eq [Bi Tyds]]]]].
    exists env1' env1'' v. split.
    + assumption.
    + split. assumption. subst. apply* weaken_ty_trm2.
Qed.

Lemma destruct_store: forall (st: store) l (v: val),
  binds l v st ->
  exists st' st'', st = st' & l ~ v & st''.
Proof.
  intros.
  induction st using env_ind.
  - false* binds_empty_inv.
  - unfolds binds. rewrite get_push in *. case_if.
    + inversion H; subst. exists st (@empty val).
      rewrite concat_empty_r. reflexivity.
    + apply IHst in H. clear IHst.
      destruct H as [st' [st'' H]]. subst.
      exists st' (st'' & x ~ v0). rewrite concat_assoc. reflexivity.
Qed.
  

(* todo remove *)
Lemma ctx_binds_to_stack_binds_raw: forall stack G S x T,
  wf_stack G S stack ->
  binds x T G ->
  exists G1 G2 v,
    G = G1 & (x ~ T) & G2 /\
    binds x v stack /\ 
    ty_trm ty_precise sub_general G1 S (trm_val v) T.
Proof.
  apply env_binds_to_st_binds_raw.
Qed.

(* todo remove *)
Lemma sigma_binds_to_store_binds_raw: forall store G S l T,
  wf env_store S G store ->
  binds l T S ->
  exists S1 S2 v,
    S = S1 & (l ~ T) & S2 /\
    binds l v store /\ 
    ty_trm ty_precise sub_general G S1 (trm_val v) T.
Proof.
  intros. gen_env env_store. apply* env_binds_to_st_binds_raw.
Qed.

Lemma st_binds_to_env_binds_raw: forall st env1 env2 x v m,
  wf m env1 env2 st ->
  binds x v st ->
  exists env1' env1'' T,
    env1 = env1' & (x ~ T) & env1'' /\
    ty_trm ty_precise sub_general (get_ctx m env1' env2) (get_sigma m env1' env2) (trm_val v) T.
Proof.
  introv Wf Bi. gen x v Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists e1 (@empty typ) T.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [e1' [e1'' [T0' [Eq Ty]]]].
      subst. exists e1' (e1'' & x ~ T) T0'. rewrite concat_assoc. auto.
  + specialize (IHWf _ _ Bi). destruct IHWf as [e1' [e1'' [T0' [Eq Ty]]]].
    subst. exists e1' e1'' T0'. split.
    reflexivity.
    apply* weaken_ty_trm2.
Qed.

Lemma stack_binds_to_ctx_binds_raw: forall stack G S x v,
  wf_stack G S stack ->
  binds x v stack ->
  exists G1 G2 T, G = G1 & x ~ T & G2 /\ ty_trm ty_precise sub_general G1 S (trm_val v) T.
Proof.
  intros. gen_env env_stack. 
  apply st_binds_to_env_binds_raw with (st := stack0); assumption.
Qed.

Lemma store_binds_to_sigma_binds_raw: forall store G S l v,
  wf_store G S store ->
  binds l v store ->
  exists S1 S2 T, S = S1 & l ~ T & S2 /\ ty_trm ty_precise sub_general G S1 (trm_val v) T.
Proof.
  intros. gen_env env_store.
  apply st_binds_to_env_binds_raw with (st := store0); assumption.
Qed.


Lemma possible_types_closure: forall G S s x v V T,
  wf_stack G S s ->
  binds x v s ->
  possible_types G S x v V ->
  subtyp ty_general sub_general G S V T ->
  possible_types G S x v T.
Proof.
  intros. eapply possible_types_closure_tight; eauto.
  eapply general_to_tight_subtyping; eauto.
Qed.

Lemma possible_types_completeness: forall G S s x T,
  wf_stack G S s ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) T ->
  exists v, binds x v s /\ possible_types G S x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise sub_general G S (trm_val v) T) as A. {
      destruct (ctx_binds_to_stack_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      weaken_ty_trm_ctx. rewrite concat_assoc.
      eapply wf_to_ok_e1. eassumption.
    }
    destruct A as [v [Bis Hty]].
    exists v. split. apply Bis. eapply possible_types_completeness_for_values; eauto.
  - specialize (IHty_trm Hwf).
    destruct IHty_trm as [v [Bis Hp]].
    exists v. split. assumption. eapply pt_bnd. eapply Hp. reflexivity.
  - specialize (IHty_trm Hwf).
    destruct IHty_trm as [v [Bis Hp]].
    exists v. split. assumption. inversion Hp; subst.
    + lets Htype: (record_type_new Hwf Bis). rewrite H5 in Htype. inversion Htype. inversion H0.
    + assumption.
  - specialize (IHty_trm1 Hwf). destruct IHty_trm1 as [v [Bis1 Hp1]].
    specialize (IHty_trm2 Hwf). destruct IHty_trm2 as [v' [Bis2 Hp2]].
    unfold binds in Bis1. unfold binds in Bis2. rewrite Bis2 in Bis1. inversions Bis1.
    exists v. split. eauto. apply pt_and; assumption.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [v [Bis Hp]].
    exists v. split. apply Bis. eapply possible_types_closure; eauto.
Qed.

Lemma possible_types_lemma: forall G S s x v T,
  wf_stack G S s ->
  binds x v s ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) T ->
  possible_types G S x v T.
Proof.
  introv Hwf Bis Hty.
  lets A: (possible_types_completeness Hwf Hty).
  destruct A as [v' [Bis' Hp]].
  unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis. inversions Bis.
  assumption.
Qed.

(* todo gen *)
Lemma ctx_binds_to_stack_binds_typing: forall G S s x T,
  wf_stack G S s ->
  binds x T G ->
  exists v, binds x v s /\ ty_trm ty_precise sub_general G S (trm_val v) T.
Proof.
  introv Hwf Bi.
  lets A: (ctx_binds_to_stack_binds_raw Hwf Bi).
  destruct A as [G1 [G2 [v [HeqG [Bis Hty]]]]].
  exists v. split; eauto.
  subst. rewrite <- concat_assoc.
  weaken_ty_trm_ctx.
  rewrite concat_assoc.
  eapply wf_to_ok_e1; eauto.
Qed.

Lemma sigma_binds_to_store_binds_typing: forall G S s l T,
  wf_store G S s ->
  binds l T S ->
  exists v, binds l v s /\ ty_trm ty_precise sub_general G S (trm_val v) T.
Proof.
  introv Hwf Bi.
  lets A: (sigma_binds_to_store_binds_raw Hwf Bi).
  destruct A as [S1 [S2 [v [HeqG [Bis Hty]]]]].
  exists v. split; eauto.
  subst. rewrite <- concat_assoc.
  weaken_ty_trm_sigma.
  rewrite concat_assoc.
  eapply wf_to_ok_e1; eauto.
Qed.

(*
Lemma (Canonical forms 1)
If G, S ~ s and G, S |- x: all(x: T)U then s(x) = lambda(x: T')t where G, S |- T <: T' and (G, x: T), S |- t: U.
 *) 
Lemma canonical_forms_1: forall G S s x T U,
  wf_stack G S s ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_all T U) ->
  (exists L T' t, binds x (val_lambda T' t) s /\ subtyp ty_general sub_general G S T T' /\
  (forall y, y \notin L -> ty_trm ty_general sub_general (G & y ~ T) S (open_trm y t) (open_typ y U))).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [V Bi].
  lets A: (ctx_binds_to_stack_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  inversion Hp; subst.
  - lets Htype: (record_type_new Hwf Bis). rewrite H4 in Htype.
    destruct Htype as [ls Htyp]. inversion Htyp.
  - pick_fresh y. exists (dom G \u L). exists V0. exists t.
    split. apply Bis. split. assumption.
    intros y0 Fr0.
    eapply ty_sub.
    intros Contra. inversion Contra.
    eapply narrow_typing.
    eapply H1; eauto.
    apply subenv_last. apply H6.
    apply ok_push. eapply wf_to_ok_e1; eauto. eauto.
    apply ok_push. eapply wf_to_ok_e1; eauto. eauto.
    eapply H7; eauto.
Qed.

(*
Lemma (Canonical forms 2)

If G, S ~ s and G, S |- x: {a: T} then s(x) = new(x: V)d for some type V, definition d such that G, S |- d: V 
and d contains a definition {a = t} where G, S |- t: T.

*)
Lemma canonical_forms_2: forall G S s x a T,
  wf_stack G S s ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_rcd (dec_trm a T)) ->
  (exists V ds t, binds x (val_new V ds) s /\ ty_defs G S (open_defs x ds) (open_typ x V) /\ defs_has (open_defs x ds) (def_trm a t) /\ ty_trm ty_general sub_general G S t T).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [V Bi].
  lets A: (ctx_binds_to_stack_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  apply pt_rcd_trm_inversion with (s:=s) in Hp; eauto.
  destruct Hp as [V' [ds [t' [Heq [Hdefs Htyd]]]]].
  subst.
  exists V' ds t'.
  split; try split; try split; try assumption.
  eapply new_ty_defs; eauto.
Qed.


(*
Lemma (Canonical forms 3)

If G, S ~ stack, G, S ~ store, and G, S |- x: Ref T then 
  stack(x) = loc l for some address l, such that G, S |- l: Ref T, and
  there exists a value v such that
  store(l) = v and G, S |- v: T.
*)
Lemma canonical_forms_3: forall G S sta sto x T,
  wf_stack G S sta ->
  wf_store G S sto ->
  ty_trm ty_general sub_general G S (trm_var (avar_f x)) (typ_ref T) ->
  exists l v,
    binds x (val_loc l) sta /\
    ty_trm ty_general sub_general G S (trm_val (val_loc l)) (typ_ref T) /\
    binds l v sto /\
    ty_trm ty_general sub_general G S (trm_val v) T.
Proof.
  introv HWfSta HWfSto Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [V Bi].
  lets A: (ctx_binds_to_stack_binds_typing HWfSta Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma HWfSta Bis Hty).
  inversion Hp; subst.
  - lets Htype: (record_type_new HWfSta Bis). rewrite H4 in Htype.
    destruct Htype as [ls Htyp]. inversion Htyp.
  - lets Bi': (typing_implies_bound_loc H4). destruct Bi' as [Tl Bi'].
    lets B: (sigma_binds_to_store_binds_typing HWfSto Bi'). destruct B as [vl [Bil Htyl]].
    exists l vl. split. assumption. split. assumption. split. assumption.
    admit.
Qed.


(* ###################################################################### *)
(** * Misc *)

Lemma var_typing_implies_avar_f: forall G S a T,
  ty_trm ty_general sub_general G S (trm_var a) T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply IHty_trm.
Qed.

Lemma val_typing: forall G S v T,
  ty_trm ty_general sub_general G S (trm_val v) T ->
  exists T', ty_trm ty_precise sub_general G S (trm_val v) T' /\
             subtyp ty_general sub_general G S T' T.
Proof.
  intros. dependent induction H.
  - exists (typ_ref T). auto.
  - exists (typ_all T U). split.
    apply ty_all_intro with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_bnd T). split.
    apply ty_new_intro with (L:=L); eauto. apply subtyp_refl.
  - destruct IHty_trm as [T' [Hty Hsub]].
    exists T'. split; eauto.
Qed.

(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.


(* todo correct reformulation? *)

(*
Let G, S |- t: T,
    G, S ~ sta, and
    G, S ~ sto. 
Then either
- t is a normal form, or
- there exists a stack sta', store sto', term t' such that 
      sta, sto | t -> sta', sto' | t', 
  and for any such sta', sto', t', there exists an environment G'' and store typing S''
  such that, letting 
      G' = G, G'',
      S' = S, S'',
  one has
      G', S' |- t': T, 
      G', S' ~ sta',
      G', S' ~ sto'
The proof is by a induction on typing derivations of G, S |- t: T.
*)


Lemma safety: forall G S sta sto t T,
  wf_stack G S sta ->
  wf_store G S sto ->
  ty_trm ty_general sub_general G S t T ->
  (normal_form t \/ 
    (exists sta' sto' t' G' G'' S' S'', 
    red t sta sto t' sta' sto' /\ 
    G' = G & G'' /\
    S' = S & S'' /\
    ty_trm ty_general sub_general G' S' t' T 
    /\ wf_stack G' S' sta'
    /\ wf_store G' S' sto')).
Proof.
  introv HWfSta HWfSto H. dependent induction H; try solve [left; eauto].
  - (* All-E *) right.
    lets C: (canonical_forms_1 HWfSta H).
    destruct C as [L [T' [t [Bis [Hsub Hty]]]]].
    exists sta sto (open_trm z t) G (@empty typ) S. exists (@empty typ).
    split.
    apply red_app with (T:=T'). assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
    eapply subst_ty_trm. eapply Hty.
    apply ok_push. eapply wf_to_ok_e1. eassumption. eauto. eauto. auto.
    rewrite subst_fresh_typ.
    apply ty_sub with (T:=U).
    intro Contra. inversion Contra.
    assumption. apply subtyp_refl.
    eauto. eauto. eauto. eauto.
  - (* Fld-E *) right.
    lets C: (canonical_forms_2 HWfSta H).
    destruct C as [V [ds [t [Bis [Tyds [Has Ty]]]]]].
    exists sta sto t G (@empty typ) S. exists (@empty typ).
    split. apply red_sel with (T:=V) (ds:=ds); try assumption.
    split. rewrite concat_empty_r. reflexivity.
    split. rewrite concat_empty_r. reflexivity.
    split. assumption.
    split. assumption. assumption.
  - (* Let *) right.
    destruct t.
    + (* var *)
      assert (exists x, a = avar_f x) as A. {
        eapply var_typing_implies_avar_f. eassumption.
      }
      destruct A as [x A]. subst a.
      exists sta sto (open_trm x u) G (@empty typ) S. exists (@empty typ).
      split. apply red_let_var.
      split. rewrite concat_empty_r. reflexivity.
      split. rewrite concat_empty_r. reflexivity. 
      split.
      pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H0 y FrL).
      rewrite subst_intro_trm with (x:=y).
      rewrite <- subst_fresh_typ with (x:=y) (y:=x).
      eapply subst_ty_trm. eapply H0.
      apply ok_push. eapply wf_to_ok_e1. eassumption. auto. auto. auto.
      rewrite subst_fresh_typ. assumption. auto. auto. auto. auto.
    + (* val *)
      lets Hv: (val_typing H).
      destruct Hv as [T' [Htyp Hsub]].
      pick_fresh x. assert (x \notin L) as FrL by auto. specialize (H0 x FrL).
      exists (sta & x ~ v) sto (open_trm x u) (G & (x ~ T')) (x ~ T') S. exists (@empty typ).
      split.
      apply red_let. auto.
      split. reflexivity. split. rewrite concat_empty_r. reflexivity.
      split. apply narrow_typing with (G:=G & x ~ T).
      assumption.
      apply subenv_last. assumption.
      apply ok_push. eapply wf_to_ok_e1. eassumption. eauto.
      apply ok_push. eapply wf_to_ok_e1. eassumption. eauto.
      split; auto.
    + (* sel *)
      specialize (IHty_trm HWfSta HWfSto). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. inversion H2. assumption.
      intros. rewrite IH2. eapply (proj51 weaken_rules_ctx).
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        weaken_ty_trm_sigma.
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption.
    + (* app *)
      specialize (IHty_trm HWfSta HWfSto). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. inversion H2. assumption.
      intros. rewrite IH2. eapply (proj51 weaken_rules_ctx).
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        weaken_ty_trm_sigma.
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption. 
    + (* let *)
      specialize (IHty_trm HWfSta HWfSto). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. inversion H2. assumption.
      intros. rewrite IH2. eapply (proj51 weaken_rules_ctx).
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        weaken_ty_trm_sigma.
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption. 
    + (* ref *)
      specialize (IHty_trm HWfSta HWfSto). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. inversion H2. assumption.
      intros. rewrite IH2. eapply (proj51 weaken_rules_ctx).
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        weaken_ty_trm_sigma.
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption. 
    + (* deref *) 
      specialize (IHty_trm HWfSta HWfSto). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. inversion H2. assumption.
      intros. rewrite IH2. eapply (proj51 weaken_rules_ctx).
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        weaken_ty_trm_sigma.
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption. 
    + (* asgn *)
      specialize (IHty_trm HWfSta HWfSto). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3]]]]]]]]]].
      exists sta' sto' (trm_let t' u) G' G'' S'. exists S''.
      split. apply red_let_tgt. assumption.
      split. assumption. split. assumption.
      split. apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. inversion H2. assumption.
      intros. rewrite IH2. eapply (proj51 weaken_rules_ctx).
      * instantiate (1:=G & x ~ T). inversion H2. inversion H5. subst.
        weaken_ty_trm_sigma.
      * reflexivity.
      * subst. inversion H2. inversion H5. apply ok_push. eauto. auto.
      * subst. inversion H2. inversion H4. split; assumption. 
  - (* sub *)
    specialize (IHty_trm HWfSta HWfSto). destruct IHty_trm as [IH | IH].
    + left. assumption.
    + right. 
      destruct IH as [sta' [sto' [t' [G' [G'' [S' [S'' [IH1 [IH2 [IH3 [IH4 [IH5 IH6]]]]]]]]]]]].
      exists sta' sto' t' G' G'' S'. exists S''.
      split; try split; try split; try split; try split; try assumption.
      apply ty_sub with (T:=T).
      intro Contra. inversion Contra. assumption.
      subst. weaken_subtyp_ctx. simpl. weaken_subtyp_sigma.
  - (* ref *)
    right. pick_fresh l.
    lets Bi: (typing_implies_bound H). destruct Bi as [V Bi].
    lets A: (ctx_binds_to_stack_binds_typing HWfSta Bi). destruct A as [v [Bis Htyv]].
    lets Hp: (possible_types_lemma HWfSta Bis H).
    exists sta (sto & l ~ v) (trm_val (val_loc l)) G (@empty typ) (S & l ~ V). exists (l ~ V).
    split. apply* red_ref_var.
    split. rewrite concat_empty_r. reflexivity.
    split. reflexivity.
    split. auto.

    split. auto.
    constructor. assumption. auto. auto. auto.
    simpl.
    (* todo *) admit.
  - (* deref *) 
    right.
    lets C: (canonical_forms_3 HWfSta HWfSto H).
    destruct C as [l [v [BiLoc [Htyloc [BiVal Htyval]]]]].
    exists sta sto (trm_val v) G (@empty typ) S. exists (@empty typ).
    split. apply red_deref with (l:=l). assumption. assumption.
    split. rewrite concat_empty_r. reflexivity.
    split. rewrite concat_empty_r. reflexivity.
    split. assumption. split. assumption. assumption.
  - (* asg *)
    right.
    lets C: (canonical_forms_3 HWfSta HWfSto H).
    destruct C as [l [v [BiLoc [Hty [BiSto HtyVal]]]]].
    lets D: (destruct_store BiSto). destruct D as [st' [st'' D]].
    lets Bi: (typing_implies_bound H0). destruct Bi as [Ty Bi].
    lets Bi': (ctx_binds_to_stack_binds_typing HWfSta Bi). destruct Bi' as [v0 [Bi' _]].
    exists sta (st' & l ~ v0 & st'') (trm_var (avar_f y)) G (@empty typ) S. exists (@empty typ).
    split.
    apply red_asgn with (l:=l) (v:=v0).
    assumption. assumption.
    apply upd_exist with (v':=v). assumption.
    split. rewrite concat_empty_r. reflexivity.
    split. rewrite concat_empty_r. reflexivity.
    split. assumption.
    split. assumption.
    apply update_to_wf_store with (s:=sto) (l:=l) (v:=v0) (T:=. assumption.
    apply upd_exist with (v':=v). assumption.
Qed.

