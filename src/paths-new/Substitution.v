(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import List Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions Weakening Helper_lemmas.

(** * Definitions *)

(** Substitution on variables: [a[u/z]] (substituting [z] with [u] in [a]). *)

Definition subst_var (z: var) (u: var) (x: var): var :=
  If x = z then u else x.

Definition subst_var_p (z: var) (u: path) (x: var): path :=
  If x = z then u else (pvar x).

Hint Unfold subst_var subst_var_p.

Definition subst_avar (z: var) (u: path) (a: avar) : path :=
  match a with
  | avar_b i => p_sel (avar_b i) nil
  | avar_f x => subst_var_p z u x
  end.

(* p    [u / z] where p = x.bs:
   x.bs [u / z] == x [u / z] . bs *)
Definition subst_path (z: var) (u: path) (p: path) : path :=
  match p with
  | p_sel x bs => sel_fields (subst_avar z u x) bs
  end.

(** Substitution on types and declarations: [T[u/z]] and [D[u/z]]. *)
Fixpoint subst_typ (z: var) (u: path) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_path q L    => typ_path (subst_path z u q) L
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  end
with subst_dec (z: var) (u: path) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_trm L U => dec_trm L (subst_typ z u U)
  end.

(** Substitution on terms, values, and definitions:
    [t[u/z]], [v[u/z]], [d[u/z]]. *)
Fixpoint subst_trm (z: var) (u: path) (t: trm) : trm :=
  match t with
  | trm_val v        => trm_val (subst_val z u v)
  | trm_path p       => trm_path (subst_path z u p)
  | trm_app x1 x2    => trm_app (subst_path z u x1) (subst_path z u x2)
  | trm_let t1 t2    => trm_let (subst_trm z u t1) (subst_trm z u t2)
  end
with subst_val (z: var) (u: path) (v: val) : val :=
  match v with
  | val_new T ds     => val_new (subst_typ z u T) (subst_defs z u ds)
  | val_lambda T t   => val_lambda (subst_typ z u T) (subst_trm z u t)
  end
with subst_def (z: var) (u: path) (d: def) : def :=
  match d with
  | def_typ L T => def_typ L (subst_typ z u T)
  | def_trm L t => def_trm L (subst_trm z u t)
  end
with subst_defs (z: var) (u: path) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (subst_defs z u rest) (subst_def z u d)
  end.

(** Substitution on the types of a typing environment: [G[u/z]]. *)
Definition subst_ctx (z: var) (u: path) (G: ctx) : ctx :=
  map (subst_typ z u) G.

(** * Lemmas *)

(** The following [subst_fresh_XYZ] lemmas state that if [x] is not free
    in a symbol [Y], then [Y[z/x] = Y]. *)

(** Fresh substitution
    - in variables *)
Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = p_sel a nil).
Proof.
  intros. destruct* a. simpl. autounfold. case_var*. simpls. notin_false.
Qed.

Lemma subst_fresh_path : forall x q p,
    x \notin fv_path p ->
    subst_path x q p = p.
Proof.
  intros. destruct p as [[n | z] bs]; simpls.
  - Case "p = (avar_b n).bs".
    rewrite* app_nil_r.
  - Case "p = (avar_f z).bs".
    unfold subst_var_p. apply notin_singleton in H. case_if.
    simpl. rewrite* app_nil_r.
Qed.

(** - in types, declarations, paths *)
Lemma subst_fresh_typ_dec: forall x y,
  (forall T : typ  , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec  , x \notin fv_dec  D  -> subst_dec  x y D  = D ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply* subst_fresh_path.
Qed.

Definition subst_fresh_typ x p := proj1 (subst_fresh_typ_dec x p).

(** - in terms, values, and definitions *)
Lemma subst_fresh_trm_val_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall v : val , x \notin fv_val  v  -> subst_val  x y v  = v ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_typ_dec || apply* subst_fresh_path).
Qed.

Lemma fv_ctx_types_push_eq : forall G x T,
    fv_ctx_types (G & x ~ T) = fv_ctx_types G \u fv_typ T.
Proof.
  intros.
  rewrite concat_def, single_def.
  unfold fv_ctx_types, fv_in_values; rewrite values_def.
  rewrite union_comm. simpl. reflexivity.
Qed.

Lemma fv_ctx_types_concat_eq : forall G1 G2,
    fv_ctx_types (G1 & G2) = fv_ctx_types G1 \u fv_ctx_types G2.
Proof.
  intros G1 G2. induction G2 using env_ind.
  - unfold fv_ctx_types, fv_in_values; rewrite values_def.
    rewrite concat_empty_r, empty_def, union_empty_r; reflexivity.
  - rewrite concat_assoc. rewrite fv_ctx_types_push_eq.
    rewrite IHG2. rewrite <- union_assoc. f_equal.
    symmetry. apply fv_ctx_types_push_eq.
Qed.

Lemma notin_fv_ctx_concat : forall x G2 G1,
    x \notin fv_ctx_types (G1 & G2) <->
    x \notin fv_ctx_types G1 /\ x \notin fv_ctx_types G2.
Proof.
  intros. rewrite <- notin_union.
  rewrite <- fv_ctx_types_concat_eq.
  split; intros; assumption.
Qed.

(** [x \notin fv(T)]           #<br>#
    [x \notin fv(G)]       #<br>#
    [―――――――――――――――――――――――] #<br>#
    [x \notin fv(G, z: T)] *)
Lemma fv_ctx_types_push: forall x z T G,
    x \notin fv_typ T ->
    x \notin fv_ctx_types G ->
    x \notin fv_ctx_types (G & z ~ T).
Proof.
  intros. rewrite fv_ctx_types_push_eq.
  apply notin_union. split~.
Qed.

(** [x \notin fv(G, z: T)]                   #<br>#
    [x \notin fv(T)]                         #<br>#
    [―――――――――――――――――――――――――――――――――――――] #<br>#
    [x \notin fv(T)] and [x \notin fv(G)] *)
Lemma invert_fv_ctx_types_push: forall x z T G,
  x \notin fv_ctx_types (G & z ~ T) -> x \notin fv_typ T /\ x \notin (fv_ctx_types G).
Proof.
  introv H. rewrite fv_ctx_types_push_eq in H.
  apply~ notin_union.
Qed.

(** [x \notin fv(G)]         #<br>#
    [――――――――――――――――――]    #<br>#
    [G[y/x] = G]    *)
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
    rewrite ((proj1 (subst_fresh_typ_dec _ _)) _ N1).
    reflexivity.
Qed.
(*
(** Definition of substitution on named variables: #<br>#
    [z[y/x] := if z == x then y else z], where [z] is a named variable. *)
Definition subst_fvar(x y z: var): var := If z = x then y else z.*)

(** The following lemmas state that substitution commutes with opening:
    for a symbol [Z], #<br>#
    [(Z^a)[y/x] = (Z[y/x])^(a[y/x])]. *)

(** Substitution commutes with opening
    - variables *)
Lemma subst_open_commut: forall x p u y n,
    lc_path p ->
    subst_avar x p (open_rec_avar n u y)
    = open_rec_path_p n (subst_var_p x p u) (subst_avar x p y).
Proof.
  introv Hl. unfold subst_var_p, subst_avar, open_rec_avar, subst_var_p.
  destruct y as [n' | y]; autounfold; destruct p as [z bs]; destruct z as [m | z'];
    repeat case_if; simpl; try case_if*; eauto; inversions  Hl; inversions H0.
Qed.

Lemma sel_fields_open : forall n p q bs,
  sel_fields (open_rec_path_p n p q) bs = open_rec_path_p n p (sel_fields q bs).
Proof.
  intros. destruct q. simpl. destruct p. destruct a. case_if; simpl; auto. rewrite* app_assoc.
  simpl. auto.
Qed.

Lemma sel_fields_subst : forall x p y bs b,
    subst_path x p (p_sel y bs) • b = (subst_path x p (p_sel y bs)) • b.
Proof.
  intros. destruct p, y; auto. simpl. unfold subst_var_p. case_if; simpl; auto.
Qed.

(** - paths *)
Lemma subst_open_commut_path: forall p n x q u,
    lc_path p ->
    subst_path x p (open_rec_path n u q)
    = open_rec_path_p n (subst_var_p x p u) (subst_path x p q).
Proof.
  introv Hl. destruct q as [z bs]. simpl. rewrite* subst_open_commut. rewrite* sel_fields_open.
Qed.

(** - types and declarations *)
Lemma subst_open_commut_typ_dec: forall x p u,
  lc_path p ->
  (forall t : typ, forall n: nat,
     subst_typ x p (open_rec_typ n u t)
     = open_rec_typ_p n (subst_var_p x p u) (subst_typ x p t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x p (open_rec_dec n u D)
     = open_rec_dec_p n (subst_var_p x p u) (subst_dec x p D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. apply* subst_open_commut_path.
Qed.

Lemma subst_open_commut_p: forall x p u y n,
    lc_path p ->
    subst_path x p (open_rec_avar_p n u y)
    = open_rec_path_p n (subst_path x p u) (subst_avar x p y).
Proof.
  introv Hl. unfold subst_path, subst_avar, subst_var_p.
  destruct y as [n' | y]; simpl; repeat case_if; destruct u; destruct a; simpl;
    try (rewrite* app_nil_r); repeat case_if; unfold sel_fields; destruct* p;
      inversions Hl; inversions H0; rewrite* app_nil_l.
Qed.

Lemma subst_open_commut_path_p: forall p n x q u,
    lc_path q ->
    subst_path x q (open_rec_path_p n u p)
    = open_rec_path_p n (subst_path x q u) (subst_path x q p).
Proof.
  introv Hl. destruct p as [z bs]. simpl.
  unfold subst_path. destruct u. rewrite <- sel_fields_open.
  unfold open_rec_path_p, subst_avar.
  destruct z; simpl; destruct a; repeat case_if*;
    unfold subst_var_p; repeat case_if;
      destruct q; simpl; try (rewrite app_assoc || rewrite app_nil_r);
        try solve [inversion Hl; inversion* H0].
Qed.

Lemma subst_open_commut_typ_dec_p: forall x y u,
  lc_path y ->
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ_p n u t)
     = open_rec_typ_p n (subst_path x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec_p n u D)
     = open_rec_dec_p n (subst_path x y u) (subst_dec x y D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*.
  apply* subst_open_commut_path_p.
Qed.

(** - types only *)
Lemma subst_open_commut_typ: forall x y u T,
  lc_path y ->
  subst_typ x y (open_typ u T) = open_typ_p (subst_var_p x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commut_typ_dec.
Qed.

Lemma subst_open_commut_typ_p: forall x y u T,
    lc_path y ->
    subst_typ x y (open_typ_p u T) = open_typ_p (subst_path x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commut_typ_dec_p.
Qed.

(** - terms, values, definitions, and list of definitions *)
Lemma subst_open_commut_trm_val_def_defs: forall x y u,
    lc_path y ->
  (forall t : trm, forall n: nat,
     subst_trm x y (open_rec_trm n u t)
     = open_rec_trm_p n (subst_var_p x y u) (subst_trm x y t)) /\
  (forall v : val, forall n: nat,
     subst_val x y (open_rec_val n u v)
     = open_rec_val_p n (subst_var_p x y u) (subst_val x y v)) /\
  (forall d : def , forall n: nat,
     subst_def x y (open_rec_def n u d)
     = open_rec_def_p n (subst_var_p x y u) (subst_def x y d)) /\
  (forall ds: defs, forall n: nat,
     subst_defs x y (open_rec_defs n u ds)
     = open_rec_defs_p n (subst_var_p x y u) (subst_defs x y ds)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal*;
  apply* subst_open_commut_path || apply* subst_open_commut_typ_dec.
Qed.

Lemma subst_open_commut_trm_val_def_defs_p: forall x y u,
    lc_path y ->
  (forall t : trm, forall n: nat,
     subst_trm x y (open_rec_trm_p n u t)
     = open_rec_trm_p n (subst_path x y u) (subst_trm x y t)) /\
  (forall v : val, forall n: nat,
     subst_val x y (open_rec_val_p n u v)
     = open_rec_val_p n (subst_path x y u) (subst_val x y v)) /\
  (forall d : def , forall n: nat,
     subst_def x y (open_rec_def_p n u d)
     = open_rec_def_p n (subst_path x y u) (subst_def x y d)) /\
  (forall ds: defs, forall n: nat,
     subst_defs x y (open_rec_defs_p n u ds)
     = open_rec_defs_p n (subst_path x y u) (subst_defs x y ds)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal*;
  apply* subst_open_commut_typ_dec_p || apply* subst_open_commut_path_p.
Qed.

(** - terms only *)
Lemma subst_open_commut_trm: forall x y u t,
    lc_path y ->
    subst_trm x y (open_trm u t)
    = open_trm_p (subst_var_p x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs.
Qed.

Lemma subst_open_commut_trm_p: forall x y u t,
    lc_path y ->
    subst_trm x y (open_trm_p u t)
    = open_trm_p (subst_path x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs_p.
Qed.

(** - definitions only *)
Lemma subst_open_commut_defs: forall x y u ds,
    lc_path y ->
    subst_defs x y (open_defs u ds)
    = open_defs_p (subst_var_p x y u) (subst_defs x y ds).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs.
Qed.

Lemma subst_open_commut_defs_p: forall x y u ds,
    lc_path y ->
    subst_defs x y (open_defs_p u ds)
    = open_defs_p (subst_path x y u) (subst_defs x y ds).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs_p.
Qed.

(** The following lemmas state that opening a symbol with a variable [y]
    is the same as opening the symbol with another variable [x] and
    substituting [x] with [y]: #<br>#
    [Z^y = (Z^x)[y/x]] *)

(** Substitution after opening
    - terms *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) -> lc_path u ->
  open_trm_p u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr Hl. unfold open_trm. rewrite* subst_open_commut_trm.
  destruct (@subst_fresh_trm_val_def_defs x u) as [Q _]. rewrite~ (Q t).
  unfold subst_var_p. case_var~.
Qed.

(** - definitions *)
Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) -> lc_path u ->
  open_defs_p u ds = subst_defs x u (open_defs x ds).
Proof.
  introv Fr Hl. unfold open_trm. rewrite* subst_open_commut_defs.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [_ [_ Q]]]. rewrite~ (Q ds).
  unfold subst_var_p. case_var~.
Qed.

(** - types *)
Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) -> lc_path u ->
  open_typ_p u T = subst_typ x u (open_typ x T).
Proof.
  introv Fr Hl. unfold open_typ. rewrite* subst_open_commut_typ.
  destruct (@subst_fresh_typ_dec x u) as [Q _]. rewrite* (Q T).
  unfold subst_var_p. case_var*.
Qed.

Ltac subst_open_fresh :=
  match goal with
  | [ |- context [ open_typ ?z (subst_typ ?x ?p ?T) ] ] =>
    replace (open_typ z (subst_typ x p T)) with (open_typ_p (subst_path x p (pvar z)) (subst_typ x p T)) by
        (unfold subst_path; simpl; unfold subst_var_p; rewrite If_r, open_var_typ_eq; auto)
    | [ |- context [ open_defs ?z (subst_defs ?x ?p ?ds) ] ] =>
        replace (open_defs z (subst_defs x p ds)) with (open_defs_p (subst_path x p (pvar z)) (subst_defs x p ds))
          by (unfold subst_path; simpl; unfold subst_var_p; rewrite If_r, open_var_defs_eq; auto)
     | [ |- context [ open_trm ?z (subst_trm ?x ?p ?t) ] ] =>
        replace (open_trm z (subst_trm x p t)) with (open_trm_p (subst_path x p (pvar z)) (subst_trm x p t))
          by (unfold subst_path; simpl; unfold subst_var_p; rewrite If_r, open_var_trm_eq; auto)
    end.

(** Substitution preserves labels of definitions: [label(d) = label(d[y/x])] *)
Lemma subst_label_of_def: forall x y d,
  label_of_def d = label_of_def (subst_def x y d).
Proof.
  intros. destruct* d.
Qed.

(** [l \notin labels(ds)]     #<br>#
    [――――――――――――――――――――――] #<br>#
    [l \notin labels(ds[y/x]] *)
Lemma subst_defs_hasnt: forall x y l ds,
  defs_hasnt ds l ->
  defs_hasnt (subst_defs x y ds) l.
Proof.
  intros x y l ds. unfold defs_hasnt. induction ds; introv Eq; auto.
  unfold get_def. simpl. rewrite <- subst_label_of_def.
  simpl in Eq. case_if~.
Qed.

Ltac subst_fresh_solver :=
  fresh_constructor;
  subst_open_fresh;
  match goal with
  | [ H: forall z, z \notin ?L -> forall G, _
      |- context [_ & subst_ctx ?x ?p ?G2 & ?z ~ subst_typ ?x ?p ?V] ] =>
    assert (subst_ctx x p G2 & z ~ subst_typ x p V = subst_ctx x p (G2 & z ~ V)) as B
        by (unfold subst_ctx; rewrite map_concat, map_single; reflexivity);
    rewrite <- concat_assoc; rewrite B;
    subst_open_fresh;
    rewrite* <- subst_open_commut_trm_p;
    rewrite* <- subst_open_commut_typ_p;
    rewrite <- open_var_typ_eq, <- open_var_trm_eq;
    apply* H; try rewrite* concat_assoc;
    rewrite <- B, concat_assoc; unfold subst_ctx;
    auto using weaken_ty_trm, ok_push, ok_concat_map
  end.
    (* try match goal with
            | [ |- _; _; _; _ ⊢ _ _ _ :: _ ] =>
              assert (z = subst_var_p x y z) as Hxyz by (unfold subst_var_p; rewrite~ If_r);
                rewrite Hxyz at 1
            end; *)

Ltac subst_tydef_solver :=
  match goal with
    | [ H: forall G3 G4 x, _,
          Hok: ok _,
          Hx: ?x \notin fv_ctx_types _,
          Hy: _ & _ ⊢ _ : _ |- _] =>
      specialize (H _ _ _ eq_refl Hok Hx);
      try solve [rewrite subst_open_commut_defs_p in H;
                 rewrite subst_open_commut_typ_p in H; eauto]
    end.

(** * Substitution Lemma *)
(** [G1, x: S, G2 ⊢ t: T]            #<br>#
    [ok(G1, x: S, G2)]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y: S[y/x]]       #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G1, G2[y/x] ⊢ t[y/x]: T[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ d: D]            #<br>#
    [ok(G1, x: S, G2)]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y: S[y/x]]       #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G1, G2[y/x] ⊢ d[y/x]: D[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ ds: T]           #<br>#
    [ok(G1, x: S, G2)]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y: S[y/x]]       #<br>#
    [――――――――――――――――――――――――――――――] #<br>#
    [G1, G2[y/x] ⊢ ds[y/x]: T[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ T <: U]           #<br>#
    [ok(G1, x: S, G2)]                #<br>#
    [x \notin fv(G1)]                  #<br>#
    [G1, G2[y/x] ⊢ y: S[y/x]]        #<br>#
    [―――――――――――――――――――――――――――――――] #<br>#
    [G1, G2[y/x] ⊢ T[y/x] <: U[y/x]] #<br>#  #<br># *)

(** The proof is by mutual induction on term typing, definition typing, and subtyping. *)
Lemma subst_rules: forall p S,
  lc_path p ->
  (forall G t T, G ⊢ t : T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    G1 & (subst_ctx x p G2) ⊢ subst_trm x p t : subst_typ x p T) /\
  (forall z bs P G d D, z; bs; P; G ⊢ d : D -> forall G1 G2 x p_x p_bs sbs,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    p = p_sel (avar_f p_x) p_bs ->
    sbs = (If z = x then p_bs else bs) ->
    subst_var x p_x z; sbs; P; G1 & (subst_ctx x p G2) ⊢ subst_def x p d : subst_dec x p D) /\
  (forall z bs P G ds T, z; bs; P; G ⊢ ds :: T -> forall G1 G2 x p_x p_bs sbs,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    p = p_sel (avar_f p_x) p_bs ->
    sbs = (If z = x then p_bs else bs) ->
    subst_var x p_x z; sbs; P; G1 & (subst_ctx x p G2) ⊢ subst_defs x p ds :: subst_typ x p T) /\
  (forall G T U, G ⊢ T <: U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x p G2) ⊢ trm_path p : subst_typ x p S ->
    G1 & (subst_ctx x p G2) ⊢ subst_typ x p T <: subst_typ x p U).
Proof.
  introv Hl. apply rules_mutind; intros; subst; simpl;
            try (subst_fresh_solver || rewrite subst_open_commut_typ_p);
            simpl in *; autounfold; eauto 4.
  - Case "ty_var".
    cases_if.
    + apply binds_middle_eq_inv in b; subst*. destruct* p.
    + eapply subst_fresh_ctx in H1.
      apply binds_subst in b; auto.
      constructor. rewrite <- H1.
      unfold subst_ctx. rewrite <- map_concat.
      apply binds_map; auto. apply ok_concat_map. apply* ok_remove.

  - Case "ty_new_intro".
    fresh_constructor.
    subst_open_fresh.
    destruct p as [p_x p_bs]. admit. (*
  match goal with
  | [ H: forall z, z \notin ?L -> forall G, _
      |- context [_ & subst_ctx ?x ?p ?G2 & ?z ~ subst_typ ?x ?p ?V] ] =>
    assert (subst_ctx x p G2 & z ~ subst_typ x p V = subst_ctx x p (G2 & z ~ V)) as B
        by (unfold subst_ctx; rewrite map_concat, map_single; reflexivity);
    rewrite <- concat_assoc; rewrite B;
    subst_open_fresh;
    rewrite* <- subst_open_commut_trm_p;
    rewrite* <- subst_open_commut_typ_p;
    rewrite <- open_var_typ_eq, <- open_var_trm_eq;
    apply* H; try rewrite* concat_assoc;
    rewrite <- B, concat_assoc; unfold subst_ctx;
    auto using weaken_ty_trm, ok_push, ok_concat_map
  end.*)

  - Case "ty_new_elim".
    asserts_rewrite (subst_path x p p0 • a = (subst_path x p p0) • a).
    destruct p0. apply sel_fields_subst. auto. Admitted. (*
  - Case "ty_rec_intro".
    constructor. rewrite <- subst_open_commut_typ_p. simpl in *. auto.
  - Case "ty_def_lambda".
    subst_tydef_solver. admit.
  - Case "ty_def_new".
    subst_tydef_solver. admit.
  - Case "ty_def_path".
    subst_tydef_solver. admit.
    (*apply* ty_def_path. intro. case_if; case_if*. *)
  - Case "ty_defs_cons".
    admit. (*constructor*.
    rewrite <- subst_label_of_def.
    apply subst_defs_hasnt. assumption.*)
Qed.*)

(** The substitution lemma for term typing.
    This lemma corresponds to Lemma 3.14 in the paper. *)
Lemma subst_ty_trm: forall p S G x t T,
    G & x ~ S ⊢ t : T ->
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    lc_path p ->
    G ⊢ trm_path p : subst_typ x p S ->
    G ⊢ subst_trm x p t : subst_typ x p T.
Proof.
  introv Ht Hok Hx Hl Hp.
  apply (proj41 (subst_rules S Hl)) with (G1:=G) (G2:=empty) (x:=x) in Ht.
  unfold subst_ctx in Ht. rewrite map_empty, concat_empty_r in Ht.
  apply Ht. rewrite* concat_empty_r. rewrite* concat_empty_r. assumption.
  unfold subst_ctx. rewrite map_empty, concat_empty_r. assumption.
Qed.

Lemma subst_ty_defs: forall z bs P G x S ds T p p_x p_bs sbs,
    z; bs; P; G & x ~ S ⊢ ds :: T ->
    p = p_sel (avar_f p_x) p_bs ->
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    G ⊢ trm_path p : subst_typ x p S ->
    sbs = (If z = x then p_bs else bs) ->
    subst_var x p_x z; sbs; P; G ⊢ subst_defs x p ds :: subst_typ x p T.
Proof.
  introv Hds Heq Hok Hx Hp Hsbs.
  assert (lc_path p) as Hl by (destruct p, a; inversion* Heq). subst p.
  eapply (proj43 (subst_rules S Hl)) with
      (G1:=G) (G2:=empty) (x:=x) (p_x0:=p_x) (p_bs0:=p_bs) (sbs:=sbs) in Hds;
    unfold subst_ctx in *; try rewrite map_empty in *; try rewrite concat_empty_r in *; auto.
Qed.

Lemma renaming_def: forall G z T ds x P,
    ok G ->
    z # G ->
    z \notin fv_ctx_types G \u fv_defs ds \u fv_typ T ->
    z; nil; P; G & z ~ open_typ z T ⊢ open_defs z ds :: open_typ z T ->
    G ⊢ tvar x : open_typ x T ->
    x; nil; P; G ⊢ open_defs x ds :: open_typ x T.
Proof.
  introv Hok Hnz Hnz' Hz Hx. rewrite open_var_typ_eq.
  assert (lc_path (pvar x)) as Hl by constructor*.
  rewrite subst_intro_typ with (x:=z); auto. rewrite open_var_defs_eq.
  rewrite subst_intro_defs with (x:=z); auto.
  assert (x = subst_var z x z) as Hxz by (unfold subst_var; case_if*).
  rewrite Hxz at 1. eapply subst_ty_defs; auto. eapply Hz. unfold pvar. eauto. rewrite <- subst_intro_typ; auto.
  rewrite* <- open_var_typ_eq. case_if*.
Qed.

Lemma path_replacement: forall p S,
  lc_path p ->
  (forall G t T, G ⊢ t : T -> forall t' T' y,
    t = open_trm_p p t' ->
    T = open_typ_p p T' ->
    G ⊢ trm_path p : open_typ_p p S ->
    G ⊢ tvar y : open_typ y S ->
    y \notin ((fv_trm t') \u (fv_typ T')) ->
    G ⊢ open_trm y t' : open_typ y T') /\
  (forall z bs P G d D, z; bs; P; G ⊢ d : D -> forall d' D' y,
    d = open_def_p p d' ->
    D = open_dec_p p D' ->
    G ⊢ trm_path p : open_typ_p p S ->
    G ⊢ tvar y : open_typ y S ->
    y \notin ((fv_def d') \u (fv_dec D')) ->
    y; nil; P; G ⊢ open_def y d' : open_dec y D') /\
  (forall z bs P G ds T, z; bs; P; G ⊢ ds :: T -> forall ds' T' y,
    ds = open_defs_p p ds' ->
    T = open_typ_p p T' ->
    G ⊢ trm_path p : open_typ_p p S ->
    G ⊢ tvar y : open_typ y S ->
    y \notin ((fv_defs ds') \u (fv_typ T')) ->
    y; nil; P; G ⊢ open_defs y ds' :: open_typ y T') /\
  (forall G T U, G ⊢ T <: U -> forall T' U' y,
    T = open_typ_p p T' ->
    U = open_typ_p p U' ->
    G ⊢ trm_path p : open_typ_p p S ->
    G ⊢ tvar y : open_typ y S ->
    y \notin ((fv_typ T') \u (fv_typ U')) ->
    G ⊢ open_typ y T' <: open_typ y U').
Proof.
  introv Hl. apply rules_mutind; intros; subst.
  - destruct t'; inversions H. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - Case "ty_def_typ".
    destruct D'; inversions H0. destruct d'; inversions H.
    assert (t0 = t1). admit. assert (t0 = t3). admit. subst. constructor.
  - Case "ty_def_all".
    destruct d'; inversions H0. destruct D'; inversions H1. destruct t2; inversions H7. destruct v; inversions H1.
    rename t1 into T. rename t2 into t. rename t4 into U. rename t3 into a.
    unfold open_def, open_dec. simpl. constructor.
  - Case "ty_def_new".
  - Case "ty_def_path".



  - destruct t'; inversions H. destruct p0. destruct p. simpls. admit.

Qed.

Lemma renaming_def': forall G z T ds x bs P,
    ok G ->
    x # G ->
    x \notin (fv_ctx_types G \u fv_defs ds \u fv_typ T) ->
    z; bs; P; G ⊢ open_defs_p (p_sel (avar_f z) bs) ds :: open_typ_p (p_sel (avar_f z) bs) T ->
    G ⊢ trm_path (p_sel (avar_f z) bs) : open_typ_p (p_sel (avar_f z) bs) T ->
    x; nil; P; G & x ~ open_typ x T ⊢ open_defs x ds :: open_typ x T.
Proof.
  introv Hok Hx Hx' Hds Hp.
  assert (lc_path (p_sel (avar_f z) bs)) as Hl by constructor*.
  apply weaken_ty_defs with (G2:=x ~ open_typ x T) in Hds; auto.
  apply weaken_ty_trm with (G2:= x ~ open_typ x T) in Hp; auto.
  lets Hpr: (proj43 (path_replacement T Hl)). eapply Hpr in Hds; eauto.
Qed.

Lemma renaming_typ: forall G z T U t x,
    ok G ->
    z # G ->
    lc_path (pvar x) ->
    z \notin (fv_ctx_types G \u fv_typ U \u fv_typ T \u fv_trm t) ->
    G & z ~ U ⊢ open_trm z t : open_typ z T ->
    G ⊢ tvar x : U ->
    G ⊢ open_trm x t : open_typ x T.
Proof.
  introv Hok Hnz Hl Hnz' Hz Hx. rewrite open_var_trm_eq. rewrite open_var_typ_eq.
  rewrite subst_intro_typ with (x:=z). rewrite subst_intro_trm with (x:=z).
  eapply subst_ty_trm; eauto. rewrite~ subst_fresh_typ. all: auto.
Qed.
