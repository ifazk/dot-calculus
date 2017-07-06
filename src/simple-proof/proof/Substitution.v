(** printing |-     %\vdash%         #&vdash;#                     *)
(** printing /-     %\vdash%         #&vdash;#                     *)
(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** printing ->     %\rightarrow%    #&rarr;#                      *)
(** printing =>     %\Rightarrow%    #&rArr;#                      *)
(** printing ~~     %\~%             #~#                           *)
(** printing /\     %\wedge%         #&and;#                       *)
(** printing \/     %\vee%           #&or;#                        *)
(** printing forall %\forall%        #&forall;#                    *)
(** printing exists %\exists%        #&exist;#                     *)
(** printing lambda %\lambda%        #&lambda;#                    *)
(** printing mu     %\mu%            #&mu;#                        *)
(** printing nu     %\nu%            #&nu;#                        *)
(** printing Gamma  %\Gamma%         #&Gamma;#                     *)
(** printing Gamma' %\Gamma'%        #&Gamma;'#                    *)
(** printing Gamma1 %\Gamma_1%       #&Gamma;<sub>1</sub>#         *)
(** printing Gamma2 %\Gamma_2%       #&Gamma;<sub>2</sub>#         *)
(** printing top    %\top%           #&#8868;#                     *)
(** printing bottom %\bot%           #&perp;#                      *)
(** printing <>     %\ne%            #&ne;#                        *)
(** printing notin  %\notin%         #&notin;#                     *)
(** printing isin   %\in%            #&isin;#                      *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import Weakening.

(** * Definitions *)

(** Substitution on variables: [a[u/z]] (substituting [u] with [z] in [a]). *)
Definition subst_avar (z: var) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => (avar_f (If x = z then u else x))
  end.

(** Substitution on types and declarations: [T[u/z]] and [D[u/z]]. *)
Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_sel x L    => typ_sel (subst_avar z u x) L
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  end
with subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_trm L U => dec_trm L (subst_typ z u U)
  end.

(** Substitution on terms, values, and definitions:
    [t[u/z]], [v[u/z]], [d[u/z]]. *)
Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_avar z u x)
  | trm_val v        => trm_val (subst_val z u v)
  | trm_sel x1 L     => trm_sel (subst_avar z u x1) L
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

(** Substitution on the types of a typing environment: [Gamma[u/z]]. *)
Definition subst_ctx (z: var) (u: var) (G: ctx) : ctx :=
  map (subst_typ z u) G.

(** * Lemmas *)

(** The following [subst_fresh_XYZ] lemmas state that if [x] is not free
    in a symbol [Y], then [Y[z/x] = Y]. *)

(** Fresh substitution
    - in variables *)
Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = a).
Proof.
  intros. destruct* a. simpl. case_var*. simpls. notin_false.
Qed.

(** - in types and declarations *)
Lemma subst_fresh_typ_dec: forall x y,
  (forall T : typ , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec , x \notin fv_dec  D  -> subst_dec  x y D  = D ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*.
  apply* subst_fresh_avar.
Qed.

Definition subst_fresh_typ(x y: var) := proj1 (subst_fresh_typ_dec x y).

(** - in terms, values, and definitions *)
Lemma subst_fresh_trm_val_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall v : val , x \notin fv_val  v  -> subst_val  x y v  = v ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_avar || apply* subst_fresh_typ_dec).
Qed.

(** [x notin fv(T)]           #<br>#
    [x notin fv(Gamma)]       #<br>#
    ------------------------
    [x notin fv(Gamma, z: T) *)
Lemma fv_ctx_types_push: forall x z T G,
    x \notin fv_typ T ->
    x \notin fv_ctx_types G ->
    x \notin fv_ctx_types (G & z ~ T).
Proof.
  intros.
  unfold fv_ctx_types in *.
  unfold fv_in_values in *.
  rewrite <- cons_to_push in *.
  rewrite values_def in *.
  unfold LibList.map in *.
  do 2 rewrite LibList.fold_right_cons in *.
  simpl in *.
  apply notin_union. split~.
Qed.

(** [x notin fv(Gamma, z: T)]                #<br>#
    [x notin fv(T)]                          #<br>#
    ---------------------------------------
    [x notin fv(T)] and [x notin fv(Gamma)] *)
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

(** [x notin fv(Gamma)]
    -------------------
    [Gamma[y/x] = Gamma]    *)
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

(** Definition of substitution on named variables: #<br>#
    [z[y/x] := if z == x then y else z], where [z] is a named variable. *)
Definition subst_fvar(x y z: var): var := If z = x then y else z.

(** The following lemmas state that substitution commutes with opening:
    for a symbol [Z], #<br>#
    [(Z^a)[y/x] = (Z[y/x])^(a[y/x])]. *)

(** Substitution commutes with opening
    - for variables *)
Lemma subst_open_commut_avar: forall x y u,
  (forall a: avar, forall n: Datatypes.nat,
    subst_avar x y (open_rec_avar n u a)
    = open_rec_avar n (subst_fvar x y u) (subst_avar  x y a)).
Proof.
  intros. unfold subst_fvar, subst_avar, open_avar, open_rec_avar. destruct a.
  + repeat case_if; auto.
  + case_var*.
Qed.

(** - for types and declarations *)
Lemma subst_open_commut_typ_dec: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec n u D)
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*.
  apply subst_open_commut_avar.
Qed.

(** - for types only *)
Lemma subst_open_commut_typ: forall x y u T,
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commut_typ_dec.
Qed.

(** - for terms, values, and definitions *)
Lemma subst_open_commut_trm_val_def_defs: forall x y u,
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
    (apply* subst_open_commut_avar || apply* subst_open_commut_typ_dec).
Qed.

(** - only for terms *)
Lemma subst_open_commut_trm: forall x y u t,
    subst_trm x y (open_trm u t)
    = open_trm (subst_fvar x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs.
Qed.

(** - only for definitions *)
Lemma subst_open_commut_defs: forall x y u ds,
    subst_defs x y (open_defs u ds)
    = open_defs (subst_fvar x y u) (subst_defs x y ds).
Proof.
  intros. apply* subst_open_commut_trm_val_def_defs.
Qed.

(** The following lemmas state that opening a symbol with a variable [y]
    is the same as opening the symbol with another variable [x] and
    substituting [x] with [y]: #<br>#
    [Z^y = (Z^x)[y/x]] *)

(** Substitution after opening
    - for terms *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) ->
  open_trm u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commut_trm.
  destruct (@subst_fresh_trm_val_def_defs x u) as [Q _]. rewrite* (Q t).
  unfold subst_fvar. case_var*.
Qed.

(** - for definitions *)
Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) ->
  open_defs u ds = subst_defs x u (open_defs x ds).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commut_defs.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [_ [_ Q]]]. rewrite* (Q ds).
  unfold subst_fvar. case_var*.
Qed.

(** - for types *)
Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) ->
  open_typ u T = subst_typ x u (open_typ x T).
Proof.
  introv Fr. unfold open_typ. rewrite* subst_open_commut_typ.
  destruct (@subst_fresh_typ_dec x u) as [Q _]. rewrite* (Q T).
  unfold subst_fvar. case_var*.
Qed.

(** Substitution preserves labels of definitions: [label(d) = label(d[y/x])] *)
Lemma subst_label_of_def: forall x y d,
  label_of_def d = label_of_def (subst_def x y d).
Proof.
  intros. destruct d; simpl; reflexivity.
Qed.

(** [l notin labels(ds)]
    ------------------------
    [l notin labels(ds[y/x]] *)
Lemma subst_defs_hasnt: forall x y l ds,
  defs_hasnt ds l ->
  defs_hasnt (subst_defs x y ds) l.
Proof.
  intros x y l ds. unfold defs_hasnt. induction ds; introv Eq.
  - simpl. reflexivity.
  - unfold get_def. simpl. rewrite <- subst_label_of_def.
    simpl in Eq. case_if. apply (IHds Eq).
Qed.

(** * Substitution Lemma *)
(** [Gamma1, x: S, Gamma2 |- t: T]            #<br>#
    [ok(Gamma1, x: S, Gamma2)]               #<br>#
    [x notin fv(Gamma1)]                     #<br>#
    [Gamma1, Gamma2[y/x] |- y: S[y/x]]
    ---------------------------------------
    [Gamma1, Gamma2[y/x] |- t[y/x]: T[y/x]]  #<br>#
    and                                      #<br>#
    [Gamma1, x: S, Gamma2 |- d: D]            #<br>#
    [ok(Gamma1, x: S, Gamma2)]               #<br>#
    [x notin fv(Gamma1)]                     #<br>#
    [Gamma1, Gamma2[y/x] |- y: S[y/x]]
    ---------------------------------------
    [Gamma1, Gamma2[y/x] |- d[y/x]: D[y/x]]  #<br>#
    and                                      #<br>#
    [Gamma1, x: S, Gamma2 |- ds: T]           #<br>#
    [ok(Gamma1, x: S, Gamma2)]               #<br>#
    [x notin fv(Gamma1)]                     #<br>#
    [Gamma1, Gamma2[y/x] |- y: S[y/x]]
    ---------------------------------------
    [Gamma1, Gamma2[y/x] |- ds[y/x]: T[y/x]] #<br>#
    and                                      #<br>#
    [Gamma1, x: S, Gamma2 |- T <: U]          #<br>#
    [ok(Gamma1, x: S, Gamma2)]               #<br>#
    [x notin fv(Gamma1)]                     #<br>#
    [Gamma1, Gamma2[y/x] |- y: S[y/x]]
    -----------------------------------------
    [Gamma1, Gamma2[y/x] |- T[y/x] <: U[y/x]] *)

(** The proof is by mutual induction on term typing, definition typing, and subtyping. *)
Lemma subst_rules: forall y S,
  (forall G t T, G |- t : T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x y G2) |- trm_var (avar_f y) : subst_typ x y S ->
    G1 & (subst_ctx x y G2) |- subst_trm x y t : subst_typ x y T) /\
  (forall G d D, G /- d : D -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x y G2) |- trm_var (avar_f y) : subst_typ x y S ->
    G1 & (subst_ctx x y G2) /- subst_def x y d : subst_dec x y D) /\
  (forall G ds T, G /- ds :: T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x y G2) |- trm_var (avar_f y) : subst_typ x y S ->
    G1 & (subst_ctx x y G2) /- subst_defs x y ds :: subst_typ x y T) /\
  (forall G T U, G |- T <: U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    G1 & (subst_ctx x y G2) |- trm_var (avar_f y) : subst_typ x y S ->
    G1 & (subst_ctx x y G2) |- subst_typ x y T <: subst_typ x y U).
Proof.
  intros y S. apply rules_mutind; intros; subst; simpl; try solve [constructor; eauto].
  - Case "ty_var".
    cases_if.
    + apply binds_middle_eq_inv in b; subst; assumption.
    + apply subst_fresh_ctx with (y:=y) in H1.
      apply binds_subst in b; auto.
      apply ty_var. rewrite <- H1.
      unfold subst_ctx. rewrite <- map_concat.
      apply binds_map; auto.
  - Case "ty_all_intro".
    apply_fresh ty_all_intro as z; auto.
    assert (z \notin L) as FrL by auto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. auto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commut_trm.
    rewrite <- A at 3. rewrite <- subst_open_commut_typ.
    assert (subst_ctx x y G2 & z ~ subst_typ x y T
                               = subst_ctx x y (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    eapply H; auto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. auto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. auto. unfold subst_ctx. auto.
  - Case "ty_all_elim".
    rewrite subst_open_commut_typ.
    eapply ty_all_elim.
    simpl in H.
    apply H; auto.
    apply H0; auto.
  - Case "ty_new_intro".
    apply_fresh ty_new_intro as z; auto.
    assert (z \notin L) as FrL by auto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. auto.
    }
    rewrite <- A at 2. rewrite <- A at 3. rewrite <- A at 4.
    rewrite <- subst_open_commut_typ. rewrite <- subst_open_commut_defs.
    assert (subst_ctx x y G2 & z ~ subst_typ x y (open_typ z T)
                               = subst_ctx x y (G2 & z ~ open_typ z T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    apply H; auto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. auto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. auto. unfold subst_ctx. auto.
  - Case "ty_let".
    simpl. apply_fresh ty_let as z; auto.
    assert (subst_ctx x y G2 & z ~ subst_typ x y T
                               = subst_ctx x y (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r; auto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commut_trm.
    apply H0 with (x0:=z); eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. auto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. auto. unfold subst_ctx. auto.
  - Case "ty_rec_intro".
    apply ty_rec_intro.
    assert (trm_var (avar_f (If x = x0 then y else x))
            = subst_trm x0 y (trm_var (avar_f x))) as A. {
      simpl. reflexivity.
    }
    rewrite A.
    assert (open_typ (If x = x0 then y else x) (subst_typ x0 y T)
            = subst_typ x0 y (open_typ x T)) as B. {
      rewrite subst_open_commut_typ. unfold subst_fvar. reflexivity.
    }
    rewrite B.
    apply H; auto.
  - Case "ty_rec_elim".
    rewrite subst_open_commut_typ.
    apply ty_rec_elim.
    apply H; auto.
  - Case "ty_sub".
    eapply ty_sub; eauto.
  - Case "ty_defs_cons".
    simpl. apply ty_defs_cons; auto.
    rewrite <- subst_label_of_def.
    apply subst_defs_hasnt. assumption.
  - Case "subtyp_trans".
    eapply subtyp_trans; auto 5.
  - Case "subtyp_sel2".
    eapply subtyp_sel2. apply H; auto.
  - Case "subtyp_sel1".
    eapply subtyp_sel1. apply H; auto.
  - Case "subtyp_all".
    apply_fresh subtyp_all as z; auto.
    assert (z \notin L) as FrL by auto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. auto.
    }
    rewrite <- A at 2. rewrite <- A at 3.
    rewrite <- subst_open_commut_typ. rewrite <- subst_open_commut_typ.
    assert (subst_ctx x y G2 & z ~ subst_typ x y S2
                               = subst_ctx x y (G2 & z ~ S2)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    apply H0; auto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. auto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. auto. unfold subst_ctx. auto.
Qed.

(** The substitution lemma for term typing.
    This lemma corresponds to Lemma 3.14 in the paper. *)
Lemma subst_ty_trm: forall y S G x t T,
    G & x ~ S |- t : T ->
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    G |- trm_var (avar_f y) : subst_typ x y S ->
    G |- subst_trm x y t : subst_typ x y T.
Proof.
  intros.
  apply (proj51 (subst_rules y S)) with (G1:=G) (G2:=empty) (x:=x) in H.
  unfold subst_ctx in H. rewrite map_empty in H. rewrite concat_empty_r in H.
  apply H.
  rewrite concat_empty_r. reflexivity.
  rewrite concat_empty_r. assumption.
  assumption.
  unfold subst_ctx. rewrite map_empty. rewrite concat_empty_r. assumption.
Qed.

(** The substiution lemma for definition typing. *)
Lemma subst_ty_defs: forall y S G x ds T,
    G & x ~ S /- ds :: T ->
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    G |- trm_var (avar_f y) : subst_typ x y S ->
    G /- subst_defs x y ds :: subst_typ x y T.
Proof.
  intros.
  apply (proj53 (subst_rules y S)) with (G1:=G) (G2:=empty) (x:=x) in H;
    try rewrite concat_empty_r; auto.
  - unfold subst_ctx in H. rewrite map_empty in H. rewrite concat_empty_r in H.
    auto.
  - unfold subst_ctx. rewrite map_empty. rewrite concat_empty_r. assumption.
Qed.
