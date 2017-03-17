Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Dot_definitions.
Require Import Dot_proofs_precise_flow.
Require Import Dot_proofs_good_types.

(* ###################################################################### *)
(** ** Tight Possible types *)

(*
Definition (Tight Possible types)

For a variable x, environment G, the set TPT(G, x) of simplified possible types
of x defined as v in G is the smallest set SS such that:

If G |-! x:T then T in SS.
If {a:T} in SS and G |-# T<:T' then {a:T'} in SS.
If {A:T..U} in SS, G |-# T'<:T and G |-# U<:U' then {A:T'..U'} in SS.
If S in SS then rec(x: S) in SS.
If all(x: S)T in SS, G |-# S'<:S and G, x: S' |-# T<:T' then all(x: S')T' in SS.
If S1 in SS and S2 in SS then (S1 & S2) in SS.
If S in SS and G |-! y: {A: S..S} then y.A in SS.
 *)

Inductive tight_pt : ctx -> var -> typ -> Prop :=
  (* Precise typing *)
| t_pt_precise : forall G x T,
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) T ->
  tight_pt G x T
  (* Term member subtyping *)
| t_pt_dec_trm : forall G x a T T',
  tight_pt G x (typ_rcd (dec_trm a T)) ->
  subtyp ty_general sub_tight G T T' ->
  tight_pt G x (typ_rcd (dec_trm a T'))
  (* Type member subtyping *)
| t_pt_dec_typ : forall G x A T T' U' U,
  tight_pt G x (typ_rcd (dec_typ A T U)) ->
  subtyp ty_general sub_tight G T' T ->
  subtyp ty_general sub_tight G U U' ->
  tight_pt G x (typ_rcd (dec_typ A T' U'))
  (* Recursive Types *)
| t_pt_bnd : forall G x S S',
  tight_pt G x S ->
  S = open_typ x S' ->
  tight_pt G x (typ_bnd S')
  (* Forall *)
| t_pt_all : forall L G x S T S' T',
  tight_pt G x (typ_all S T) ->
  subtyp ty_general sub_tight G S' S ->
  (forall y, y \notin L ->
   subtyp ty_general sub_general (G & y ~ S') (open_typ y T) (open_typ y T')) ->
  tight_pt G x (typ_all S' T')
  (* And *)
| t_pt_and : forall G x S1 S2,
  tight_pt G x S1 ->
  tight_pt G x S2 ->
  tight_pt G x (typ_and S1 S2)
  (* Tight Selection *)
| t_pt_sel : forall G x y A S,
  tight_pt G x S ->
  ty_trm ty_precise sub_general G (trm_var y) (typ_rcd (dec_typ A S S)) ->
  tight_pt G x (typ_sel y A)
  (* Top *)
| t_pt_top : forall G x T,
  tight_pt G x T ->
  tight_pt G x typ_top
.

Hint Constructors tight_pt.

Lemma tight_possible_types_closure_tight: forall G x T U,
  good G ->
  tight_pt G x T ->
  subtyp ty_general sub_tight G T U ->
  tight_pt G x U.
Proof.
  intros G x T U Hgd HT Hsub.
  dependent induction Hsub; auto.
  - eauto.
  - inversion HT.
    destruct (good_ty_precise_bot Hgd H).
  - inversion HT.
    + apply ty_precise_var_and_inv1 in H.
      auto.
    + auto.
  - inversion HT.
    + apply ty_precise_var_and_inv2 in H.
      auto.
    + auto.
  - eapply t_pt_dec_trm; eauto.
  - eapply t_pt_dec_typ; eauto.
  - eapply t_pt_sel; eassumption.
  - dependent induction HT.
    + false * good_precise_sel_inv.
    + pose proof (good_unique_tight_bounds Hgd H H0) as H1.
      rewrite <- H1. assumption.
  - apply t_pt_all with (L:=L) (S:=S1) (T:=T1); auto.
Qed.

Lemma tight_possible_types_lemma :
  forall G U x,
    good G -> (* G good *)
    ty_trm ty_general sub_tight G (trm_var (avar_f x)) U -> (* G |-# x : U *)
    tight_pt G x U (* U \in TPT(G,x,T) *).
Proof.
  intros G U x Hgd Hty.
  dependent induction Hty.
  - auto.
  - specialize (IHHty Hgd).
    eapply t_pt_bnd.
    apply IHHty.
    reflexivity.
  - specialize (IHHty Hgd).
    inversion IHHty; subst; auto.
  - apply t_pt_and; auto.
  - eapply tight_possible_types_closure_tight; auto.
Qed.
