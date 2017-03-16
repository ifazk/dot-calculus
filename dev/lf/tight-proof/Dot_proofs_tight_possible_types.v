Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Dot_definitions.
Require Import Dot_proofs_weakening.
Require Import Dot_proofs_wellformed_store.
Require Import Dot_proofs_substitution.
Require Import Dot_proofs_some_lemmas.
Require Import Dot_proofs_narrowing.
Require Import Dot_proofs_has_member.
Require Import Dot_proofs_tight_bound_completeness.
Require Import Dot_proofs_misc_inversions.
Require Import Dot_open_ind.
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
  tight_pt G x (typ_bnd S') (* 7. T is S -> rec(x:T) in SPT *)
  (* Forall *)
| t_pt_all : forall L G x S T S' T',
  tight_pt G x (typ_all S T) ->
  subtyp ty_general sub_tight G S' S ->
  (forall y, y \notin L ->
   subtyp ty_general sub_tight (G & y ~ S') (open_typ y T) (open_typ y T')) ->
  tight_pt G x (typ_all S' T')
  (* And *)
| t_pt_and : forall G x S1 S2,
  tight_pt G x S1 ->
  tight_pt G x S2 ->
  tight_pt G x (typ_and S1 S2) (* 5. S1, S2 in SPT -> S1 ^ S2 in SPT *)
  (* Tight Selection *)
| t_pt_sel : forall G x y A S,
  tight_pt G x S ->
  ty_trm ty_precise sub_general G (trm_var y) (typ_rcd (dec_typ A S S)) ->
  tight_pt G x (typ_sel y A) (* 6. S in SPT, G |-! y : {A : S .. S} -> y.A in SPT *)
  (* Top *)
| t_pt_top : forall G x T,
  tight_pt G x T ->
  tight_pt G x typ_top
.

Hint Constructors tight_pt.

Lemma tight_possible_types_lemma :
  forall G U x,
    good G -> (* G good *)
    ty_trm ty_general sub_tight G (trm_var (avar_f x)) U -> (* G |-# x : U *)
    tight_pt G x U (* U \in TPT(G,x,T) *).
Proof.
Admitted.
