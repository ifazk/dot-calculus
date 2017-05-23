Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inert_types.

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

Reserved Notation "G '|-##' x '::' T" (at level 40, x at level 59).

Inductive tight_pt : ctx -> var -> typ -> Prop :=
  (* Precise typing *)
| t_pt_precise : forall G x T,
  G |-! trm_var (avar_f x) :: T ->
  G |-## x :: T
  (* Term member subtyping *)
| t_pt_dec_trm : forall G x a T T',
  G |-## x :: typ_rcd (dec_trm a T) ->
  G |-# T <: T' ->
  G |-## x :: typ_rcd (dec_trm a T')
  (* Type member subtyping *)
| t_pt_dec_typ : forall G x A T T' U' U,
  G |-## x :: typ_rcd (dec_typ A T U) ->
  G |-# T' <: T ->
  G |-# U <: U' ->
  G |-## x :: typ_rcd (dec_typ A T' U')
  (* Recursive Types *)
| t_pt_bnd : forall G x S S',
  G |-## x :: S ->
  S = open_typ x S' ->
  G |-## x :: typ_bnd S'
  (* Forall *)
| t_pt_all : forall L G x S T S' T',
  G |-## x :: typ_all S T ->
  G |-# S' <: S ->
  (forall y, y \notin L ->
   G & y ~ S' |- open_typ y T <: open_typ y T') ->
  G |-## x :: typ_all S' T'
  (* And *)
| t_pt_and : forall G x S1 S2,
  G |-## x :: S1 ->
  G |-## x :: S2 ->
  G |-## x :: typ_and S1 S2
  (* Tight Selection *)
| t_pt_sel : forall G x y A S,
  G |-## x :: S ->
  G |-! trm_var y :: typ_rcd (dec_typ A S S) ->
  G |-## x :: typ_sel y A
  (* Top *)
| t_pt_top : forall G x T,
  G |-## x :: T ->
  G |-## x :: typ_top
where "G '|-##' x '::' T" := (tight_pt G x T).

Hint Constructors tight_pt.

Lemma tight_possible_types_closure_tight: forall G x T U,
  inert G ->
  G |-## x :: T ->
  G |-# T <: U ->
  G |-## x :: U.
Proof.
  intros G x T U Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversion HT.
    destruct (precise_bot_false Hgd H).
  - inversion HT; auto. apply ty_and1_p in H. auto.
  - inversion HT; auto. apply ty_and2_p in H. auto.
  - inversions HT.
    + false* precise_psel_false.
    + pose proof (inert_unique_tight_bounds Hgd H H5) as Hu. subst. assumption.
Qed.

Lemma tight_possible_types_lemma :
  forall G U x,
    inert G ->
    G |-# trm_var (avar_f x) :: U ->
    G |-## x :: U.
Proof.
  intros G U x Hgd Hty.
  dependent induction Hty.
  - auto.
  - specialize (IHHty _ Hgd eq_refl).
    eapply t_pt_bnd.
    apply IHHty.
    reflexivity.
  - specialize (IHHty _ Hgd eq_refl).
    inversion IHHty; subst; auto.
  - apply t_pt_and; auto.
  - eapply tight_possible_types_closure_tight; auto.
Qed.
