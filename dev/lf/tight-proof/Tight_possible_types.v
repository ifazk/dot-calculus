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

Reserved Notation "G ',' S '|-##' x ':' T" (at level 40, S at level 58, x at level 59).

Inductive tight_pt : ctx -> sigma -> var -> typ -> Prop :=
  (* Precise typing *)
| t_pt_precise : forall G S x T,
  G, S |-! trm_var (avar_f x) : T ->
  G, S |-## x : T
  (* Term member subtyping *)
| t_pt_dec_trm : forall G S x a T T',
  G, S |-## x : typ_rcd (dec_trm a T) ->
  G, S |-# T <: T' ->
  G, S |-## x : typ_rcd (dec_trm a T')
  (* Type member subtyping *)
| t_pt_dec_typ : forall G S x A T T' U' U,
  G, S |-## x : typ_rcd (dec_typ A T U) ->
  G, S |-# T' <: T ->
  G, S |-# U <: U' ->
  G, S |-## x : typ_rcd (dec_typ A T' U')
  (* Recursive Types *)
| t_pt_bnd : forall G S x T T',
  G, S |-## x : T ->
  T = open_typ x T' ->
  G, S |-## x : typ_bnd T'
  (* Forall *)
| t_pt_all : forall L G S x V T V' T',
  G, S |-## x : typ_all V T ->
  G, S |-# V' <: V ->
  (forall y, y \notin L ->
        G & y ~ V', S |- open_typ y T <: open_typ y T') ->
  G, S |-## x : typ_all V' T'
  (* And *)
| t_pt_and : forall G S x S1 S2,
  G, S |-## x : S1 ->
  G, S |-## x : S2 ->
  G, S |-## x : typ_and S1 S2
  (* Tight Selection *)
| t_pt_sel : forall G S x y A T,
  G, S |-## x : T ->
  G, S |-! trm_var y : typ_rcd (dec_typ A T T) ->
  G, S |-## x : typ_sel y A
  (* Loc *)
| t_pt_loc : forall G S x T U,
  G, S |-## x : typ_ref T ->
  G, S |-# T <: U ->
  G, S |-# U <: T ->  
  G, S |-## x : typ_ref U
  (* Top *)
| t_pt_top : forall G S x T,
  G, S |-## x : T ->
  G, S |-## x : typ_top
where "G ',' S '|-##' x ':' T" := (tight_pt G S x T).

Hint Constructors tight_pt.

Lemma tight_possible_types_closure_tight: forall G S x T U,
  inert G ->
  G, S |-## x : T ->
  G, S |-# T <: U ->
  G, S |-## x : U.
Proof.
  intros G S x T U Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversion HT.
    destruct (precise_bot_false Hgd H).
  - inversion HT; auto. apply ty_and1_p in H. auto.
  - inversion HT; auto. apply ty_and2_p in H. auto.
  - inversions HT.
    + false* precise_psel_false.
    + pose proof (inert_unique_tight_bounds Hgd H H6) as Hu. subst. assumption.
Qed.

Lemma tight_possible_types_lemma : forall G S U x,
    inert G ->
    G, S |-# trm_var (avar_f x) : U ->
    G, S |-## x : U.
Proof.
  intros G S U x Hgd Hty.
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
