Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Precise_flow.
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

Reserved Notation "G '|-##' p '::' T" (at level 40, p at level 59).

Inductive tight_pt : ctx -> path -> typ -> Prop :=
  (* Precise typing *)
| t_pt_precise : forall G x T,
    G |-! trm_path (p_var (avar_f x)) :: T ->
    G |-## p_var (avar_f x) :: T
  (* Term member subtyping *)
| t_pt_dec_trm : forall G p a m T T',
    G |-## p :: typ_rcd (dec_trm a m T) ->
    G |-# T <: T' ->
    G |-## p :: typ_rcd (dec_trm a m T')
  (* Type member subtyping *)
| t_pt_dec_typ : forall G p A T T' U' U,
    G |-## p :: typ_rcd (dec_typ A T U) ->
    G |-# T' <: T ->
    G |-# U <: U' ->
    G |-## p :: typ_rcd (dec_typ A T' U')
  (* Recursive Types *)
| t_pt_bnd : forall G p S,
    G |-## p :: open_typ_p p S ->
    G |-## p :: typ_bnd S
  (* Forall *)
| t_pt_all : forall L G p S T S' T',
    G |-## p :: typ_all S T ->
    G |-# S' <: S ->
    (forall y, y \notin L ->
      G & y ~ S' |- T ||^ y <: T' ||^ y) ->
    G |-## p :: typ_all S' T'
  (* And *)
| t_pt_and : forall G p S1 S2,
    G |-## p :: S1 ->
    G |-## p :: S2 ->
    G |-## p :: typ_and S1 S2
  (* Tight Selection *)
| t_pt_sel : forall G p q A S,
    G |-## p :: S ->
    G |-! trm_path q :: typ_rcd (dec_typ A S S) ->
    G |-## p :: typ_path q A
  (* Top *)
| t_pt_top : forall G p T,
    G |-## p :: T ->
    G |-## p :: typ_top
where "G '|-##' p '::' T" := (tight_pt G p T).

Hint Constructors tight_pt.

Lemma tight_possible_types_closure_tight: forall G p T U,
  inert G ->
  G |-## p :: T ->
  G |-# T <: U ->
  G |-## p :: U.
Proof.
  introv Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversion HT. inversions H1.
    destruct (inert_ty_precise_bot Hgd H).
  - inversion* HT.
  - inversion* HT.
  - inversions HT.
    + false * inert_precise_sel_inv.
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
  - specialize (IHHty _ Hgd eq_refl eq_refl eq_refl).
    eapply t_pt_bnd.
    apply IHHty.
    reflexivity.
  - specialize (IHHty _ Hgd eq_refl eq_refl eq_refl).
    inversion IHHty; subst; auto.
  - apply t_pt_and; auto.
  - eapply tight_possible_types_closure_tight; auto.
Qed.
