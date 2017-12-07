(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions RecordAndInertTypes PreciseTyping TightTyping InvertibleTyping
        GeneralToTight Subenvironments Weakening Narrowing Substitution.

Local Hint Resolve x_bound_unique.
Local Hint Resolve pf_inert_unique_tight_bounds.

Inductive bnd_sup : ctx -> typ -> typ -> Prop :=
| bnd_sup_top : forall G T,
    bnd_sup G T typ_top
| bnd_sup_and : forall G T T1 T2,
    bnd_sup G T T1 ->
    bnd_sup G T T2 ->
    bnd_sup G T (typ_and T1 T2)
| bnd_sup_sel : forall G T x A U S,
    G ⊢! x : U ⪼ typ_rcd (dec_typ A S S) ->
    bnd_sup G T S ->
    bnd_sup G T (typ_sel (avar_f x) A)
| bnd_sup_rec : forall G T,
    bnd_sup G (typ_bnd T) (typ_bnd T).
Local Hint Constructors bnd_sup.

Lemma tight_bnd_sup: forall G S T U,
    inert G ->
    G ⊢# T <: U ->
    bnd_sup G (typ_bnd S) T ->
    bnd_sup G (typ_bnd S) U.
Proof.
  introv Hi H.
  dependent induction H; intros;
    match goal with
    | [ H : bnd_sup _ _ _ |- _ ] =>
      try solve [inversions H; auto]
    end; eauto.
  inversions H0; auto.
  replace U0 with U in * by eauto.
  replace S0 with T in * by eauto.
  auto.
Qed.

Inductive all_sup : ctx -> typ -> typ -> Prop :=
| all_sup_top : forall G T,
    all_sup G T typ_top
| all_sup_and : forall G T T1 T2,
    all_sup G T T1 ->
    all_sup G T T2 ->
    all_sup G T (typ_and T1 T2)
| all_sup_sel : forall G T x A U S,
    G ⊢! x : U ⪼ typ_rcd (dec_typ A S S) ->
    all_sup G T S ->
    all_sup G T (typ_sel (avar_f x) A)
| all_sup_all : forall L G S1 T1 S2 T2,
    G ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    all_sup G (typ_all S1 T1) (typ_all S2 T2).
Local Hint Constructors all_sup.

Lemma all_sup_refl: forall G S T,
    all_sup G (typ_all S T) (typ_all S T).
Proof.
  intros. apply_fresh all_sup_all as z; auto.
Qed.
Local Hint Resolve all_sup_refl.

Lemma tight_all_sup: forall G S T U1 U2,
    inert G ->
    G ⊢# U1 <: U2 ->
    all_sup G (typ_all S T) U1 ->
    all_sup G (typ_all S T) U2.
Proof.
  introv Hi H.
  dependent induction H; intros; auto;
    match goal with
    | |- all_sup _ _ (typ_sel (avar_f _) _) =>
      eauto
    | [ H : all_sup _ _ _ |- _ ] =>
      try solve [inversions H; auto]
    end.
  - inversions H0; auto.
    replace U0 with U in * by eauto.
    replace S0 with T0 in * by eauto.
    auto.
  - pose proof ((proj2 tight_to_general) _ _ _ H);
    inversions H1; apply_fresh all_sup_all as z.
    + eauto.
    + assert (G & z ~ S2 ⊢ open_typ z T <: open_typ z T1)
        by apply* narrow_subtyping; eauto.
Qed.

Lemma inert_subtyping: forall G,
  inert G ->
  (forall T S U, ~ G ⊢ (typ_bnd T) <: (typ_all S U)) /\
  (forall T S U, ~ G ⊢ (typ_all S U) <: (typ_bnd T)).
Proof.
  introv Hi; split; introv H.
  - apply (proj2 (general_to_tight Hi)) in H; auto.
    assert (Contra: bnd_sup G (typ_bnd T) (typ_all S U))
      by eauto using tight_bnd_sup.
    inversion Contra.
  - apply (proj2 (general_to_tight Hi)) in H; auto.
    assert (Contra: all_sup G (typ_all S U) (typ_bnd T))
      by eauto using tight_all_sup.
    inversions Contra.
Qed.
