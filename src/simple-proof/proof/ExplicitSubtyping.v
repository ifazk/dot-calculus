Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions RecordAndInertTypes PreciseTyping
        TightTyping GeneralToTight.

Reserved Notation "G '⊢%' T '<:b' U" (at level 40, T at level 59).
Reserved Notation "G '⊢%' T '<:s' U" (at level 40, T at level 59).
Reserved Notation "G '⊢%' T '<:i' U" (at level 40, T at level 59).
Reserved Notation "G '⊢%' T '<:d' U" (at level 40, T at level 59).
Reserved Notation "G '⊢%' T '<:f' U" (at level 40, T at level 59).
Reserved Notation "G '⊢%' T '<:e' U" (at level 40, T at level 59).

Inductive basic_subtyp : ctx -> typ -> typ -> Prop :=
| subtyp_top_e: forall G T,
    G ⊢% T <:b typ_top

(** [G ⊢% bot <: T] *)
| subtyp_bot_e: forall G T,
    G ⊢% typ_bot <:b T

(** [G ⊢% T <: T] *)
| subtyp_refl_e: forall G T,
    G ⊢% T <:b T

where "G '⊢%' T '<:b' U" := (basic_subtyp G T U).

Inductive sel_subtyp : ctx -> typ -> typ -> Prop :=
| subtyp_sel2_e: forall G x A T U,
    G ⊢! x : U ⪼ typ_rcd (dec_typ A T T) ->
    G ⊢% T <:s typ_sel (avar_f x) A

| subtyp_sel1_e: forall G x A T U,
    G ⊢! x : U ⪼ typ_rcd (dec_typ A T T) ->
    G ⊢% typ_sel (avar_f x) A <:s T
where "G '⊢%' T '<:s' U" := (sel_subtyp G T U).

Inductive inter_subtyp : ctx -> typ -> typ -> Prop :=
| subtyp_and11_e: forall G T U,
    G ⊢% typ_and T U <:i T

| subtyp_and12_e: forall G T U,
    G ⊢% typ_and T U <:i U

| subtyp_and2_e: forall G S T U,
    G ⊢% S <:e T ->
    G ⊢% S <:e U ->
    G ⊢% S <:i typ_and T U

where "G '⊢%' T '<:i' U" := (inter_subtyp G T U)

with dec_subtyp : ctx -> typ -> typ -> Prop :=
| subtyp_fld_e: forall G a T U,
    G ⊢% T <:e U ->
    G ⊢% typ_rcd (dec_trm a T) <:d typ_rcd (dec_trm a U)

| subtyp_typ_e: forall G A S1 T1 S2 T2,
    G ⊢% S2 <:e S1 ->
    G ⊢% T1 <:e T2 ->
    G ⊢% typ_rcd (dec_typ A S1 T1) <:d typ_rcd (dec_typ A S2 T2)
where "G '⊢%' T '<:d' U" := (dec_subtyp G T U)

with fun_subtyp : ctx -> typ -> typ -> Prop :=
| subtyp_all_e: forall L G S1 T1 S2 T2,
    G ⊢% S2 <:e S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢% typ_all S1 T1 <:f typ_all S2 T2

where "G '⊢%' T '<:f' U" := (fun_subtyp G T U)

with explicit_subtyp : ctx -> typ -> typ -> Prop :=
| basic_e : forall G T1 T2,
    G ⊢% T1 <:b T2 ->
    G ⊢% T1 <:e T2

| sel_e : forall G T1 T2,
    G ⊢% T1 <:s T2 ->
    G ⊢% T1 <:e T2

| inter_e : forall G T1 T2,
    G ⊢% T1 <:i T2 ->
    G ⊢% T1 <:e T2

| dec_e : forall G T1 T2,
    G ⊢% T1 <:d T2 ->
    G ⊢% T1 <:e T2

| fun_e : forall G T1 T2,
    G ⊢% T1 <:f T2 ->
    G ⊢% T1 <:e T2

| subtyp_trans_e: forall G S T U,
    G ⊢% S <:e T ->
    G ⊢% T <:e U ->
    G ⊢% S <:e U

where "G '⊢%' T '<:e' U" := (explicit_subtyp G T U).

Hint Constructors
     basic_subtyp sel_subtyp
     inter_subtyp dec_subtyp
     fun_subtyp explicit_subtyp.

Scheme isub_mut := Induction for inter_subtyp Sort Prop
with   dsub_mut := Induction for dec_subtyp Sort Prop
with   fsub_mut := Induction for fun_subtyp Sort Prop
with   esub_mut := Induction for explicit_subtyp Sort Prop.

Combined Scheme esub_mutind from
         isub_mut, dsub_mut,
         fsub_mut, esub_mut.

Lemma tight_to_explicit: forall G T1 T2,
    G ⊢# T1 <: T2 ->
    G ⊢% T1 <:e T2.
Proof.
  introv H. induction H; eauto.
Qed.

Lemma basic_to_tight: forall G T1 T2,
    G ⊢% T1 <:b T2 ->
    G ⊢# T1 <: T2.
Proof.
  introv H; induction H; auto.
Qed.

Lemma sel_to_tight: forall G T1 T2,
    G ⊢% T1 <:s T2 ->
    G ⊢# T1 <: T2.
Proof.
  introv H; induction H; eauto.
Qed.

Lemma explicit_to_tight:
  (forall G T1 T2, G ⊢% T1 <:i T2 -> G ⊢# T1 <: T2) /\
  (forall G T1 T2, G ⊢% T1 <:d T2 -> G ⊢# T1 <: T2) /\
  (forall G T1 T2, G ⊢% T1 <:f T2 -> G ⊢# T1 <: T2) /\
  (forall G T1 T2, G ⊢% T1 <:e T2 -> G ⊢# T1 <: T2).
Proof.
  apply esub_mutind; eauto using basic_to_tight, sel_to_tight.
Qed.

Inductive typ_all_dec_bot_free : ctx -> typ -> Prop :=
| tab_free_top : forall G,
    typ_all_dec_bot_free G typ_top
| tab_free_and : forall G T1 T2,
    typ_all_dec_bot_free G T1 ->
    typ_all_dec_bot_free G T2 ->
    typ_all_dec_bot_free G (typ_and T1 T2)
| tab_free_sel : forall G x A U T,
    G ⊢! x : U ⪼ typ_rcd (dec_typ A T T) ->
    typ_all_dec_bot_free G T ->
    typ_all_dec_bot_free G (typ_sel (avar_f x) A)
| tab_free_bnd : forall G T,
    typ_all_dec_bot_free G (typ_bnd T).

Hint Constructors typ_all_dec_bot_free.

Lemma basic_tadb_free_super: forall G T1 T2,
    G ⊢% T1 <:b T2 ->
    typ_all_dec_bot_free G T1 ->
    typ_all_dec_bot_free G T2.
Proof.
  introv H; inversions H; auto.
  introv H; inversions H.
Qed.

Lemma explicit_tadb_free_super:
  (forall G T1 T2,
      G ⊢% T1 <:i T2 ->
      inert G ->
      typ_all_dec_bot_free G T1 ->
      typ_all_dec_bot_free G T2) /\
  (forall G T1 T2,
      G ⊢% T1 <:d T2 ->
      inert G ->
      typ_all_dec_bot_free G T1 ->
      typ_all_dec_bot_free G T2) /\
  (forall G T1 T2,
      G ⊢% T1 <:f T2 ->
      inert G ->
      typ_all_dec_bot_free G T1 ->
      typ_all_dec_bot_free G T2) /\
  (forall G T1 T2,
      G ⊢% T1 <:e T2 ->
      inert G ->
      typ_all_dec_bot_free G T1 ->
      typ_all_dec_bot_free G T2).
Proof.
  apply esub_mutind; try solve [intros;
    match goal with
    | [ H : typ_all_dec_bot_free _ _ |- _ ] =>
      inversions H; eauto
    end]; eauto using basic_tadb_free_super.
  - intros. inversions s; auto.
    inversions H0; eauto.
    inversions H0; eauto.
    pose proof (x_bound_unique H1 H5); subst U0.
    pose proof (pf_inert_unique_tight_bounds H H1 H5); subst T2.
    auto.
Qed.

Lemma inert_bnd_subtyp_all_inv : forall G T S U,
    inert G ->
    G ⊢ (typ_bnd T) <: (typ_all S U) ->
    False.
Proof.
  intros.
  apply (proj2 (general_to_tight H)) in H0; auto.
  apply tight_to_explicit in H0.
  assert (typ_all_dec_bot_free G (typ_bnd T)) by auto.
  apply ((proj44 explicit_tadb_free_super) _ _ _ H0 H) in H1.
  inversion H1.
Qed.

Inductive typ_bnd_dec_bot_free : ctx -> typ -> Prop :=
| tdbd_free_top : forall G,
    typ_bnd_dec_bot_free G typ_top
| tdbd_free_and : forall G T1 T2,
    typ_bnd_dec_bot_free G T1 ->
    typ_bnd_dec_bot_free G T2 ->
    typ_bnd_dec_bot_free G (typ_and T1 T2)
| tdbd_free_sel : forall G x A U T,
    G ⊢! x : U ⪼ typ_rcd (dec_typ A T T) ->
    typ_bnd_dec_bot_free G T ->
    typ_bnd_dec_bot_free G (typ_sel (avar_f x) A)
| tdbd_free_all : forall G T1 T2,
    typ_bnd_dec_bot_free G (typ_all T1 T2).

Hint Constructors typ_bnd_dec_bot_free.

Lemma basic_tbdb_free_super: forall G T1 T2,
    G ⊢% T1 <:b T2 ->
    typ_bnd_dec_bot_free G T1 ->
    typ_bnd_dec_bot_free G T2.
Proof.
  introv H; inversions H; auto.
  introv H; inversions H.
Qed.

Lemma explicit_tbdb_free_super:
  (forall G T1 T2,
      G ⊢% T1 <:i T2 ->
      inert G ->
      typ_bnd_dec_bot_free G T1 ->
      typ_bnd_dec_bot_free G T2) /\
  (forall G T1 T2,
      G ⊢% T1 <:d T2 ->
      inert G ->
      typ_bnd_dec_bot_free G T1 ->
      typ_bnd_dec_bot_free G T2) /\
  (forall G T1 T2,
      G ⊢% T1 <:f T2 ->
      inert G ->
      typ_bnd_dec_bot_free G T1 ->
      typ_bnd_dec_bot_free G T2) /\
  (forall G T1 T2,
      G ⊢% T1 <:e T2 ->
      inert G ->
      typ_bnd_dec_bot_free G T1 ->
      typ_bnd_dec_bot_free G T2).
Proof.
  apply esub_mutind; try solve [intros;
    match goal with
    | [ H : typ_bnd_dec_bot_free _ _ |- _ ] =>
      inversions H; eauto
    end]; eauto using basic_tbdb_free_super.
  - intros. inversions s; auto.
    inversions H0; eauto.
    inversions H0; eauto.
    pose proof (x_bound_unique H1 H5); subst U0.
    pose proof (pf_inert_unique_tight_bounds H H1 H5); subst T2.
    auto.
Qed.

Lemma inert_all_subtyp_bnd_inv : forall G T S U,
    inert G ->
    G ⊢ (typ_all S U) <: (typ_bnd T) ->
    False.
Proof.
  intros.
  apply (proj2 (general_to_tight H)) in H0; auto.
  apply tight_to_explicit in H0.
  assert (typ_bnd_dec_bot_free G (typ_all S U)) by auto.
  apply ((proj44 explicit_tbdb_free_super) _ _ _ H0 H) in H1.
  inversion H1.
Qed.

Lemma tight_tbdb_free_super: forall G T1 T2,
    inert G ->
    G ⊢# T1 <: T2 ->
    typ_bnd_dec_bot_free G T1 ->
    typ_bnd_dec_bot_free G T2.
Proof.
  introv Hi Ht; induction Ht;
    try solve[ intros;
    match goal with
    | [ H : typ_bnd_dec_bot_free _ _ |- _ ] =>
      inversions H; eauto
    end]; eauto.
  intros. inversions H0; auto.
  pose proof (x_bound_unique H H4); subst U0.
  pose proof (pf_inert_unique_tight_bounds Hi H H4); subst T0.
  auto.
Qed.
