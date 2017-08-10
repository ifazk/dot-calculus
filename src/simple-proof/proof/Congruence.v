Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Narrowing.
Require Import Helper_lemmas.
Require Import Precise_types.
Require Import Substitution.
Require Import Canonical_forms.

Fixpoint congruence (e : ec) (t : trm) (k : nat) : (option (ec * trm)) :=
  match k with
  | 0 => None
  | S n =>
    match e with
    | e_hole s =>
      match t with
      | trm_let t u => congruence (e_term s u) t n
      | _ => Some (e, t)
      end
    | e_term s u =>
      match t with
      | trm_val v =>
        let x := (var_gen (dom s)) in
        congruence (e_hole (s & x ~ v)) (open_trm x t) n
      | _ => Some (e, t)
      end
    end
  end.

Inductive red_congruence : ec -> trm -> ec -> trm -> Prop :=
(** [e[ ] | let x = t in u |-> e[let x = [ ] in u] | t] *)
| red_congruence_let' : forall s t u,
    red_congruence (e_hole s) (trm_let t u) (e_term s u) t
(** [e[let x = [ ] in t] | v |-> e[let x = v in [ ]] | t^x] *)
| red_congruence_val' : forall s v t,
    let x := (var_gen (dom s)) in
    red_congruence (e_term s t) (trm_val v) (e_hole (s & (x ~ v))) (open_trm x t).

Lemma congruence_deterministic: forall e t e' t' e'' t'',
    red_congruence e t e' t' ->
    red_congruence e t e'' t'' ->
    e' = e'' /\ t' = t''.
Proof.
  intros. inversions H; inversions H0; auto.
Qed.

Fixpoint double_num_lets (t : trm) : nat :=
  match t with
  | trm_let t u => 2 * (1 + (double_num_lets t) + (double_num_lets u))
  | _ => 0
  end.

Definition double_num_lets_pair (e : ec) (t : trm) : nat :=
  match e with
  | e_hole _ => double_num_lets t
  | e_term _ u => 2 + (double_num_lets t) + (double_num_lets u)
  end.

Lemma congruence_max: forall e t e' t' e'' t'',
    congruence e t (double_num_lets_pair e t) = Some (e', t') ->
    red_congruence e' t' e'' t'' ->
    False.
Proof.
  intros. destruct t; destruct e; simpl in *; try solve [inversions H; inversions H0].
  - destruct (double_num_lets t1 + double_num_lets t2 + S (double_num_lets t1 + double_num_lets t2 + 0)); inversions H.
    destruct t1; inversions H2; try solve [inversions H0].
    destruct n; inversions H1. inversions H0.
Qed.
