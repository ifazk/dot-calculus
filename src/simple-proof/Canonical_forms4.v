Set Implicit Arguments.

Require Import LibMap LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Some_lemmas.
Require Import Inert_types.
Require Import General_to_tight.
Require Import Invertible_typing.
Require Import Canonical_forms3.

Lemma canonical_forms_4: forall G S sta sto x T,
  inert G ->
  G, S |~ sta, sto ->
  G, S |- trm_var (avar_f x) : typ_nref T ->
  (exists l,
      binds x (val_loc l) sta /\
      G, S |- trm_val (val_loc l) : typ_nref T /\
      (bindsM l None sto \/ (exists y, bindsM l (Some y) sto /\ G, S |- trm_var (avar_f y) : T))).
Proof. 
  introv Hin Hwf Hty.
  pose proof (typing_implies_bound Hty) as [V Bi].
  pose proof (general_to_tight_typing Hin Hty) as Hty'.
  pose proof (invertible_typing_lemma Hin Hty') as Hinv.
  pose proof (invertible_to_precise_typ_nref Hin Hinv) as [T' [Hx [Hs1 Hs2]]].
  pose proof (corresponding_types Hwf Hin Bi)
    as [[L [U [W [S1 [W1 [t [Hb [Ht [Heq _]]]]]]]]] | [[U [ds [Hb [Ht Heq]]]] | [U [U' [l [Hb [Ht [Heq [Hs1' Hs2']]]]]]]]].
  - assert (H: exists T, record_type T /\ V = (typ_bnd T)).
    { pose proof (binds_inert Bi Hin) as HinT.
      induction HinT.
      - destruct Hx as [Hx | Hx]. 
        { 
          destruct (precise_flow_lemma Hx) as [W' H].
          pose proof (pf_binds H). apply (binds_func Bi) in H0.
          apply pf_inert_nref_U in H. subst. inversion H0. assumption.
        }
        {
          destruct (precise_flow_lemma Hx) as [W' H].
          pose proof (pf_binds H). apply (binds_func Bi) in H0.
          apply pf_inert_ref_U in H. subst. inversion H0. assumption.
        } 
      - exists T0. auto.
      - inversion Heq. 
      - inversion Heq.
    }
    destruct H as [T0 [Hrt Hsubst]]; subst V; rename T0 into V.
    inversion Hsubst.
  - pose proof (binds_inert Bi Hin) as Hgt.
    induction Hgt.
    + inversion Heq.
    + 
      destruct Hx as [Hx | Hx]. 
      { 
        pose proof (precise_flow_lemma Hx) as [W' H'].
        pose proof (pf_binds H'). apply (binds_func Bi) in H0.
        apply pf_inert_nref_U in H'. subst. inversion H0. assumption.
      }
      { 
        pose proof (precise_flow_lemma Hx) as [W' H'].
        pose proof (pf_binds H'). apply (binds_func Bi) in H0.
        apply pf_inert_ref_U in H'. subst. inversion H0. assumption.
      }
    + inversion Heq.
    + inversion Heq.
  - subst. 
    remember Ht as Ht'. inversions Ht'. 
    destruct Heq; subst.
    { (* nref *)
      destruct Hx as [Hx | Hx].
      { (* nref *)
        pose proof (precise_flow_lemma Hx).
        destruct H as [V Hpf]. pose proof (pf_inert_nref_U Hin Hpf). subst.
        apply pf_binds in Hpf. apply (binds_func Hpf) in Bi. 
        inversions Bi.
        exists l. repeat split.
        - assumption.
        - apply precise_to_general in Ht. 
          apply tight_to_general in Hs1. 
          apply tight_to_general in Hs2. 
          pose proof (subtyp_nref Hs1' Hs2').
          apply (ty_sub Ht) in H.
          pose proof (subtyp_nref Hs1 Hs2).
          apply (ty_sub H H0).
        - pose proof (test4 Hin Hwf Hpf Hb H3) as [Hsto | [y [Hsto Hy]]].
          + left. assumption.
          + right. exists y. split. 
            * assumption.
            * apply tight_to_general in Hs1.
              pose proof (ty_sub Hy Hs1').
              apply (ty_sub H Hs1).
      }
      { (* ref *)
        pose proof (precise_flow_lemma Hx).
        destruct H as [V Hpf]. pose proof (pf_inert_ref_U Hin Hpf). subst.
        apply pf_binds in Hpf. apply (binds_func Hpf) in Bi. 
        inversions Bi.
      } 
    } 
    { (* ref *)
      pose proof (test Hin Hwf Bi H3 Hb) as [y [Biy Hy]].
      destruct Hx as [Hx | Hx].
      { (* nref *)
        pose proof (precise_flow_lemma Hx).
        destruct H as [V Hpf]. pose proof (pf_inert_nref_U Hin Hpf). subst.
        apply pf_binds in Hpf. apply (binds_func Hpf) in Bi. 
        inversions Bi. 
      }
      { (* ref *)
        pose proof (precise_flow_lemma Hx).
        destruct H as [V Hpf]. pose proof (pf_inert_ref_U Hin Hpf). subst.
        apply pf_binds in Hpf. apply (binds_func Hpf) in Bi. 
        inversions Bi.
        exists l. repeat split.
        - assumption.
        - apply precise_to_general in Ht. 
          apply tight_to_general in Hs1. 
          apply tight_to_general in Hs2. 
          pose proof (subtyp_nref Hs1' Hs2').
          apply (ty_sub Ht) in H.
          pose proof (subtyp_nref Hs1 Hs2).
          apply (ty_sub H H0).
        - right. exists y. split.
          + assumption.
          + apply tight_to_general in Hs1.
            pose proof (ty_sub Hy Hs1').
            apply (ty_sub H Hs1).
      }
    }      
Qed.
