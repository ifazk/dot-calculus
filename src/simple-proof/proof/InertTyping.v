Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Definitions GeneralToTight InvertibleTyping Narrowing PreciseTyping RecordAndInertTypes
            Subenvironments Substitution TightTyping.

(** * Simple Implications of Typing *)

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma typing_implies_bound: forall G x T,
  G ⊢ trm_var (avar_f x) : T ->
  exists S, binds x S G.
Proof.
  introv Ht. dependent induction Ht; eauto.
Qed.

Lemma new_typing: forall G T ds U,
    (G ⊢ (trm_new T ds) : U) ->
    exists L, forall z, z \notin L ->
              G & z ~ open_typ z T /- (open_defs z ds) :: open_typ z T.
Proof.
  introv H.
  dependent induction H.
  - exists L; auto.
  - apply* IHty_trm.
Qed.

Lemma new_typing_super: forall G T ds U,
    (G ⊢ (trm_new T ds) : U) ->
    (G ⊢ (typ_bnd T) <: U).
Proof.
  introv H.
  dependent induction H; auto.
  pose proof (IHty_trm T ds eq_refl).
  eauto using subtyp_trans.
Qed.

(** [G ⊢##v v: forall(S)T]                 #<br>#
    [inert G]                          #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [exists S', T', G ⊢! v: forall(S')T']      #<br>#
    [G ⊢ S <: S']                      #<br>#
    [forall fresh y, G, y: S ⊢ T'^y <: T^y] *)
Lemma invertible_val_to_precise_lambda: forall G v S T,
    inert G ->
    G ⊢##v v : typ_all S T ->
    exists L S' T',
      G ⊢!v v : typ_all S' T' /\
      G ⊢ S <: S' /\
      (forall y, y \notin L ->
                 G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Hi Ht. dependent induction Ht.
  - exists (dom G) S T. split*.
  - destruct (IHHt S0 T0 Hi eq_refl) as [L' [S1 [T1 [Hp [Hss Hst]]]]].
    exists (L \u L' \u dom G) S1 T1. split. assumption. split. apply subtyp_trans with (T:=S0).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ S)) as Hok. {
      apply* ok_push.
    }
    apply subtyp_trans with (T:=open_typ y T0).
    eapply narrow_subtyping. apply* Hst. apply subenv_last. apply* tight_to_general.
    assumption.
    apply* H0.
Qed.

(** This lemma corresponds to Lemma 3.7 ([forall] to [G(x)]) in the paper.

    [inert G]            #<br>#
    [G ⊢ x: forall(T)U]       #<br>#
    [――――――――――――――-]    #<br>#
    [exists T', U',]          #<br>#
    [G(x) = forall(T')U']     #<br>#
    [G ⊢ T <: T']        #<br>#
    [forall fresh y, G, y: T ⊢ U'^y <: U^y] *)
Lemma var_typ_all_to_binds: forall G x T U,
    inert G ->
    G ⊢ trm_var (avar_f x) : typ_all T U ->
    (exists L T' U',
        binds x (typ_all T' U') G /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_all (inert_ok Hin) Hinv) as [T' [U' [V' [L [Htp [Hs1 Hs2]]]]]].
  exists L T' U'. repeat split.
  - apply* inert_precise_all_inv.
  - apply~ tight_to_general.
  - assumption.
Qed.

(** This lemma corresponds to Lemma 3.8 ([forall] to [lambda]) in the paper.

    [inert G]                       #<br>#
    [G ⊢ v: forall(T)U]                  #<br>#
    [――――――――――――]                  #<br>#
    [exists T', t,]                       #<br>#
    [v = lambda(T')t]              #<br>#
    [G ⊢ T <: T']                   #<br>#
    [forall fresh y, G, y: T ⊢ t^y: U^y] *)
Lemma val_typ_all_to_lambda: forall G v T U,
    inert G ->
    G ⊢ trm_val v : typ_all T U ->
    (exists L T' t,
        v = val_fun T' t /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_trm y t) : open_typ y U)).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible_v _ Hin Htt).
  destruct (invertible_val_to_precise_lambda Hin Hinv) as [L [T' [U' [Htp [Hs1 Hs2]]]]].
  inversions Htp.
  exists (L0 \u L \u (dom G)) T' t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H2 y HL0).
  eapply ty_sub; eauto. eapply narrow_typing in H2; eauto.
Qed.

(** [d1 isin ds]             #<br>#
    [label(d2) \notin ds]     #<br>#
    [―――――――――――――――――――――]  #<br>#
    [label(d1) <> label(d2)]  *)
Lemma defs_has_hasnt_neq: forall ds d1 d2,
  defs_has ds d1 ->
  defs_hasnt ds (label_of_def d2) ->
  label_of_def d1 <> label_of_def d2.
Proof.
  introv Hhas Hhasnt.
  unfold defs_has in Hhas.
  unfold defs_hasnt in Hhasnt.
  induction ds.
  - simpl in Hhas. inversion Hhas.
  - simpl in Hhasnt. simpl in Hhas. case_if; case_if.
    + inversions Hhas. assumption.
    + apply IHds; eauto.
Qed.

(** [G ⊢ ds :: ... /\ D /\ ...]       #<br>#
    [―――――――――――――――――――――――]       #<br>#
    [exists d, ds = ... /\ d /\ ...]       #<br>#
    [G ⊢ d: D]                      *)
Lemma record_has_ty_defs: forall G T ds D,
  G /- ds :: T ->
  record_has T D ->
  exists d, defs_has ds d /\ G /- d : D.
Proof.
  introv Hdefs Hhas. induction Hdefs.
  - inversion Hhas; subst. exists d. split.
    + unfold defs_has. simpl. rewrite If_l; reflexivity.
    + assumption.
  - inversion Hhas; subst.
    + destruct (IHHdefs H4) as [d' [H1 H2]].
      exists d'. split.
      * unfold defs_has. simpl. rewrite If_r. apply H1.
        apply not_eq_sym. eapply defs_has_hasnt_neq; eauto.
      * assumption.
    + exists d. split.
      * unfold defs_has. simpl. rewrite If_l; reflexivity.
      * inversions* H4.
Qed.

(** This lemma corresponds to Lemma 3.9 ([mu] to [G(x)]) in the paper.

    [inert G]                    #<br>#
    [G ⊢ x: {a: T}]              #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [exists S, T', G(x) = mu(S)]       #<br>#
    [S^x = ... /\ {a: T'} /\ ...]  #<br>#
    [G ⊢ T' <: T]                *)
Lemma var_typ_rcd_to_binds: forall G x a T,
    inert G ->
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    (exists S T',
        binds x (typ_bnd S) G /\
        record_has (open_typ x S) (dec_trm a T') /\
        G ⊢ T' <: T).
Proof.
  introv Hin Ht.
  destruct (typing_implies_bound Ht) as [S BiG].
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_trm_dec Hinv) as [T' [U [Htp Hs]]].
  destruct (pf_inert_rcd_U Hin Htp) as [U' Hr]. subst.
  lets Hr': (precise_flow_record_has Hin Htp). apply pf_binds in Htp.
  exists U' T'. split. assumption. split. assumption. apply* tight_to_general.
Qed.

(** This lemma corresponds to Lemma 3.10 ([mu] to [nu]) in the paper.

    [inert G]                  #<br>#
    [G ⊢ v: mu(T)]             #<br>#
    [G ⊢ x: T^x]               #<br>#
    [T = ... /\ {a: U} /\ ...  ] #<br>#
    [――――――――――――――――――――――――] #<br>#
    [exists t, ds, v = nu(T)ds     ] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: U] *)
Lemma val_mu_to_new: forall G v T U a x,
    inert G ->
    G ⊢ trm_val v: typ_bnd T ->
    G ⊢ trm_var (avar_f x) : open_typ x T ->
    record_has (open_typ x T) (dec_trm a U) ->
    exists t ds,
      v = val_obj T ds /\
      defs_has (open_defs x ds) (def_trm a t) /\
      G ⊢ t: U.
Proof.
  introv Hi Ht Hx Hr.
  lets Htt: (general_to_tight_typing Hi Ht).
  lets Hinv: (tight_to_invertible_v _ Hi Htt).
  inversions Hinv. inversions H.
  pick_fresh z. assert (z \notin L) as Hz by auto.
  specialize (H3 z Hz).
  assert (G /- open_defs x ds :: open_typ x T) as Hds by apply* renaming_def.
  destruct (record_has_ty_defs Hds Hr) as [d [Hh Hd]]. inversions Hd.
  exists t ds. split*.
Qed.
