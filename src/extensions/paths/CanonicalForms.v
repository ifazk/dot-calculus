(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module proves the Canonical Forms Lemmas, which allow us
    to retrieve the shape of a value given its type. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import LibLN.
Require Import Binding Definitions GeneralToTight InvertibleTyping Lookup Narrowing PreciseTyping
        RecordAndInertTypes Substitution Subenvironments TightTyping Weakening.
Require Import Sequences.

(** * Well-typedness *)

(** If [e: G], the variables in the domain of [e] are distinct. *)
Lemma well_typed_to_ok_G: forall s G,
    well_typed G s -> ok G.
Proof.
  intros. induction H; jauto.
Qed.
Hint Resolve well_typed_to_ok_G.

(** [s: G]       #<br>#
    [x ∉ dom(G)] #<br>#
    [――――――――――] #<br>#
    [x ∉ dom(s)] *)
Lemma well_typed_notin_dom: forall G s x,
    well_typed G s ->
    x # s ->
    x # G.
Proof.
  intros. induction H; auto.
Qed.

Lemma val_typing: forall G v T,
  G ⊢ trm_val v : T ->
  exists T', G ⊢!v v : T' /\
        G ⊢ T' <: T.
Proof.
  intros G v T H. dependent induction H; eauto.
  destruct (IHty_trm _ eq_refl). destruct_all. eauto.
Qed.

(** [G ~ s]                 #<br>#
    [G ⊢ p: T]              #<br>#
    [―――――――――――――――――――――] #<br>#
    [exists P v, P ⊢ s ∋ (p, v)] *)
Lemma typed_path_lookup : forall G s p T,
    inert G ->
    well_typed G s ->
    G ⊢ trm_path p: T ->
    exists v, s ∋ (p, v).
Proof.
  introv Hi Hwt. gen p T. induction Hwt; introv Hp.
  - false* typing_empty_false.
  - proof_recipe. dependent induction Hp; eauto. dependent induction H2; eauto.
    * destruct (binds_push_inv H0) as [[Heq1 Heq2] | [Hneq Hb]].
      subst. exists v. constructor. apply star_one. constructor*.
      apply inert_prefix in Hi. lets Hok': (inert_ok Hi).
      lets Ht: (ty_var Hb Hok'). unfolds tvar.  specialize (IHHwt Hi _ _ Ht).
      destruct_all. exists x1. constructor. apply* lookup_push_neq. inversion* H4.
    * specialize (IHprecise_flow _ _ _ JMeq_refl H0 Hi Hwt H H1 IHHwt Hok).
      destruct IHprecise_flow as [v' Hl].
      inversions Hl. dependent induction H5.

Lemma lookup_step_preservation_prec: forall G s p T T' t,
    inert G ->
    well_typed G s ->
    s ⟦ trm_path p ⟼ t ⟧ ->
    G ⊢! p : T ⪼ T' ->
    G ⊢ t: T.
Proof.
  introv Hi Hwt Hs Hp. gen T' T p t. induction Hwt; introv Hp Hs.
  - false* lookup_empty.
  - destruct p as [y bs].
    (* showing that y is named *)
    lets Hg: (precise_to_general Hp). apply typed_paths_named in Hg. inversions Hg.
    destruct_all. inversions H2.
    destruct (classicT (x = x0)).
    * subst. rename x1 into bs. gen t v. dependent induction Hp; introv Hv Hs.
      + Case "pf_bind".
        apply binds_push_eq_inv in H1. subst.
        assert (p_sel (avar_f x0) nil = pvar x0) as Heq by auto. rewrite Heq in Hs.
        apply lookup_push_eq_inv_var in Hs. destruct_all. subst.
        apply* weaken_ty_trm.
      + Case "pf_fld".
        unfolds sel_fields. destruct p. inversions x.
        inversions Hs; unfolds sel_fields; simpls. destruct p. inversions H1.
        inversions H2. specialize (IHHp _ _ H0 _ _ Hi Hwt H IHHwt eq_refl JMeq_refl _ _ Hv H1).
        apply (general_to_tight_typing Hi) in IHHp. apply (tight_to_invertible_v Hi) in IHHp.
        assert (inert_typ T0) as HT0 by apply* pf_inert_T.
        lets Heq: (invertible_to_precise_v_obj IHHp HT0). subst. inversions IHHp.
        inversions H2.
      (* deal with renaming *)
        assert (x0; f; P; G & x0 ~ T ⊢
                                 open_defs_p (p_sel (avar_f x0) f) ds0 :: open_typ_p (p_sel (avar_f x0) f) T1)
          as Hds by admit.
        lets Hrh: (precise_flow_record_has Hi Hp).
        destruct (record_has_ty_defs Hds Hrh) as [d [Hd Ht]].
        lets Hdt: (defs_has_typing Ht). destruct Hdt as [t' Heq]. subst.
        lets Heq: (defs_has_inv Hd H4). subst. dependent induction Ht; eauto.
      (* fresh_constructor; deal with renaming #2 *)
        admit.
      + Case "pf_open".
        eauto.
      + Case "pf_and1".
        eauto.
      + Case "pf_and2".
        eauto.
   * apply pf_strengthen in Hp; auto.
     assert (inert G) as Hi' by apply* inert_prefix.
     lets Hn: (lookup_strengthen Hs n). apply* weaken_ty_trm.
Qed.

(** * Lemmas to Prove Canonical Forms for Functions *)

Lemma lookup_preservation_typ_all : forall G s t u T S,
    inert G ->
    well_typed G s ->
    star (lookup_step s) t u ->
    G ⊢ t : typ_all S T ->
    G ⊢ u: typ_all S T.
Proof.
  introv Hi Hwt Hl Hp. dependent induction Hl; auto.
  destruct (lookup_inv_path_t H) as [p Heq]. subst.
  proof_recipe.
  lets Hlp: (lookup_step_preservation_prec Hi Hwt H Hpr).
  lets Heq: (pf_inert_lambda_U Hi Hpr). subst.
  apply ty_sub with (U:=typ_all S T) in Hlp. apply* IHHl.
  fresh_constructor. apply* tight_to_general.
Qed.

Lemma corresponding_types_fun: forall G s p S T T',
    inert G ->
    well_typed G s ->
    G ⊢! p: typ_all S T ⪼ T' ->
    (exists v, s ∋ (p, v) /\
            G ⊢ trm_val v : typ_all S T).
Proof.
  introv Hi Hwt Hp.
  apply pf_precise_U in Hp.
  lets Hg: (precise_to_general Hp).
  destruct (typed_path_lookup Hi Hwt Hg) as [v Hs].
  lets Hi': (pf_inert_T Hi Hp). inversions Hs.
  lets Ht: (lookup_preservation_typ_all Hi Hwt H1 Hg). eauto.
Qed.

(** [G ⊢##v v: forall(S)T]                 #<br>#
    [inert G]                          #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [exists S', T', G ⊢! v: forall(S')T']      #<br>#
    [G ⊢ S <: S']                      #<br>#
    [forall fresh y, G, y: S ⊢ T'^y <: T^y] *)
Lemma invertible_val_to_precise_lambda: forall G v S T,
    G ⊢##v v : typ_all S T ->
    inert G ->
    exists L S' T',
      G ⊢!v v : typ_all S' T' /\
      G ⊢ S <: S' /\
      (forall y, y \notin L ->
                 G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Ht Hg. dependent induction Ht.
  - exists (dom G) S T. split*.
  - destruct (IHHt _ _ eq_refl Hg) as [L' [S' [T' [Hp [Hss Hst]]]]].
    exists (L \u L' \u dom G) S' T'. split. assumption. split. apply subtyp_trans with (T:=S1).
    apply* tight_to_general. assumption. intros.
    assert (ok (G & y ~ S)) as Hok by apply* ok_push.
    apply subtyp_trans with (T:=open_typ y T1).
    * eapply narrow_subtyping. apply* Hst. apply subenv_last. apply* tight_to_general. auto.
    * apply* H0.
Qed.

(** [forall] to [G(x)]        #<br>#
    [inert G]            #<br>#
    [G ⊢ p: forall(T)U]       #<br>#
    [――――――――――――――--]   #<br>#
    [exists T', U',]          #<br>#
    [G ∋ (p, forall(T')U')]   #<br>#
    [G ⊢ T <: T']        #<br>#
    [forall fresh y, G, y: T ⊢ U'^y <: U^y] *)
Lemma var_typ_all_to_binds: forall G p T U,
    inert G ->
    G ⊢ trm_path p : typ_all T U ->
    (exists L V T' U',
        G ⊢! p : typ_all T' U' ⪼ V /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_all (inert_ok Hin) Hinv) as [T' [U' [V [L [Htp [Hs1 Hs2]]]]]].
  exists L V T' U'. repeat split.
  lets Hv: (pf_inert_lambda_U Hin Htp). subst*. apply* tight_to_general. eauto.
Qed.

(** [forall] to [lambda]                 #<br>#
    [inert G]                       #<br>#
    [G ⊢ v: forall(T)U]                  #<br>#
    [――――――――――――]                  #<br>#
    [exists T', t,]                      #<br>#
    [v = lambda(T')t]               #<br>#
    [G ⊢ T <: T']                   #<br>#
    [forall fresh y, G, y: T ⊢ t^y: U^y] *)
Lemma val_typ_all_to_lambda: forall G v T U,
    inert G ->
    G ⊢ trm_val v : typ_all T U ->
    (exists L T' t,
        v = val_lambda T' t /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_trm y t) : open_typ y U)).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible_v Hin Htt).
  destruct (invertible_val_to_precise_lambda Hinv Hin) as [L [T' [U' [Htp [Hs1 Hs2]]]]].
  inversions Htp.
  exists (L0 \u L \u (dom G)) T' t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H2 y HL0).
  eapply ty_sub; eauto. eapply narrow_typing in H2; eauto.
Qed.

(** ** Canonical Forms for Functions

    [inert G]              #<br>#
    [s: G]                 #<br>#
    [G ⊢ p: forall(T)U]         #<br>#
    [――――――――――――――――――――] #<br>#
    [s ∋ (p, lambda(T')t)] #<br>#
    [G ⊢ T <: T']          #<br>#
    [G, y: T ⊢ t: U]          *)
Lemma canonical_forms_fun: forall G s p T U,
  inert G ->
  well_typed G s ->
  G ⊢ trm_path p : typ_all T U ->
                   (exists L T' t, s ∋ (p, val_lambda T' t) /\
                    G ⊢ T <: T' /\
                    (forall y, y \notin L -> G & y ~ T ⊢ open_trm y t : open_typ y U)).
Proof.
  introv Hin Hwt Hty.
  destruct (var_typ_all_to_binds Hin Hty) as [L [V [S [T' [Hp [Hs1 Hs2]]]]]].
  destruct (corresponding_types_fun Hin Hwt Hp) as [v [P Hv]].
  destruct (val_typ_all_to_lambda Hin Hv) as [L' [S' [t [Heq [Hs1' Hs2']]]]].
  subst.
  exists (L \u L' \u (dom G)) S' t. repeat split~.
  - eapply subtyp_trans; eauto.
  - intros.
    assert (HL: y \notin L) by auto.
    assert (HL': y \notin L') by auto.
    specialize (Hs2 y HL).
    specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    eapply ty_sub; eauto.
Qed.
