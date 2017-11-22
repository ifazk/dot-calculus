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
Require Import Binding Definitions GeneralToTight InvertibleTyping Narrowing PreciseTyping
         RecordAndInertTypes Substitution Subenvironments TightTyping Weakening.

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

Lemma record_has_trm_dec : forall G p T U T' U' a,
    G ⊢ trm_path p: T ->
    G ⊢ T <: U ->
    record_type T ->
    record_type U ->
    record_has T (dec_trm a T') ->
    (record_has U (dec_trm a U') /\ G ⊢ T' <: U').
Proof.
  introv Hp Hs HrT HrU Ha. Admitted.

Lemma record_has_ty_dec : forall G p T U T' A,
    G ⊢ trm_path p: T ->
    G ⊢ T <: U ->
    record_type T ->
    record_type U ->
    record_has T (dec_typ A T' T') ->
    record_has U (dec_typ A T' T').
Proof.
  introv Hp Hs HrT HrU HA. Admitted.

Lemma val_typing_sub: forall G v T U p,
    inert G ->
    G ⊢ trm_val v: typ_bnd T ->
    G ⊢ open_typ_p p T <: open_typ_p p U ->
    G ⊢ trm_path p: open_typ_p p T ->
    record_type T ->
    record_type U ->
    G ⊢ trm_val v: typ_bnd U.
Proof.
  introv Hi Hv Hs Hp HT HU.
  apply (general_to_tight_typing Hi) in Hv.
  apply (tight_to_invertible_v Hi) in Hv.
  inversions Hv. inversions H. pick_fresh x. assert (x \notin L) as Hx by auto.
  specialize (H3 x Hx). assert (HT' := HT). assert (HU' := HU).
  destruct HT as [lsT HT]. destruct HU as [lsU HU].
  induction HT; subst.
  - destruct D. inversions H. apply open_record_type_p with (p:=p) in HT'.
    apply open_record_type_p with (p:=p) in HU'.
    assert (record_has (open_typ_p p (typ_rcd {t >: t1 <: t1})) (open_dec_p p {t >: t1 <: t1})) as Hrh. {
      unfold open_typ_p, open_dec_p. simpl. auto.
    }
   lets Hr: (record_has_ty_dec Hp Hs HT' HU' Hrh).
Admitted.

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
Lemma record_has_ty_defs: forall z bs P G T ds D,
  z; bs; P; G ⊢ ds :: T ->
  record_has T D ->
  exists d, defs_has ds d /\ z; bs; P; G ⊢ d : D.
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
(*
Lemma corresponding_types_helper: forall G x T s v P1 P2 cs ds U U' y,
    well_typed G s ->
    G  ⊢! p_sel (avar_f x) cs: U' ⪼ U' ->
    x; cs; P; G ⊢ ds :: U

    exists v, s ∋ (p_sel (avar_f y) cs, v).
Proof.
  introv Wt Hp. dependent induction Wt. false* empty_push_inv.
  Admitted.

Lemma corresponding_types_helper: forall G x T s v P1 P2 cs ds U U' y,
    well_typed (G & x ~ T) (s & x ~ v) ->
    G & x ~ T ⊢! p_sel (avar_f y) cs: U' ⪼ U' ->
    (x <> y) \/ (x = y /\ x; cs; (P1 ++ P2); (G & x ~ T) ⊢ ds :: U /\ In cs P1) ->
    exists v, s ∋ (p_sel (avar_f y) cs, v).
Proof.
  introv Wt Hp. dependent induction Wt. false* empty_push_inv.
  Admitted.*)

(** [s: G]                #<br>#
    [G ⊢! p: T]           #<br>#
    [―――――――――――――――]     #<br>#
    [exists v, s ∋ (p, v)]     #<br>#
    [G |- v: T]          *)
Lemma corresponding_types: forall G s p T T',
    inert G ->
    well_typed G s ->
    G ⊢! p: T ⪼ T' ->
    (exists v, s ∋ (p, v) /\
          G ⊢ trm_val v : T).
Proof.
  (* Proof strategy:
     1) induction on well-typedness
     2) induction on the derivation of precise flow *)
  introv Hi Hwt. gen p T T'. induction Hwt; introv Hp.
  - false. dependent induction Hp; eauto; false* binds_empty_inv.
  - destruct p as [y bs].
    (* showing that y is named *)
    lets Hg: (precise_to_general Hp). apply typed_paths_named in Hg. inversions Hg.
    destruct_all. inversions H2.
    destruct (classicT (x = x0)).
    * subst. dependent induction Hp; eauto.
      + Case "pf_bind".
        apply binds_push_eq_inv in H3. subst. exists v. split.
        constructor*. apply* weaken_ty_trm.
      + Case "pf_fld".
        unfolds sel_fields. destruct p. inversions x.
        specialize (IHHp _ _ H0 _ _ Hi Hwt H H1 IHHwt eq_refl JMeq_refl). destruct_all.
        rename x into v'. rename f into bs.
        (* - show that [T = μ(...{a: U}...) *)
        lets Hp': (pf_inert_rcd_U Hi Hp). destruct_all. subst.
        lets Hr: (precise_flow_record_has Hi Hp).
        (* - show that [v' = ν(...{a = v''}...)] and [Г ⊢ v'': U] *)
        apply (proj21 (general_to_tight Hi)) in H3; auto.
        apply tight_to_invertible_v in H3; auto.
        inversions H3. inversions H4. pick_fresh y. assert (y \notin L) as Hy by auto.
        specialize (H7 _ Hy). rewrite open_var_defs_eq in H7. rewrite open_var_typ_eq in H7.
        unfolds pvar. rename x into T'.
        assert (x0; bs; P; G & x0 ~ T ⊢
                                  open_defs_p (p_sel (avar_f x0) bs) ds :: open_typ_p (p_sel (avar_f x0) bs) T')
          as Hds. {
          apply* renaming_def_strengthen. rewrite fv_ctx_types_push_eq. auto.
          rewrite open_var_typ_eq. rewrite open_var_defs_eq. auto.
          apply pf_precise_U in Hp. apply precise_to_general in Hp. apply* ty_rec_elim.
        }
        lets Hd: (record_has_ty_defs Hds Hr). destruct Hd as [d [Hdh HdD]].
        assert (p_sel (avar_f x0) (a :: bs) = (p_sel (avar_f x0) bs) • a) as Heq by auto. rewrite Heq.
        inversions HdD; eauto.
        ++ SCase "ty_def_new".
           exists (val_new T0 ds0). split*. admit.
        ++ SCase "ty_def_path".
           rename x0 into x. rename y0 into z.
           destruct (classicT (x = z)).
           +++ SSCase "x = z".
               subst. specialize (H14 eq_refl). clear Heq.
               inversions H14.
               induction P1. admit.
               dependent induction Hds.
               ++++ destruct ds; inversions x1. destruct ds; inversions H11. destruct T'; inversions x.
                    inversions H7.
                    admit.
               ++++ destruct ds; inversions x1. destruct T'; inversions x. destruct T'2; inversions H13.


           +++ SSCase "x <> z".
               lets Hig: (inert_prefix Hi).
               lets Hok: (inert_ok Hi).
               apply general_to_tight_typing in H5; auto.
               apply tight_to_invertible in H5; auto. clear Heq H14.
               inversions H6.
               ++++ SSSCase "U is a function type".
                    destruct (invertible_to_precise_typ_all Hok H5) as [S'' [T'' [U [L' [Hq [Hs Hs']]]]]].
                    apply pf_strengthen in Hq; auto.
                    destruct (IHHwt Hig _ _ _ Hq) as [v' [Hqp Hv']].
                    exists v'. split. apply* lookup_path. apply* lookup_push_neq.
                    apply pf_inert_lambda_U in Hq; auto. subst. apply ty_sub with (T:=typ_all S'' T'').
                    apply* weaken_ty_trm. apply_fresh subtyp_all as z. apply* tight_to_general.
                    apply* Hs'.
               ++++ SSSCase "U is a recursive type".
                    destruct (invertible_to_precise_typ_bnd H5 H3) as [U [Hq Hs]].
                    apply pf_strengthen in Hq; auto.
                    destruct (IHHwt Hig _ _ _ Hq) as [v' [Hqp Hv']].
                    exists v'. split. apply* lookup_path. apply* lookup_push_neq.
                    apply weaken_ty_trm with (G2 := x ~ T) in Hv'; auto.
                    lets Hpr: (pf_rcd_T Hig Hq). apply precise_to_general in Hq.
                    apply ty_rec_elim in Hq. apply weaken_ty_trm with (G2 := x ~ T) in Hq.
                    apply* val_typing_sub. apply* inert_ok.
      * apply pf_strengthen in Hp; auto.
        assert (inert G) as Hi' by apply* inert_prefix.
        specialize (IHHwt Hi' _ _ _ Hp) as [v' [Hl Ht]].
        exists v'. repeat split. apply* lookup_push_neq. apply* weaken_ty_trm.
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

(** [forall] to [G(x)]

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
  - admit. (*apply~ inert_precise_all_inv.*)
  - apply~ tight_to_general.
  - assumption.
Qed.

(** [forall] to [lambda]

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

(** * Canonical Forms for Functions

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
  destruct (corresponding_types Hin Hwt Hp) as [v [Bis Ht]].
  destruct (val_typ_all_to_lambda Hin Ht) as [L' [S' [t [Heq [Hs1' Hs2']]]]].
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

(** This lemma corresponds to Lemma 3.9 ([mu] to [G(x)]) in the paper.

    [inert G]                    #<br>#
    [G ⊢ p: {a: T}]              #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [exists S, T', G(x) = mu(S)]       #<br>#
    [S^p = ... /\ {a: T'} /\ ...]  #<br>#
    [G ⊢ T' <: T]                *)
Lemma var_typ_rcd_to_binds: forall G p a T,
    inert G ->
    G ⊢ trm_path p : typ_rcd (dec_trm a T) ->
    (exists S T' V,
        G ⊢! p : typ_bnd S ⪼ V /\
        record_has (open_typ_p p S) (dec_trm a T') /\
        G ⊢ T' <: T).
Proof.
  introv Hin Ht.
  lets Hn: (typed_paths_named Ht). destruct Hn as [x [bs Heq]]. subst.
  destruct (typing_implies_bound Ht) as [S BiG].
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_trm_dec Hinv) as [T' [V [Htp Hs]]].
  destruct (pf_inert_rcd_U Hin Htp) as [U' Hr]. subst.
  lets Hr': (precise_flow_record_has Hin Htp). (*apply pf_binds in Pf.
  exists U' T'. split. assumption. split. rewrite open_var_typ_eq. assumption. apply* tight_to_general.
Qed.*) Admitted.

(** [mu] to [nu])

    [inert G]                    #<br>#
    [G ⊢ v: mu(T)]               #<br>#
    [G ⊢ p: T^p]                 #<br>#
    [T^p = ... /\ {a: U} /\ ...  ] #<br>#
    [――――――――――――――――――――――――――] #<br>#
    [exists t, ds, v = nu(T)ds      ] #<br>#
    [ds^p = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: U] *)
Lemma val_mu_to_new: forall G v T U a p,
    inert G ->
    G ⊢ trm_val v: typ_bnd T ->
    G ⊢ trm_path p : open_typ_p p T ->
    record_has (open_typ_p p T) (dec_trm a U) ->
    exists t ds,
      v = val_new T ds /\
      defs_has (open_defs_p p ds) (def_trm a t) /\
      G ⊢ t: U.
Proof.
  introv Hi Ht Hx Hr.
  lets Htt: (general_to_tight_typing Hi Ht).
  lets Hinv: (tight_to_invertible_v Hi Htt).
  inversions Hinv. inversions H.
  pick_fresh z.
  assert (z \notin L) as Hz by auto.
  specialize (H3 z Hz).
  destruct p as [x bs].
  lets Hv: (typed_paths_named Hx). inversions Hv. destruct_all.
  assert (x0; bs; P; G ⊢
    open_defs_p (p_sel (avar_f x0) bs) ds :: open_typ_p (p_sel (avar_f x0) bs) T)
    as Hds by admit. (*apply* renaming_def.*)
  inversions H.
  destruct (record_has_ty_defs Hds Hr) as [d [Hh Hd]].
  inversions Hd; eauto.
  Case "ty_def_new".
  exists (trm_val (val_new T0 ds0)) ds. repeat split*.
  fresh_constructor. simpls. lets Hrs: (record_has_sel_typ Hx Hr). apply ty_rec_elim in Hrs.
  Admitted. (*
  apply* renaming_def'.
Qed.
  *)

(** * Canonical Forms for Objects

    [inert G]            #<br>#
    [s: G]             #<br>#
    [G ⊢ x: {a:T}]             #<br>#
    [――――――――――――――――――] #<br>#
    [exists S, ds, t,] #<br>#
    [s(x) = nu(S)ds] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: T] *)
Lemma canonical_forms_obj: forall G s p a T,
  inert G ->
  well_typed G s ->
  G ⊢ trm_path p: typ_rcd (dec_trm a T) ->
               (exists S ds t,
                   s ∋ (p, val_new S ds) /\
                   defs_has (open_defs_p p ds) (def_trm a t) /\
                   G ⊢ t : T).
Proof.
  introv Hi Hwt Hty.
  destruct (var_typ_rcd_to_binds Hi Hty) as [S [T' [V [Bi [Hr Hs]]]]].
  destruct (corresponding_types Hi Hwt Bi) as [v [Bis Ht]]. Admitted. (*
  apply ty_var in Bi. apply ty_rec_elim in Bi. rewrite <- open_var_typ_eq in Bi.
  destruct (val_mu_to_new Hi Ht Bi Hr) as [t [ds [Heq [Hdefs Ht']]]].
  subst. exists S ds t. repeat split~. eapply ty_sub; eauto.
  apply* inert_ok.
Qed.
*)
