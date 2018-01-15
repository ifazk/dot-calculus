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

Lemma stack_typing : forall G s v p,
    well_typed G s ->
    s ∋ (p, v) ->
    exists T, G ⊢ trm_val v: T.
Proof.
  introv Hwt Hs.
Admitted.

(** [G ~ s]                             #<br>#
    [s ∋ (p, ν(U)...{a = q}...) // ps]  #<br>#
    [――――――――――――――――――――――――――――――――]  #<br>#
    [exists T, Г ⊢ q: T]                         *)
Lemma stack_path_typing : forall G s U ds a p r t,
    well_typed G s ->
    s ∋ (p, val_new U ds) ->
    defs_has (open_defs_p r ds) (def_trm a t) ->
    exists T, G ⊢ t: T.
Proof.
  introv Hwt Hs Hd.
  destruct (stack_typing Hwt Hs) as [T Ht].
  (* apply [stack_typing] to say that [val_new U ds] is typed in [G], and therefore, [q] can be typed. *)
Admitted.

(** [G ~ s]                 #<br>#
    [G ⊢ p: T]              #<br>#
    [―――――――――――――――――――――] #<br>#
    [exists P v, P ⊢ s ∋ (p, v)] *)
Lemma typed_path_lookup : forall G s p T,
    well_typed G s ->
    G ⊢ trm_path p: T ->
    exists v, s ∋ (p, v).
Proof.
  introv Hwt Hp. Admitted.

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


(** * Lemmas to Prove Canonical Forms for Objects *)

Lemma lookup_path_subtyping: forall G s p q T,
    inert G ->
    well_typed G s ->
    s ⟦ trm_path p ⟼ trm_path q ⟧ ->
    G ⊢ open_typ_p q T <: open_typ_p p T /\ G ⊢ open_typ_p p T <: open_typ_p q T.
Proof.
  introv Hi Hwt. gen p q T. induction Hwt; introv Hl.
  - false* lookup_empty.
  - inversions Hl. inversions H3.

Lemma lookup_path_subtyping: forall G s p q T,
    inert G ->
    well_typed G s ->
    s ⟦ trm_path p ⟼ trm_path q ⟧ ->
    G ⊢ trm_path p: open_typ_p p T ->
    G ⊢ open_typ_p q T <: open_typ_p p T /\ G ⊢ open_typ_p p T <: open_typ_p q T.
Proof.
  introv Hi Hwt Hl Ht.
  proof_recipe.
  dependent induction Ht.
  -



Lemma lookup_path_subtyping_p: forall G s p q T,
    well_typed G s ->
    star (lookup_step s) (trm_path p) (trm_path q) ->
    G ⊢ open_typ_p q T <: open_typ_p p T.
Proof.
  apply* lookup_path_subtyping.
Qed.

Lemma lookup_path_subtyping_q: forall G s p q T,
    well_typed G s ->
    star (lookup_step s) (trm_path p) (trm_path q) ->
    G ⊢ open_typ_p p T <: open_typ_p q T.
Proof.
  apply* lookup_path_subtyping.
Qed.

Lemma lookup_preservation_typ_bnd: forall G s p q U a,
    inert G ->
    well_typed G s ->
    star (lookup_step s) (trm_path p) (trm_path q) ->
    G ⊢ trm_path p : typ_rcd (dec_trm a (open_typ_p p U)) ->
    G ⊢ trm_path q : typ_rcd (dec_trm a (open_typ_p q U)).
Proof.
  introv Hi Hwt Hl Hp. gen a U. dependent induction Hl; introv Hp; auto.
  proof_recipe.
  lets Hlp: (lookup_step_preservation_prec Hi Hwt H Hpr).
  destruct (lookup_path_inv Hl) as [q' Heq]. subst.
  destruct (pf_inert_rcd_U Hi Hpr) as [V Heq]. subst.
  lets Hh: (precise_flow_record_has Hi Hpr).
  assert (exists Tpr', Tpr = open_typ_p p Tpr') as Hop. admit.
  destruct Hop as [Tpr' Heq]. subst.
  specialize (IHHl _ _ Hi Hwt eq_refl eq_refl).
  assert (G ⊢ trm_path q' : typ_rcd (dec_trm a (open_typ_p q' Tpr'))) as Hq'. {
    apply ty_rec_elim in Hlp. apply* typing_record_has. apply* record_has_open_diff.
  }
  specialize (IHHl _ _ Hq'). apply ty_sub with (T:=typ_rcd (dec_trm a (open_typ_p q Tpr'))).
  assumption.
  assert (star (lookup_step s) (trm_path p) (trm_path q)) as Hpq. {
    eapply star_trans. apply star_one. apply H. auto.
  }
  constructor. apply subtyp_trans with (T:=open_typ_p p Tpr').
  apply* lookup_path_subtyping_p.
  apply tight_to_general in Hspr. apply subtyp_trans with (T:=open_typ_p p U).
  assumption. apply* lookup_path_subtyping_q.
Qed.

Lemma corresponding_types_obj: forall G s p S a T,
    inert G ->
    well_typed G s ->
    G ⊢! p: typ_bnd S ⪼ typ_rcd (dec_trm a T) ->
    (exists q v S' T',
        star (lookup_step s) (trm_path p) (trm_path q) /\
        s ⟦ trm_path q ⟼ trm_val v ⟧ /\
        G ⊢ trm_path q : typ_rcd (dec_trm a (open_typ_p q T')) /\
        G ⊢ trm_val v : typ_bnd S' /\
        record_has (open_typ_p q S') (dec_trm a (open_typ_p q T')) /\
        G ⊢ open_typ_p q T' <: T).
Proof.
  introv Hi Hwt Hp.
  lets Hp': (pf_precise_U Hp).
  apply precise_to_general in Hp'.
  destruct (typed_path_lookup Hwt Hp') as [v Hs]. inversions Hs.
  lets Hr: (precise_flow_record_has Hi Hp).
  destruct (record_has_open _ _ Hr) as [U Hr'].
  assert (s ∋ (p, v)) as Hl by auto.
  destruct (lookup_last_path Hl) as [q [Hpq Hqv]].
  lets Hpg: (precise_to_general Hp).
  assert (exists T', T = open_typ_p p T') as Heq by admit.
  destruct Heq as [T' Heq]. subst.
  lets Ht: (lookup_preservation_typ_bnd _ Hi Hwt Hpq Hpg).
  proof_recipe.
  lets Hlp: (lookup_step_preservation_prec Hi Hwt Hqv Hpr).
  destruct (pf_inert_rcd_U Hi Hpr) as [T Heq]. subst.
  assert (exists Tpr', Tpr = open_typ_p q Tpr') as Heq by admit. destruct Heq as [Tpr' Heq]. subst.
  exists q v T Tpr'. repeat split; auto.
  apply* precise_to_general.
  apply* precise_flow_record_has. apply tight_to_general in Hspr.
  apply (subtyp_trans Hspr). apply* lookup_path_subtyping.
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
  lets Hr': (precise_flow_record_has Hin Htp).
  apply tight_to_general in Hs. repeat eexists; eauto.
Qed.

(** [mu] to [nu])

    [inert G]                    #<br>#
    [G ⊢ v: mu(T)]               #<br>#
    [G ⊢ p: T^p]                 #<br>#
    [T^p = ... /\ {a: U} /\ ...  ] #<br>#
    [――――――――――――――――――――――――――] #<br>#
    [exists t, ds, v = nu(T)ds      ] #<br>#
    [ds^p = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: U]
*)
Lemma val_mu_to_new: forall G v T U a p,
    inert G ->
    G ⊢ trm_val v: typ_bnd T ->
    G ⊢ trm_path p : typ_rcd (dec_trm a U) ->
    record_has (open_typ_p p T) (dec_trm a U) ->
    exists t ds,
      v = val_new T ds /\
      defs_has (open_defs_p p ds) (def_trm a t) /\
      G ⊢ t: U.
(**
    Γ ⊢ v: μ(T)
    Γ ⊢ p: T’^p
    T = …{a: U}…
    T’ = …{a: U’}…
    Γ ⊢ U <: U’
    ______________ (Lemma 2’)
    ∃ t, ds.
    v = ν(T)ds
    ds^p = …{a = t}…
    Γ ⊢ t: U’
 *)
(*Lemma val_mu_to_new: forall G v T T' U a p,
    inert G ->
    G ⊢ trm_val v: typ_bnd T ->
    G ⊢ trm_path p : open_typ_p p T' ->
    record_has (open_typ_p p T') (dec_trm a U') ->
    exists t ds,
      v = val_new T ds /\
      defs_has (open_defs_p p ds) (def_trm a t) /\
      G ⊢ t: U.*)

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
  fresh_constructor. simpls. rename x1 into bs.
Admitted. (*
  apply* renaming_def'.
Qed.
             *)


(** ** Canonical Forms for Objects

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
  proof_recipe.
  destruct (pf_inert_rcd_U Hi Hpr) as [V Heq]. subst.
  destruct (corresponding_types_obj Hi Hwt Hpr) as
      [q [v [S' [T' [Hpq [Hqv [Hq [Hv [Hr Hs]]]]]]]]].
  lets Hrh: (precise_flow_record_has Hi Hpr).
  lets Bieq: (pf_precise_U Hpr).
  destruct (val_mu_to_new Hi Hv Hq Hr) as [t [ds [Heq' [Hdefs Ht']]]].
  subst. exists S' ds t. repeat split~.
  - eapply star_trans. apply Hpq. apply* star_one.
  - assert (exists t', t = open_trm_p p t') as Hex. admit.
    destruct Hex as [t' Heq]. subst. admit.
  - apply ty_sub with (T:=Tpr). apply ty_sub with (T:=open_typ_p q T'). assumption. assumption.
    apply* tight_to_general.
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
  destruct (typed_path_lookup Hwt Hg) as [v Hs].
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
