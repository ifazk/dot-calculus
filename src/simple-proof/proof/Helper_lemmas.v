(** printing |-     %\vdash%         #&vdash;#                     *)
(** printing /-     %\vdash%         #&vdash;#                     *)
(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** printing ->     %\rightarrow%    #&rarr;#                      *)
(** printing =>     %\Rightarrow%    #&rArr;#                      *)
(** printing ~~     %\~\~%           #~~#                          *)
(** printing /\     %\wedge%         #&and;#                       *)
(** printing \/     %\vee%           #&or;#                        *)
(** printing forall %\forall%        #&forall;#                    *)
(** printing exists %\exists%        #&exist;#                     *)
(** printing lambda %\lambda%        #&lambda;#                    *)
(** printing mu     %\mu%            #&mu;#                        *)
(** printing nu     %\nu%            #&nu;#                        *)
(** printing Gamma  %\Gamma%         #&Gamma;#                     *)
(** printing top    %\top%           #&#8868;#                     *)
(** printing bottom %\bot%           #&perp;#                      *)
(** printing <>     %\ne%            #&ne;#                        *)
(** printing isin   %\in%            #&isin;#                      *)
(** remove printing ~ *)

(** This module defines various helper lemmas used throughout the proof. *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

(** * Lemmas About Opening *)

(** The following [open_comm_XYZ] lemmas state that opening two
    symbols (variables, types, terms, etc.) at different indices commute. *)

(** - opening types and declarations with different indices commute. *)
Lemma open_comm_typ_dec: forall x y,
    (forall T n m,
        n <> m ->
        open_rec_typ n x (open_rec_typ m y T) =
        open_rec_typ m y (open_rec_typ n x T)) /\
    (forall D n m,
        n <> m ->
        open_rec_dec n x (open_rec_dec m y D) =
        open_rec_dec m y (open_rec_dec n x D)).
Proof.
  intros. apply typ_mutind; intros; subst; simpl; auto.
  - rewrite~ H.
  - rewrite~ H. rewrite~ H0.
  - destruct a; simpl; auto.
    repeat case_if; subst; simpl; repeat case_if~.
  - rewrite~ H.
  - rewrite~ H. rewrite~ H0.
  - rewrite~ H. rewrite~ H0.
  - rewrite~ H.
Qed.

(** - opening terms, values, definitions, and lists of definitions with
      different indices commute. *)
Lemma open_comm_trm_val_def_defs : forall x y,
    (forall t n m,
        n <> m ->
        open_rec_trm n x (open_rec_trm m y t) =
        open_rec_trm m y (open_rec_trm n x t)) /\
    (forall v n m,
        n <> m ->
        open_rec_val n x (open_rec_val m y v) =
        open_rec_val m y (open_rec_val n x v)) /\
    (forall d n m,
        n <> m ->
        open_rec_def n x (open_rec_def m y d) =
        open_rec_def m y (open_rec_def n x d)) /\
    (forall ds n m,
        n <> m ->
        open_rec_defs n x (open_rec_defs m y ds) =
        open_rec_defs m y (open_rec_defs n x ds)).
Proof.
  intros. apply trm_mutind; intros; subst; simpl; auto.
  - destruct a; simpl; auto.
    repeat case_if; subst; simpl; repeat case_if~.
  - rewrite~ H.
  - destruct a; simpl; auto.
    repeat case_if; subst; simpl; repeat case_if~.
  - destruct a; destruct a0; simpl; auto; repeat case_if~; subst; simpl; repeat case_if~.
  - rewrite~ H. rewrite~ H0.
  - rewrite~ H. rewrite~ (proj21 (open_comm_typ_dec x y)).
  - rewrite~ H. rewrite~ (proj21 (open_comm_typ_dec x y)).
  - rewrite~ (proj21 (open_comm_typ_dec x y)).
  - rewrite~ H.
  - rewrite~ H. rewrite~ H0.
Qed.

(** The following [lc_open_rec_open_XYZ] lemmas state that if opening
    a symbol (variables, types, terms, etc.) at index [n] that is
    already opened at index [m] results in the same opened symbol,
    opening the symbol itself at index [n] results in the same symbol. *)

(** - if opening an opened type or declaration at index [n] has no effect,
      opening the original type or declaration at index [n] has no effect *)
Lemma lc_open_rec_open_typ_dec: forall x y,
    (forall T n m,
        n <> m ->
        open_rec_typ n x (open_rec_typ m y T) = open_rec_typ m y T ->
        open_rec_typ n x T = T) /\
    (forall D n m,
        n <> m ->
        open_rec_dec n x (open_rec_dec m y D) = open_rec_dec m y D ->
        open_rec_dec n x D = D).
Proof.
  introv. apply typ_mutind; intros; simpls; auto.
  - inversions H1. rewrite H with (m:=m); auto.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=m); auto.
  - inversions H0. destruct a; simpl; auto.
    case_if; simpls; case_if; subst; simpl in *; repeat case_if~.
    reflexivity.
  - inversions H1. rewrite H with (m:=S m); auto.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=S m); auto.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=m); auto.
  - inversions H1. rewrite H with (m:=m); auto.
Qed.

(** - if opening an opened term, value, definition, or list of definitions
      at index [n] has no effect, opening the original term, value, definition,
      or list of definitions at index [n] has no effect *)
Lemma lc_open_rec_open_trm_val_def_defs: forall x y,
    (forall t n m,
        n <> m ->
        open_rec_trm n x (open_rec_trm m y t) = open_rec_trm m y t ->
        open_rec_trm n x t = t) /\
    (forall v n m,
        n <> m ->
        open_rec_val n x (open_rec_val m y v) = open_rec_val m y v ->
        open_rec_val n x v = v) /\
    (forall d n m,
        n <> m ->
        open_rec_def n x (open_rec_def m y d) = open_rec_def m y d ->
        open_rec_def n x d = d) /\
    (forall ds n m,
        n <> m ->
        open_rec_defs n x (open_rec_defs m y ds) = open_rec_defs m y ds ->
        open_rec_defs n x ds = ds).
Proof.
  introv. apply trm_mutind; intros; simpls; auto.
  - destruct a; simpl; auto.
    case_if; simpl in *; case_if; simpl in *; auto; case_if.
  - inversions H1. rewrite H with (m:=m); auto.
  - inversions H0.
    destruct a; simpl; auto.
    case_if; simpl in *; case_if; simpl in *; auto; case_if.
  - inversions H0. destruct a; destruct a0; simpl; auto; repeat case_if~; simpls; repeat case_if; simpl in *; repeat case_if~.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=S m); auto.
  - inversions H1. rewrite H with (m:=S m); auto.
    rewrite (proj21 (lc_open_rec_open_typ_dec x y)) with (m:=S m); auto.
  - inversions H1. rewrite H with (m:=S m); auto.
    rewrite (proj21 (lc_open_rec_open_typ_dec x y)) with (m:=m); auto.
  - inversions H0.
    rewrite (proj21 (lc_open_rec_open_typ_dec x y)) with (m:=m); auto.
  - inversions H1. rewrite H with (m:=m); auto.
  - inversions H2. rewrite H with (m:=m); auto. rewrite H0 with (m:=m); auto.
Qed.

Lemma lc_opening_avar: forall n x y,
    lc_var y ->
    open_rec_avar n x y = y.
Proof.
  introv Hl. destruct y as [b | y]. inversion Hl. simpls*.
Qed.

Lemma lc_opening_typ_dec: forall x,
    (forall T, lc_typ T -> forall n, open_rec_typ n x T = T) /\
    (forall D, lc_dec D -> forall n, open_rec_dec n x D = D).
Proof.
  intros. apply lc_typ_mutind; intros; simpls; f_equal*.
  - apply* lc_opening_avar.
  - specialize (H x (S n)). apply lc_open_rec_open_typ_dec in H; auto.
  - specialize (H x (S n)). apply lc_open_rec_open_typ_dec in H; auto.
Qed.

Lemma lc_opening_trm_val_def_defs: forall x,
  (forall t, lc_trm t -> forall n, open_rec_trm n x t = t) /\
  (forall v, lc_val v -> forall n, open_rec_val n x v = v) /\
  (forall d, lc_def d -> forall n, open_rec_def n x d = d) /\
  (forall ds, lc_defs ds -> forall n, open_rec_defs n x ds = ds).
Proof.
  introv. apply lc_mutind; intros; simpls; f_equal*; try (apply* lc_opening_avar).
  - specialize (H0 x (S n)).
    rewrite (proj41 (lc_open_rec_open_trm_val_def_defs) x x) with (m:=0); auto.
  - specialize (l x).
    apply (proj21 (lc_opening_typ_dec x)) with (n := S n) in l.
    rewrite (proj21 (lc_open_rec_open_typ_dec x x)) with (m:=0); auto.
  - specialize (H x (S n)).
    rewrite (proj44 (lc_open_rec_open_trm_val_def_defs) x x) with (m:=0); auto.
  - apply* lc_opening_typ_dec.
  - specialize (H x (S n)).
    rewrite (proj41 (lc_open_rec_open_trm_val_def_defs) x x) with (m:=0); auto.
  - apply* lc_opening_typ_dec.
Qed.

Lemma lc_opening : forall t n x,
    lc_trm t ->
    open_rec_trm n x t = t.
Proof.
  intros. apply* lc_opening_trm_val_def_defs.
Qed.

(** * Lemmas About Records and Record Types *)

(** [labels(D) = labels(D^x)] *)
Lemma open_dec_preserves_label: forall D x i,
  label_of_dec D = label_of_dec (open_rec_dec i x D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

(** [record_dec D]
    ----------------
    [record_dec D^x] *)
Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open_dec x D).
Proof.
  intros. inversion H; unfold open_dec; simpl; constructor.
Qed.

(** [record_typ T]
    ----------------
    [record_typ T^x] *)
Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (open_typ x T) ls.
Proof.
  intros. induction H.
  - unfold open_typ. simpl.
    apply rt_one.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
  - unfold open_typ. simpl.
    apply rt_cons; try assumption.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
Qed.

(** [record_typ T]
    ----------------
    [record_typ T^x] *)
Lemma open_record_type: forall T x,
  record_type T -> record_type (open_typ x T).
Proof.
  intros. destruct H as [ls H]. exists ls. eapply open_record_typ.
  eassumption.
Qed.

(** If [T] is a record type with labels [ls], and [T = ... /\ D /\ ...],
    then [label(D) isin ls]. *)
Lemma record_typ_has_label_in: forall T D ls,
  record_typ T ls ->
  record_has T D ->
  label_of_dec D \in ls.
Proof.
  introv Htyp Has. generalize dependent D. induction Htyp; intros.
  - inversion Has. subst. apply in_singleton_self.
  - inversion Has; subst; rewrite in_union.
    + left. apply* IHHtyp.
    + right. inversions H5. apply in_singleton_self.
Qed.

(** [T = ... /\ {A: T1..T1} /\ ...] #<br>#
    [T = ... /\ {A: T2..T2} /\ ...]
    -----------------------------
    [T1 = T2] *)
Lemma unique_rcd_typ: forall T A T1 T2,
  record_type T ->
  record_has T (dec_typ A T1 T1) ->
  record_has T (dec_typ A T2 T2) ->
  T1 = T2.
Proof.
  introv Htype Has1 Has2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:=dec_typ A T1 T1) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:=dec_typ A T2 T2) in Htyp.
    + inversions H5. false* H1.
    + assumption.
  - inversions H5. inversions* H9.
Qed.

(** [ds = ... /\ {a = t} /\ ...]  #<br>#
    [ds = ... /\ {a = t'} /\ ...]
    -----------------------------
    [t = t'] *)
Lemma defs_has_inv: forall ds a t t',
    defs_has ds (def_trm a t) ->
    defs_has ds (def_trm a t') ->
    t = t'.
Proof.
  intros. unfold defs_has in *.
  inversions H. inversions H0.
  rewrite H1 in H2. inversions H2.
  reflexivity.
Qed.

(** * Conversion into General Typing *)

(** Precise typing implies general typing. *)
Lemma precise_to_general: forall G t T,
    G |-! t : T ->
    G |- t : T.
Proof.
  intros. induction H; intros; subst; eauto.
Qed.

(** Tight typing implies general typing. *)
Lemma tight_to_general:
  (forall G t T,
     G |-# t : T ->
     G |- t : T) /\
  (forall G S U,
     G |-# S <: U ->
     G |- S <: U).
Proof.
  apply ts_mutind_t; intros; subst; eauto using precise_to_general.
Qed.

(** * Other Lemmas *)

(** If a value [v] has type [T], then [v] has a precise type [T']
    that is a subtype of [T].
    This lemma corresponds to Lemma 3.13 in the paper. *)
Lemma val_typing: forall G v T,
  G |- trm_val v : T ->
  exists T', G |-! trm_val v : T' /\
        G |- T' <: T.
Proof.
  intros G v T H. dependent induction H.
  - exists (typ_all T U). split.
    apply ty_all_intro_p with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_bnd T). split.
    apply ty_new_intro_p with (L:=L); eauto. apply subtyp_refl.
  - destruct (IHty_trm _ eq_refl) as [T' [Hty Hsub]].
    exists T'. split; eauto.
Qed.

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma typing_implies_bound: forall G x T,
  G |- trm_var (avar_f x) : T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_var (avar_f x)) as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm; eauto];
    try solve [inversion Heqt; eapply IHty_trm1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.
