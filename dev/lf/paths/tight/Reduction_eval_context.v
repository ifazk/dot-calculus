Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.

Inductive ec : Set :=
| e_empty     : ec              (* [] *)
| e_let_val   : val -> ec -> ec  (* let x = v in e *)
| e_let_trm   : trm -> ec.      (* let x = [] in t *)

Inductive ec_app : ec -> trm -> trm -> Prop :=               (* e[u] ≡ t *)
| ec_empty : forall t,
    ec_app e_empty t t                                      (* ⦰[t] ≡ t *)
| ec_val : forall e u t v,
    ec_app e u t ->                                         (*       e[u] ≡ t            *)
    ec_app (e_let_val v e) u (trm_let (trm_val v) t)        (* (e,x=v)[u] ≡ let x=v in t *)
| ec_trm : forall u t,
    ec_app (e_let_trm u) t (trm_let t u).
