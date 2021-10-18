Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export decl_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme kind_ind' := Induction for kind Sort Prop.

Definition kind_mutind :=
  fun H1 H2 H3 =>
  kind_ind' H1 H2 H3.

Scheme kind_rec' := Induction for kind Sort Set.

Definition kind_mutrec :=
  fun H1 H2 H3 =>
  kind_rec' H1 H2 H3.

Scheme expr_ind' := Induction for expr Sort Prop
  with body_ind' := Induction for body Sort Prop.

Definition expr_body_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  (conj (expr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)
  (body_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)).

Scheme expr_rec' := Induction for expr Sort Set
  with body_rec' := Induction for body Sort Set.

Definition expr_body_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  (pair (expr_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)
  (body_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)).

Scheme context_ind' := Induction for context Sort Prop.

Definition context_mutind :=
  fun H1 H2 H3 =>
  context_ind' H1 H2 H3.

Scheme context_rec' := Induction for context Sort Set.

Definition context_mutrec :=
  fun H1 H2 H3 =>
  context_rec' H1 H2 H3.

Scheme dir_ind' := Induction for dir Sort Prop.

Definition dir_mutind :=
  fun H1 H2 H3 =>
  dir_ind' H1 H2 H3.

Scheme dir_rec' := Induction for dir Sort Set.

Definition dir_mutrec :=
  fun H1 H2 H3 =>
  dir_rec' H1 H2 H3.

Scheme obindd_ind' := Induction for obindd Sort Prop.

Definition obindd_mutind :=
  fun H1 H2 H3 =>
  obindd_ind' H1 H2 H3.

Scheme obindd_rec' := Induction for obindd Sort Set.

Definition obindd_mutrec :=
  fun H1 H2 H3 =>
  obindd_rec' H1 H2 H3.

Scheme dwork_ind' := Induction for dwork Sort Prop
  with dworklist_ind' := Induction for dworklist Sort Prop.

Definition dwork_dworklist_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (conj (dwork_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (dworklist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Scheme dwork_rec' := Induction for dwork Sort Set
  with dworklist_rec' := Induction for dworklist Sort Set.

Definition dwork_dworklist_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (pair (dwork_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (dworklist_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_expr_wrt_expr_rec (n1 : nat) (x1 : exprvar) (e1 : expr) {struct e1} : expr :=
  match e1 with
    | e_var_f x2 => if (x1 == x2) then (e_var_b n1) else (e_var_f x2)
    | e_var_b n2 => if (lt_ge_dec n2 n1) then (e_var_b n2) else (e_var_b (S n2))
    | e_kind k1 => e_kind k1
    | e_num n2 => e_num n2
    | e_int => e_int
    | e_bot A1 => e_bot (close_expr_wrt_expr_rec n1 x1 A1)
    | e_app e2 e3 => e_app (close_expr_wrt_expr_rec n1 x1 e2) (close_expr_wrt_expr_rec n1 x1 e3)
    | e_abs A1 b1 => e_abs (close_expr_wrt_expr_rec n1 x1 A1) (close_body_wrt_expr_rec (S n1) x1 b1)
    | e_pi A1 B1 => e_pi (close_expr_wrt_expr_rec n1 x1 A1) (close_expr_wrt_expr_rec (S n1) x1 B1)
    | e_bind A1 b1 => e_bind (close_expr_wrt_expr_rec n1 x1 A1) (close_body_wrt_expr_rec (S n1) x1 b1)
    | e_all A1 B1 => e_all (close_expr_wrt_expr_rec n1 x1 A1) (close_expr_wrt_expr_rec (S n1) x1 B1)
    | e_castup A1 e2 => e_castup (close_expr_wrt_expr_rec n1 x1 A1) (close_expr_wrt_expr_rec n1 x1 e2)
    | e_castdn e2 => e_castdn (close_expr_wrt_expr_rec n1 x1 e2)
  end

with close_body_wrt_expr_rec (n1 : nat) (x1 : exprvar) (b1 : body) {struct b1} : body :=
  match b1 with
    | b_anno e1 A1 => b_anno (close_expr_wrt_expr_rec n1 x1 e1) (close_expr_wrt_expr_rec n1 x1 A1)
  end.

Definition close_expr_wrt_expr x1 e1 := close_expr_wrt_expr_rec 0 x1 e1.

Definition close_body_wrt_expr x1 b1 := close_body_wrt_expr_rec 0 x1 b1.

Fixpoint close_context_wrt_expr_rec (n1 : nat) (x1 : exprvar) (G1 : context) {struct G1} : context :=
  match G1 with
    | ctx_nil => ctx_nil
    | ctx_cons G2 x2 A1 => ctx_cons (close_context_wrt_expr_rec n1 x1 G2) x2 (close_expr_wrt_expr_rec n1 x1 A1)
  end.

Definition close_context_wrt_expr x1 G1 := close_context_wrt_expr_rec 0 x1 G1.

Fixpoint close_obindd_wrt_expr_rec (n1 : nat) (x1 : exprvar) (ob1 : obindd) {struct ob1} : obindd :=
  match ob1 with
    | dob_none => dob_none
    | dob_bind x2 A1 => dob_bind x2 (close_expr_wrt_expr_rec n1 x1 A1)
  end.

Definition close_obindd_wrt_expr x1 ob1 := close_obindd_wrt_expr_rec 0 x1 ob1.

Fixpoint close_dwork_wrt_expr_rec (n1 : nat) (x1 : exprvar) (w1 : dwork) {struct w1} : dwork :=
  match w1 with
    | dw_check ob1 e1 e2 A1 => dw_check (close_obindd_wrt_expr_rec n1 x1 ob1) (close_expr_wrt_expr_rec n1 x1 e1) (close_expr_wrt_expr_rec n1 x1 e2) (close_expr_wrt_expr_rec n1 x1 A1)
    | dw_infer e1 e2 wl1 => dw_infer (close_expr_wrt_expr_rec n1 x1 e1) (close_expr_wrt_expr_rec n1 x1 e2) (close_dworklist_wrt_expr_rec (S n1) x1 wl1)
    | dw_infer_app A1 e1 e2 wl1 => dw_infer_app (close_expr_wrt_expr_rec n1 x1 A1) (close_expr_wrt_expr_rec n1 x1 e1) (close_expr_wrt_expr_rec n1 x1 e2) (close_dworklist_wrt_expr_rec (S n1) x1 wl1)
    | dw_reduce e1 wl1 => dw_reduce (close_expr_wrt_expr_rec n1 x1 e1) (close_dworklist_wrt_expr_rec (S n1) x1 wl1)
    | dw_compact A1 B1 => dw_compact (close_expr_wrt_expr_rec n1 x1 A1) (close_expr_wrt_expr_rec n1 x1 B1)
  end

with close_dworklist_wrt_expr_rec (n1 : nat) (x1 : exprvar) (wl1 : dworklist) {struct wl1} : dworklist :=
  match wl1 with
    | dwl_nil => dwl_nil
    | dwl_cons wl2 w1 => dwl_cons (close_dworklist_wrt_expr_rec n1 x1 wl2) (close_dwork_wrt_expr_rec n1 x1 w1)
    | dwl_bind wl2 x2 A1 => dwl_bind (close_dworklist_wrt_expr_rec n1 x1 wl2) x2 (close_expr_wrt_expr_rec n1 x1 A1)
  end.

Definition close_dwork_wrt_expr x1 w1 := close_dwork_wrt_expr_rec 0 x1 w1.

Definition close_dworklist_wrt_expr x1 wl1 := close_dworklist_wrt_expr_rec 0 x1 wl1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_kind (k1 : kind) {struct k1} : nat :=
  match k1 with
    | k_star => 1
    | k_box => 1
  end.

Fixpoint size_expr (e1 : expr) {struct e1} : nat :=
  match e1 with
    | e_var_f x1 => 1
    | e_var_b n1 => 1
    | e_kind k1 => 1 + (size_kind k1)
    | e_num n1 => 1
    | e_int => 1
    | e_bot A1 => 1 + (size_expr A1)
    | e_app e2 e3 => 1 + (size_expr e2) + (size_expr e3)
    | e_abs A1 b1 => 1 + (size_expr A1) + (size_body b1)
    | e_pi A1 B1 => 1 + (size_expr A1) + (size_expr B1)
    | e_bind A1 b1 => 1 + (size_expr A1) + (size_body b1)
    | e_all A1 B1 => 1 + (size_expr A1) + (size_expr B1)
    | e_castup A1 e2 => 1 + (size_expr A1) + (size_expr e2)
    | e_castdn e2 => 1 + (size_expr e2)
  end

with size_body (b1 : body) {struct b1} : nat :=
  match b1 with
    | b_anno e1 A1 => 1 + (size_expr e1) + (size_expr A1)
  end.

Fixpoint size_context (G1 : context) {struct G1} : nat :=
  match G1 with
    | ctx_nil => 1
    | ctx_cons G2 x1 A1 => 1 + (size_context G2) + (size_expr A1)
  end.

Fixpoint size_dir (d1 : dir) {struct d1} : nat :=
  match d1 with
    | d_infer => 1
    | d_check => 1
  end.

Fixpoint size_obindd (ob1 : obindd) {struct ob1} : nat :=
  match ob1 with
    | dob_none => 1
    | dob_bind x1 A1 => 1 + (size_expr A1)
  end.

Fixpoint size_dwork (w1 : dwork) {struct w1} : nat :=
  match w1 with
    | dw_check ob1 e1 e2 A1 => 1 + (size_obindd ob1) + (size_expr e1) + (size_expr e2) + (size_expr A1)
    | dw_infer e1 e2 wl1 => 1 + (size_expr e1) + (size_expr e2) + (size_dworklist wl1)
    | dw_infer_app A1 e1 e2 wl1 => 1 + (size_expr A1) + (size_expr e1) + (size_expr e2) + (size_dworklist wl1)
    | dw_reduce e1 wl1 => 1 + (size_expr e1) + (size_dworklist wl1)
    | dw_compact A1 B1 => 1 + (size_expr A1) + (size_expr B1)
  end

with size_dworklist (wl1 : dworklist) {struct wl1} : nat :=
  match wl1 with
    | dwl_nil => 1
    | dwl_cons wl2 w1 => 1 + (size_dworklist wl2) + (size_dwork w1)
    | dwl_bind wl2 x1 A1 => 1 + (size_dworklist wl2) + (size_expr A1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_expr_wrt_expr : nat -> expr -> Prop :=
  | degree_wrt_expr_e_var_f : forall n1 x1,
    degree_expr_wrt_expr n1 (e_var_f x1)
  | degree_wrt_expr_e_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_expr_wrt_expr n1 (e_var_b n2)
  | degree_wrt_expr_e_kind : forall n1 k1,
    degree_expr_wrt_expr n1 (e_kind k1)
  | degree_wrt_expr_e_num : forall n1 n2,
    degree_expr_wrt_expr n1 (e_num n2)
  | degree_wrt_expr_e_int : forall n1,
    degree_expr_wrt_expr n1 (e_int)
  | degree_wrt_expr_e_bot : forall n1 A1,
    degree_expr_wrt_expr n1 A1 ->
    degree_expr_wrt_expr n1 (e_bot A1)
  | degree_wrt_expr_e_app : forall n1 e1 e2,
    degree_expr_wrt_expr n1 e1 ->
    degree_expr_wrt_expr n1 e2 ->
    degree_expr_wrt_expr n1 (e_app e1 e2)
  | degree_wrt_expr_e_abs : forall n1 A1 b1,
    degree_expr_wrt_expr n1 A1 ->
    degree_body_wrt_expr (S n1) b1 ->
    degree_expr_wrt_expr n1 (e_abs A1 b1)
  | degree_wrt_expr_e_pi : forall n1 A1 B1,
    degree_expr_wrt_expr n1 A1 ->
    degree_expr_wrt_expr (S n1) B1 ->
    degree_expr_wrt_expr n1 (e_pi A1 B1)
  | degree_wrt_expr_e_bind : forall n1 A1 b1,
    degree_expr_wrt_expr n1 A1 ->
    degree_body_wrt_expr (S n1) b1 ->
    degree_expr_wrt_expr n1 (e_bind A1 b1)
  | degree_wrt_expr_e_all : forall n1 A1 B1,
    degree_expr_wrt_expr n1 A1 ->
    degree_expr_wrt_expr (S n1) B1 ->
    degree_expr_wrt_expr n1 (e_all A1 B1)
  | degree_wrt_expr_e_castup : forall n1 A1 e1,
    degree_expr_wrt_expr n1 A1 ->
    degree_expr_wrt_expr n1 e1 ->
    degree_expr_wrt_expr n1 (e_castup A1 e1)
  | degree_wrt_expr_e_castdn : forall n1 e1,
    degree_expr_wrt_expr n1 e1 ->
    degree_expr_wrt_expr n1 (e_castdn e1)

with degree_body_wrt_expr : nat -> body -> Prop :=
  | degree_wrt_expr_b_anno : forall n1 e1 A1,
    degree_expr_wrt_expr n1 e1 ->
    degree_expr_wrt_expr n1 A1 ->
    degree_body_wrt_expr n1 (b_anno e1 A1).

Scheme degree_expr_wrt_expr_ind' := Induction for degree_expr_wrt_expr Sort Prop
  with degree_body_wrt_expr_ind' := Induction for degree_body_wrt_expr Sort Prop.

Definition degree_expr_wrt_expr_degree_body_wrt_expr_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  (conj (degree_expr_wrt_expr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)
  (degree_body_wrt_expr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)).

Hint Constructors degree_expr_wrt_expr : core lngen.

Hint Constructors degree_body_wrt_expr : core lngen.

Inductive degree_context_wrt_expr : nat -> context -> Prop :=
  | degree_wrt_expr_ctx_nil : forall n1,
    degree_context_wrt_expr n1 (ctx_nil)
  | degree_wrt_expr_ctx_cons : forall n1 G1 x1 A1,
    degree_context_wrt_expr n1 G1 ->
    degree_expr_wrt_expr n1 A1 ->
    degree_context_wrt_expr n1 (ctx_cons G1 x1 A1).

Scheme degree_context_wrt_expr_ind' := Induction for degree_context_wrt_expr Sort Prop.

Definition degree_context_wrt_expr_mutind :=
  fun H1 H2 H3 =>
  degree_context_wrt_expr_ind' H1 H2 H3.

Hint Constructors degree_context_wrt_expr : core lngen.

Inductive degree_obindd_wrt_expr : nat -> obindd -> Prop :=
  | degree_wrt_expr_dob_none : forall n1,
    degree_obindd_wrt_expr n1 (dob_none)
  | degree_wrt_expr_dob_bind : forall n1 x1 A1,
    degree_expr_wrt_expr n1 A1 ->
    degree_obindd_wrt_expr n1 (dob_bind x1 A1).

Scheme degree_obindd_wrt_expr_ind' := Induction for degree_obindd_wrt_expr Sort Prop.

Definition degree_obindd_wrt_expr_mutind :=
  fun H1 H2 H3 =>
  degree_obindd_wrt_expr_ind' H1 H2 H3.

Hint Constructors degree_obindd_wrt_expr : core lngen.

Inductive degree_dwork_wrt_expr : nat -> dwork -> Prop :=
  | degree_wrt_expr_dw_check : forall n1 ob1 e1 e2 A1,
    degree_obindd_wrt_expr n1 ob1 ->
    degree_expr_wrt_expr n1 e1 ->
    degree_expr_wrt_expr n1 e2 ->
    degree_expr_wrt_expr n1 A1 ->
    degree_dwork_wrt_expr n1 (dw_check ob1 e1 e2 A1)
  | degree_wrt_expr_dw_infer : forall n1 e1 e2 wl1,
    degree_expr_wrt_expr n1 e1 ->
    degree_expr_wrt_expr n1 e2 ->
    degree_dworklist_wrt_expr (S n1) wl1 ->
    degree_dwork_wrt_expr n1 (dw_infer e1 e2 wl1)
  | degree_wrt_expr_dw_infer_app : forall n1 A1 e1 e2 wl1,
    degree_expr_wrt_expr n1 A1 ->
    degree_expr_wrt_expr n1 e1 ->
    degree_expr_wrt_expr n1 e2 ->
    degree_dworklist_wrt_expr (S n1) wl1 ->
    degree_dwork_wrt_expr n1 (dw_infer_app A1 e1 e2 wl1)
  | degree_wrt_expr_dw_reduce : forall n1 e1 wl1,
    degree_expr_wrt_expr n1 e1 ->
    degree_dworklist_wrt_expr (S n1) wl1 ->
    degree_dwork_wrt_expr n1 (dw_reduce e1 wl1)
  | degree_wrt_expr_dw_compact : forall n1 A1 B1,
    degree_expr_wrt_expr n1 A1 ->
    degree_expr_wrt_expr n1 B1 ->
    degree_dwork_wrt_expr n1 (dw_compact A1 B1)

with degree_dworklist_wrt_expr : nat -> dworklist -> Prop :=
  | degree_wrt_expr_dwl_nil : forall n1,
    degree_dworklist_wrt_expr n1 (dwl_nil)
  | degree_wrt_expr_dwl_cons : forall n1 wl1 w1,
    degree_dworklist_wrt_expr n1 wl1 ->
    degree_dwork_wrt_expr n1 w1 ->
    degree_dworklist_wrt_expr n1 (dwl_cons wl1 w1)
  | degree_wrt_expr_dwl_bind : forall n1 wl1 x1 A1,
    degree_dworklist_wrt_expr n1 wl1 ->
    degree_expr_wrt_expr n1 A1 ->
    degree_dworklist_wrt_expr n1 (dwl_bind wl1 x1 A1).

Scheme degree_dwork_wrt_expr_ind' := Induction for degree_dwork_wrt_expr Sort Prop
  with degree_dworklist_wrt_expr_ind' := Induction for degree_dworklist_wrt_expr Sort Prop.

Definition degree_dwork_wrt_expr_degree_dworklist_wrt_expr_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (conj (degree_dwork_wrt_expr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (degree_dworklist_wrt_expr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Hint Constructors degree_dwork_wrt_expr : core lngen.

Hint Constructors degree_dworklist_wrt_expr : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_expr : expr -> Set :=
  | lc_set_e_var_f : forall x1,
    lc_set_expr (e_var_f x1)
  | lc_set_e_kind : forall k1,
    lc_set_expr (e_kind k1)
  | lc_set_e_num : forall n1,
    lc_set_expr (e_num n1)
  | lc_set_e_int :
    lc_set_expr (e_int)
  | lc_set_e_bot : forall A1,
    lc_set_expr A1 ->
    lc_set_expr (e_bot A1)
  | lc_set_e_app : forall e1 e2,
    lc_set_expr e1 ->
    lc_set_expr e2 ->
    lc_set_expr (e_app e1 e2)
  | lc_set_e_abs : forall A1 b1,
    lc_set_expr A1 ->
    (forall x1 : exprvar, lc_set_body (open_body_wrt_expr b1 (e_var_f x1))) ->
    lc_set_expr (e_abs A1 b1)
  | lc_set_e_pi : forall A1 B1,
    lc_set_expr A1 ->
    (forall x1 : exprvar, lc_set_expr (open_expr_wrt_expr B1 (e_var_f x1))) ->
    lc_set_expr (e_pi A1 B1)
  | lc_set_e_bind : forall A1 b1,
    lc_set_expr A1 ->
    (forall x1 : exprvar, lc_set_body (open_body_wrt_expr b1 (e_var_f x1))) ->
    lc_set_expr (e_bind A1 b1)
  | lc_set_e_all : forall A1 B1,
    lc_set_expr A1 ->
    (forall x1 : exprvar, lc_set_expr (open_expr_wrt_expr B1 (e_var_f x1))) ->
    lc_set_expr (e_all A1 B1)
  | lc_set_e_castup : forall A1 e1,
    lc_set_expr A1 ->
    lc_set_expr e1 ->
    lc_set_expr (e_castup A1 e1)
  | lc_set_e_castdn : forall e1,
    lc_set_expr e1 ->
    lc_set_expr (e_castdn e1)

with lc_set_body : body -> Set :=
  | lc_set_b_anno : forall e1 A1,
    lc_set_expr e1 ->
    lc_set_expr A1 ->
    lc_set_body (b_anno e1 A1).

Scheme lc_expr_ind' := Induction for lc_expr Sort Prop
  with lc_body_ind' := Induction for lc_body Sort Prop.

Definition lc_expr_lc_body_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (conj (lc_expr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (lc_body_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)).

Scheme lc_set_expr_ind' := Induction for lc_set_expr Sort Prop
  with lc_set_body_ind' := Induction for lc_set_body Sort Prop.

Definition lc_set_expr_lc_set_body_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (conj (lc_set_expr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (lc_set_body_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)).

Scheme lc_set_expr_rec' := Induction for lc_set_expr Sort Set
  with lc_set_body_rec' := Induction for lc_set_body Sort Set.

Definition lc_set_expr_lc_set_body_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (pair (lc_set_expr_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (lc_set_body_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)).

Hint Constructors lc_expr : core lngen.

Hint Constructors lc_body : core lngen.

Hint Constructors lc_set_expr : core lngen.

Hint Constructors lc_set_body : core lngen.

Inductive lc_set_context : context -> Set :=
  | lc_set_ctx_nil :
    lc_set_context (ctx_nil)
  | lc_set_ctx_cons : forall G1 x1 A1,
    lc_set_context G1 ->
    lc_set_expr A1 ->
    lc_set_context (ctx_cons G1 x1 A1).

Scheme lc_context_ind' := Induction for lc_context Sort Prop.

Definition lc_context_mutind :=
  fun H1 H2 H3 =>
  lc_context_ind' H1 H2 H3.

Scheme lc_set_context_ind' := Induction for lc_set_context Sort Prop.

Definition lc_set_context_mutind :=
  fun H1 H2 H3 =>
  lc_set_context_ind' H1 H2 H3.

Scheme lc_set_context_rec' := Induction for lc_set_context Sort Set.

Definition lc_set_context_mutrec :=
  fun H1 H2 H3 =>
  lc_set_context_rec' H1 H2 H3.

Hint Constructors lc_context : core lngen.

Hint Constructors lc_set_context : core lngen.

Inductive lc_set_obindd : obindd -> Set :=
  | lc_set_dob_none :
    lc_set_obindd (dob_none)
  | lc_set_dob_bind : forall x1 A1,
    lc_set_expr A1 ->
    lc_set_obindd (dob_bind x1 A1).

Scheme lc_obindd_ind' := Induction for lc_obindd Sort Prop.

Definition lc_obindd_mutind :=
  fun H1 H2 H3 =>
  lc_obindd_ind' H1 H2 H3.

Scheme lc_set_obindd_ind' := Induction for lc_set_obindd Sort Prop.

Definition lc_set_obindd_mutind :=
  fun H1 H2 H3 =>
  lc_set_obindd_ind' H1 H2 H3.

Scheme lc_set_obindd_rec' := Induction for lc_set_obindd Sort Set.

Definition lc_set_obindd_mutrec :=
  fun H1 H2 H3 =>
  lc_set_obindd_rec' H1 H2 H3.

Hint Constructors lc_obindd : core lngen.

Hint Constructors lc_set_obindd : core lngen.

Inductive lc_set_dwork : dwork -> Set :=
  | lc_set_dw_check : forall ob1 e1 e2 A1,
    lc_set_obindd ob1 ->
    lc_set_expr e1 ->
    lc_set_expr e2 ->
    lc_set_expr A1 ->
    lc_set_dwork (dw_check ob1 e1 e2 A1)
  | lc_set_dw_infer : forall e1 e2 wl1,
    lc_set_expr e1 ->
    lc_set_expr e2 ->
    (forall x1 : exprvar, lc_set_dworklist (open_dworklist_wrt_expr wl1 (e_var_f x1))) ->
    lc_set_dwork (dw_infer e1 e2 wl1)
  | lc_set_dw_infer_app : forall A1 e1 e2 wl1,
    lc_set_expr A1 ->
    lc_set_expr e1 ->
    lc_set_expr e2 ->
    (forall x1 : exprvar, lc_set_dworklist (open_dworklist_wrt_expr wl1 (e_var_f x1))) ->
    lc_set_dwork (dw_infer_app A1 e1 e2 wl1)
  | lc_set_dw_reduce : forall e1 wl1,
    lc_set_expr e1 ->
    (forall x1 : exprvar, lc_set_dworklist (open_dworklist_wrt_expr wl1 (e_var_f x1))) ->
    lc_set_dwork (dw_reduce e1 wl1)
  | lc_set_dw_compact : forall A1 B1,
    lc_set_expr A1 ->
    lc_set_expr B1 ->
    lc_set_dwork (dw_compact A1 B1)

with lc_set_dworklist : dworklist -> Set :=
  | lc_set_dwl_nil :
    lc_set_dworklist (dwl_nil)
  | lc_set_dwl_cons : forall wl1 w1,
    lc_set_dworklist wl1 ->
    lc_set_dwork w1 ->
    lc_set_dworklist (dwl_cons wl1 w1)
  | lc_set_dwl_bind : forall wl1 x1 A1,
    lc_set_dworklist wl1 ->
    lc_set_expr A1 ->
    lc_set_dworklist (dwl_bind wl1 x1 A1).

Scheme lc_dwork_ind' := Induction for lc_dwork Sort Prop
  with lc_dworklist_ind' := Induction for lc_dworklist Sort Prop.

Definition lc_dwork_lc_dworklist_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (conj (lc_dwork_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (lc_dworklist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Scheme lc_set_dwork_ind' := Induction for lc_set_dwork Sort Prop
  with lc_set_dworklist_ind' := Induction for lc_set_dworklist Sort Prop.

Definition lc_set_dwork_lc_set_dworklist_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (conj (lc_set_dwork_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (lc_set_dworklist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Scheme lc_set_dwork_rec' := Induction for lc_set_dwork Sort Set
  with lc_set_dworklist_rec' := Induction for lc_set_dworklist Sort Set.

Definition lc_set_dwork_lc_set_dworklist_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (pair (lc_set_dwork_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (lc_set_dworklist_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Hint Constructors lc_dwork : core lngen.

Hint Constructors lc_dworklist : core lngen.

Hint Constructors lc_set_dwork : core lngen.

Hint Constructors lc_set_dworklist : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_expr_wrt_expr e1 := forall x1, lc_expr (open_expr_wrt_expr e1 (e_var_f x1)).

Definition body_body_wrt_expr b1 := forall x1, lc_body (open_body_wrt_expr b1 (e_var_f x1)).

Hint Unfold body_expr_wrt_expr : core.

Hint Unfold body_body_wrt_expr : core.

Definition body_context_wrt_expr G1 := forall x1, lc_context (open_context_wrt_expr G1 (e_var_f x1)).

Hint Unfold body_context_wrt_expr : core.

Definition body_obindd_wrt_expr ob1 := forall x1, lc_obindd (open_obindd_wrt_expr ob1 (e_var_f x1)).

Hint Unfold body_obindd_wrt_expr : core.

Definition body_dwork_wrt_expr w1 := forall x1, lc_dwork (open_dwork_wrt_expr w1 (e_var_f x1)).

Definition body_dworklist_wrt_expr wl1 := forall x1, lc_dworklist (open_dworklist_wrt_expr wl1 (e_var_f x1)).

Hint Unfold body_dwork_wrt_expr : core.

Hint Unfold body_dworklist_wrt_expr : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_kind_min_mutual :
(forall k1, 1 <= size_kind k1).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_kind_min :
forall k1, 1 <= size_kind k1.
Proof.
pose proof size_kind_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_kind_min : lngen.

(* begin hide *)

Lemma size_expr_min_size_body_min_mutual :
(forall e1, 1 <= size_expr e1) /\
(forall b1, 1 <= size_body b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_expr_min :
forall e1, 1 <= size_expr e1.
Proof.
pose proof size_expr_min_size_body_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_expr_min : lngen.

Lemma size_body_min :
forall b1, 1 <= size_body b1.
Proof.
pose proof size_expr_min_size_body_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_body_min : lngen.

(* begin hide *)

Lemma size_context_min_mutual :
(forall G1, 1 <= size_context G1).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_context_min :
forall G1, 1 <= size_context G1.
Proof.
pose proof size_context_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_context_min : lngen.

(* begin hide *)

Lemma size_dir_min_mutual :
(forall d1, 1 <= size_dir d1).
Proof.
apply_mutual_ind dir_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_dir_min :
forall d1, 1 <= size_dir d1.
Proof.
pose proof size_dir_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dir_min : lngen.

(* begin hide *)

Lemma size_obindd_min_mutual :
(forall ob1, 1 <= size_obindd ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_obindd_min :
forall ob1, 1 <= size_obindd ob1.
Proof.
pose proof size_obindd_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_obindd_min : lngen.

(* begin hide *)

Lemma size_dwork_min_size_dworklist_min_mutual :
(forall w1, 1 <= size_dwork w1) /\
(forall wl1, 1 <= size_dworklist wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_dwork_min :
forall w1, 1 <= size_dwork w1.
Proof.
pose proof size_dwork_min_size_dworklist_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dwork_min : lngen.

Lemma size_dworklist_min :
forall wl1, 1 <= size_dworklist wl1.
Proof.
pose proof size_dwork_min_size_dworklist_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dworklist_min : lngen.

(* begin hide *)

Lemma size_expr_close_expr_wrt_expr_rec_size_body_close_body_wrt_expr_rec_mutual :
(forall e1 x1 n1,
  size_expr (close_expr_wrt_expr_rec n1 x1 e1) = size_expr e1) /\
(forall b1 x1 n1,
  size_body (close_body_wrt_expr_rec n1 x1 b1) = size_body b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_expr_close_expr_wrt_expr_rec :
forall e1 x1 n1,
  size_expr (close_expr_wrt_expr_rec n1 x1 e1) = size_expr e1.
Proof.
pose proof size_expr_close_expr_wrt_expr_rec_size_body_close_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_expr_close_expr_wrt_expr_rec : lngen.
Hint Rewrite size_expr_close_expr_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_body_close_body_wrt_expr_rec :
forall b1 x1 n1,
  size_body (close_body_wrt_expr_rec n1 x1 b1) = size_body b1.
Proof.
pose proof size_expr_close_expr_wrt_expr_rec_size_body_close_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_body_close_body_wrt_expr_rec : lngen.
Hint Rewrite size_body_close_body_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_context_close_context_wrt_expr_rec_mutual :
(forall G1 x1 n1,
  size_context (close_context_wrt_expr_rec n1 x1 G1) = size_context G1).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_context_close_context_wrt_expr_rec :
forall G1 x1 n1,
  size_context (close_context_wrt_expr_rec n1 x1 G1) = size_context G1.
Proof.
pose proof size_context_close_context_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_context_close_context_wrt_expr_rec : lngen.
Hint Rewrite size_context_close_context_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_obindd_close_obindd_wrt_expr_rec_mutual :
(forall ob1 x1 n1,
  size_obindd (close_obindd_wrt_expr_rec n1 x1 ob1) = size_obindd ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_obindd_close_obindd_wrt_expr_rec :
forall ob1 x1 n1,
  size_obindd (close_obindd_wrt_expr_rec n1 x1 ob1) = size_obindd ob1.
Proof.
pose proof size_obindd_close_obindd_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_obindd_close_obindd_wrt_expr_rec : lngen.
Hint Rewrite size_obindd_close_obindd_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dwork_close_dwork_wrt_expr_rec_size_dworklist_close_dworklist_wrt_expr_rec_mutual :
(forall w1 x1 n1,
  size_dwork (close_dwork_wrt_expr_rec n1 x1 w1) = size_dwork w1) /\
(forall wl1 x1 n1,
  size_dworklist (close_dworklist_wrt_expr_rec n1 x1 wl1) = size_dworklist wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dwork_close_dwork_wrt_expr_rec :
forall w1 x1 n1,
  size_dwork (close_dwork_wrt_expr_rec n1 x1 w1) = size_dwork w1.
Proof.
pose proof size_dwork_close_dwork_wrt_expr_rec_size_dworklist_close_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dwork_close_dwork_wrt_expr_rec : lngen.
Hint Rewrite size_dwork_close_dwork_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dworklist_close_dworklist_wrt_expr_rec :
forall wl1 x1 n1,
  size_dworklist (close_dworklist_wrt_expr_rec n1 x1 wl1) = size_dworklist wl1.
Proof.
pose proof size_dwork_close_dwork_wrt_expr_rec_size_dworklist_close_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dworklist_close_dworklist_wrt_expr_rec : lngen.
Hint Rewrite size_dworklist_close_dworklist_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_expr_close_expr_wrt_expr :
forall e1 x1,
  size_expr (close_expr_wrt_expr x1 e1) = size_expr e1.
Proof.
unfold close_expr_wrt_expr; default_simp.
Qed.

Hint Resolve size_expr_close_expr_wrt_expr : lngen.
Hint Rewrite size_expr_close_expr_wrt_expr using solve [auto] : lngen.

Lemma size_body_close_body_wrt_expr :
forall b1 x1,
  size_body (close_body_wrt_expr x1 b1) = size_body b1.
Proof.
unfold close_body_wrt_expr; default_simp.
Qed.

Hint Resolve size_body_close_body_wrt_expr : lngen.
Hint Rewrite size_body_close_body_wrt_expr using solve [auto] : lngen.

Lemma size_context_close_context_wrt_expr :
forall G1 x1,
  size_context (close_context_wrt_expr x1 G1) = size_context G1.
Proof.
unfold close_context_wrt_expr; default_simp.
Qed.

Hint Resolve size_context_close_context_wrt_expr : lngen.
Hint Rewrite size_context_close_context_wrt_expr using solve [auto] : lngen.

Lemma size_obindd_close_obindd_wrt_expr :
forall ob1 x1,
  size_obindd (close_obindd_wrt_expr x1 ob1) = size_obindd ob1.
Proof.
unfold close_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve size_obindd_close_obindd_wrt_expr : lngen.
Hint Rewrite size_obindd_close_obindd_wrt_expr using solve [auto] : lngen.

Lemma size_dwork_close_dwork_wrt_expr :
forall w1 x1,
  size_dwork (close_dwork_wrt_expr x1 w1) = size_dwork w1.
Proof.
unfold close_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve size_dwork_close_dwork_wrt_expr : lngen.
Hint Rewrite size_dwork_close_dwork_wrt_expr using solve [auto] : lngen.

Lemma size_dworklist_close_dworklist_wrt_expr :
forall wl1 x1,
  size_dworklist (close_dworklist_wrt_expr x1 wl1) = size_dworklist wl1.
Proof.
unfold close_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve size_dworklist_close_dworklist_wrt_expr : lngen.
Hint Rewrite size_dworklist_close_dworklist_wrt_expr using solve [auto] : lngen.

(* begin hide *)

Lemma size_expr_open_expr_wrt_expr_rec_size_body_open_body_wrt_expr_rec_mutual :
(forall e1 e2 n1,
  size_expr e1 <= size_expr (open_expr_wrt_expr_rec n1 e2 e1)) /\
(forall b1 e1 n1,
  size_body b1 <= size_body (open_body_wrt_expr_rec n1 e1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_expr_open_expr_wrt_expr_rec :
forall e1 e2 n1,
  size_expr e1 <= size_expr (open_expr_wrt_expr_rec n1 e2 e1).
Proof.
pose proof size_expr_open_expr_wrt_expr_rec_size_body_open_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_expr_open_expr_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_body_open_body_wrt_expr_rec :
forall b1 e1 n1,
  size_body b1 <= size_body (open_body_wrt_expr_rec n1 e1 b1).
Proof.
pose proof size_expr_open_expr_wrt_expr_rec_size_body_open_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_body_open_body_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_context_open_context_wrt_expr_rec_mutual :
(forall G1 e1 n1,
  size_context G1 <= size_context (open_context_wrt_expr_rec n1 e1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_context_open_context_wrt_expr_rec :
forall G1 e1 n1,
  size_context G1 <= size_context (open_context_wrt_expr_rec n1 e1 G1).
Proof.
pose proof size_context_open_context_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_context_open_context_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_obindd_open_obindd_wrt_expr_rec_mutual :
(forall ob1 e1 n1,
  size_obindd ob1 <= size_obindd (open_obindd_wrt_expr_rec n1 e1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_obindd_open_obindd_wrt_expr_rec :
forall ob1 e1 n1,
  size_obindd ob1 <= size_obindd (open_obindd_wrt_expr_rec n1 e1 ob1).
Proof.
pose proof size_obindd_open_obindd_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_obindd_open_obindd_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dwork_open_dwork_wrt_expr_rec_size_dworklist_open_dworklist_wrt_expr_rec_mutual :
(forall w1 e1 n1,
  size_dwork w1 <= size_dwork (open_dwork_wrt_expr_rec n1 e1 w1)) /\
(forall wl1 e1 n1,
  size_dworklist wl1 <= size_dworklist (open_dworklist_wrt_expr_rec n1 e1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dwork_open_dwork_wrt_expr_rec :
forall w1 e1 n1,
  size_dwork w1 <= size_dwork (open_dwork_wrt_expr_rec n1 e1 w1).
Proof.
pose proof size_dwork_open_dwork_wrt_expr_rec_size_dworklist_open_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dwork_open_dwork_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dworklist_open_dworklist_wrt_expr_rec :
forall wl1 e1 n1,
  size_dworklist wl1 <= size_dworklist (open_dworklist_wrt_expr_rec n1 e1 wl1).
Proof.
pose proof size_dwork_open_dwork_wrt_expr_rec_size_dworklist_open_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dworklist_open_dworklist_wrt_expr_rec : lngen.

(* end hide *)

Lemma size_expr_open_expr_wrt_expr :
forall e1 e2,
  size_expr e1 <= size_expr (open_expr_wrt_expr e1 e2).
Proof.
unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve size_expr_open_expr_wrt_expr : lngen.

Lemma size_body_open_body_wrt_expr :
forall b1 e1,
  size_body b1 <= size_body (open_body_wrt_expr b1 e1).
Proof.
unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve size_body_open_body_wrt_expr : lngen.

Lemma size_context_open_context_wrt_expr :
forall G1 e1,
  size_context G1 <= size_context (open_context_wrt_expr G1 e1).
Proof.
unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve size_context_open_context_wrt_expr : lngen.

Lemma size_obindd_open_obindd_wrt_expr :
forall ob1 e1,
  size_obindd ob1 <= size_obindd (open_obindd_wrt_expr ob1 e1).
Proof.
unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve size_obindd_open_obindd_wrt_expr : lngen.

Lemma size_dwork_open_dwork_wrt_expr :
forall w1 e1,
  size_dwork w1 <= size_dwork (open_dwork_wrt_expr w1 e1).
Proof.
unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve size_dwork_open_dwork_wrt_expr : lngen.

Lemma size_dworklist_open_dworklist_wrt_expr :
forall wl1 e1,
  size_dworklist wl1 <= size_dworklist (open_dworklist_wrt_expr wl1 e1).
Proof.
unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve size_dworklist_open_dworklist_wrt_expr : lngen.

(* begin hide *)

Lemma size_expr_open_expr_wrt_expr_rec_var_size_body_open_body_wrt_expr_rec_var_mutual :
(forall e1 x1 n1,
  size_expr (open_expr_wrt_expr_rec n1 (e_var_f x1) e1) = size_expr e1) /\
(forall b1 x1 n1,
  size_body (open_body_wrt_expr_rec n1 (e_var_f x1) b1) = size_body b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_expr_open_expr_wrt_expr_rec_var :
forall e1 x1 n1,
  size_expr (open_expr_wrt_expr_rec n1 (e_var_f x1) e1) = size_expr e1.
Proof.
pose proof size_expr_open_expr_wrt_expr_rec_var_size_body_open_body_wrt_expr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_expr_open_expr_wrt_expr_rec_var : lngen.
Hint Rewrite size_expr_open_expr_wrt_expr_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_body_open_body_wrt_expr_rec_var :
forall b1 x1 n1,
  size_body (open_body_wrt_expr_rec n1 (e_var_f x1) b1) = size_body b1.
Proof.
pose proof size_expr_open_expr_wrt_expr_rec_var_size_body_open_body_wrt_expr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_body_open_body_wrt_expr_rec_var : lngen.
Hint Rewrite size_body_open_body_wrt_expr_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_context_open_context_wrt_expr_rec_var_mutual :
(forall G1 x1 n1,
  size_context (open_context_wrt_expr_rec n1 (e_var_f x1) G1) = size_context G1).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_context_open_context_wrt_expr_rec_var :
forall G1 x1 n1,
  size_context (open_context_wrt_expr_rec n1 (e_var_f x1) G1) = size_context G1.
Proof.
pose proof size_context_open_context_wrt_expr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_context_open_context_wrt_expr_rec_var : lngen.
Hint Rewrite size_context_open_context_wrt_expr_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_obindd_open_obindd_wrt_expr_rec_var_mutual :
(forall ob1 x1 n1,
  size_obindd (open_obindd_wrt_expr_rec n1 (e_var_f x1) ob1) = size_obindd ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_obindd_open_obindd_wrt_expr_rec_var :
forall ob1 x1 n1,
  size_obindd (open_obindd_wrt_expr_rec n1 (e_var_f x1) ob1) = size_obindd ob1.
Proof.
pose proof size_obindd_open_obindd_wrt_expr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_obindd_open_obindd_wrt_expr_rec_var : lngen.
Hint Rewrite size_obindd_open_obindd_wrt_expr_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dwork_open_dwork_wrt_expr_rec_var_size_dworklist_open_dworklist_wrt_expr_rec_var_mutual :
(forall w1 x1 n1,
  size_dwork (open_dwork_wrt_expr_rec n1 (e_var_f x1) w1) = size_dwork w1) /\
(forall wl1 x1 n1,
  size_dworklist (open_dworklist_wrt_expr_rec n1 (e_var_f x1) wl1) = size_dworklist wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dwork_open_dwork_wrt_expr_rec_var :
forall w1 x1 n1,
  size_dwork (open_dwork_wrt_expr_rec n1 (e_var_f x1) w1) = size_dwork w1.
Proof.
pose proof size_dwork_open_dwork_wrt_expr_rec_var_size_dworklist_open_dworklist_wrt_expr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dwork_open_dwork_wrt_expr_rec_var : lngen.
Hint Rewrite size_dwork_open_dwork_wrt_expr_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dworklist_open_dworklist_wrt_expr_rec_var :
forall wl1 x1 n1,
  size_dworklist (open_dworklist_wrt_expr_rec n1 (e_var_f x1) wl1) = size_dworklist wl1.
Proof.
pose proof size_dwork_open_dwork_wrt_expr_rec_var_size_dworklist_open_dworklist_wrt_expr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dworklist_open_dworklist_wrt_expr_rec_var : lngen.
Hint Rewrite size_dworklist_open_dworklist_wrt_expr_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_expr_open_expr_wrt_expr_var :
forall e1 x1,
  size_expr (open_expr_wrt_expr e1 (e_var_f x1)) = size_expr e1.
Proof.
unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve size_expr_open_expr_wrt_expr_var : lngen.
Hint Rewrite size_expr_open_expr_wrt_expr_var using solve [auto] : lngen.

Lemma size_body_open_body_wrt_expr_var :
forall b1 x1,
  size_body (open_body_wrt_expr b1 (e_var_f x1)) = size_body b1.
Proof.
unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve size_body_open_body_wrt_expr_var : lngen.
Hint Rewrite size_body_open_body_wrt_expr_var using solve [auto] : lngen.

Lemma size_context_open_context_wrt_expr_var :
forall G1 x1,
  size_context (open_context_wrt_expr G1 (e_var_f x1)) = size_context G1.
Proof.
unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve size_context_open_context_wrt_expr_var : lngen.
Hint Rewrite size_context_open_context_wrt_expr_var using solve [auto] : lngen.

Lemma size_obindd_open_obindd_wrt_expr_var :
forall ob1 x1,
  size_obindd (open_obindd_wrt_expr ob1 (e_var_f x1)) = size_obindd ob1.
Proof.
unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve size_obindd_open_obindd_wrt_expr_var : lngen.
Hint Rewrite size_obindd_open_obindd_wrt_expr_var using solve [auto] : lngen.

Lemma size_dwork_open_dwork_wrt_expr_var :
forall w1 x1,
  size_dwork (open_dwork_wrt_expr w1 (e_var_f x1)) = size_dwork w1.
Proof.
unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve size_dwork_open_dwork_wrt_expr_var : lngen.
Hint Rewrite size_dwork_open_dwork_wrt_expr_var using solve [auto] : lngen.

Lemma size_dworklist_open_dworklist_wrt_expr_var :
forall wl1 x1,
  size_dworklist (open_dworklist_wrt_expr wl1 (e_var_f x1)) = size_dworklist wl1.
Proof.
unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve size_dworklist_open_dworklist_wrt_expr_var : lngen.
Hint Rewrite size_dworklist_open_dworklist_wrt_expr_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_expr_wrt_expr_S_degree_body_wrt_expr_S_mutual :
(forall n1 e1,
  degree_expr_wrt_expr n1 e1 ->
  degree_expr_wrt_expr (S n1) e1) /\
(forall n1 b1,
  degree_body_wrt_expr n1 b1 ->
  degree_body_wrt_expr (S n1) b1).
Proof.
apply_mutual_ind degree_expr_wrt_expr_degree_body_wrt_expr_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_expr_wrt_expr_S :
forall n1 e1,
  degree_expr_wrt_expr n1 e1 ->
  degree_expr_wrt_expr (S n1) e1.
Proof.
pose proof degree_expr_wrt_expr_S_degree_body_wrt_expr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_expr_wrt_expr_S : lngen.

Lemma degree_body_wrt_expr_S :
forall n1 b1,
  degree_body_wrt_expr n1 b1 ->
  degree_body_wrt_expr (S n1) b1.
Proof.
pose proof degree_expr_wrt_expr_S_degree_body_wrt_expr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_body_wrt_expr_S : lngen.

(* begin hide *)

Lemma degree_context_wrt_expr_S_mutual :
(forall n1 G1,
  degree_context_wrt_expr n1 G1 ->
  degree_context_wrt_expr (S n1) G1).
Proof.
apply_mutual_ind degree_context_wrt_expr_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_context_wrt_expr_S :
forall n1 G1,
  degree_context_wrt_expr n1 G1 ->
  degree_context_wrt_expr (S n1) G1.
Proof.
pose proof degree_context_wrt_expr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_context_wrt_expr_S : lngen.

(* begin hide *)

Lemma degree_obindd_wrt_expr_S_mutual :
(forall n1 ob1,
  degree_obindd_wrt_expr n1 ob1 ->
  degree_obindd_wrt_expr (S n1) ob1).
Proof.
apply_mutual_ind degree_obindd_wrt_expr_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_obindd_wrt_expr_S :
forall n1 ob1,
  degree_obindd_wrt_expr n1 ob1 ->
  degree_obindd_wrt_expr (S n1) ob1.
Proof.
pose proof degree_obindd_wrt_expr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_obindd_wrt_expr_S : lngen.

(* begin hide *)

Lemma degree_dwork_wrt_expr_S_degree_dworklist_wrt_expr_S_mutual :
(forall n1 w1,
  degree_dwork_wrt_expr n1 w1 ->
  degree_dwork_wrt_expr (S n1) w1) /\
(forall n1 wl1,
  degree_dworklist_wrt_expr n1 wl1 ->
  degree_dworklist_wrt_expr (S n1) wl1).
Proof.
apply_mutual_ind degree_dwork_wrt_expr_degree_dworklist_wrt_expr_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_dwork_wrt_expr_S :
forall n1 w1,
  degree_dwork_wrt_expr n1 w1 ->
  degree_dwork_wrt_expr (S n1) w1.
Proof.
pose proof degree_dwork_wrt_expr_S_degree_dworklist_wrt_expr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dwork_wrt_expr_S : lngen.

Lemma degree_dworklist_wrt_expr_S :
forall n1 wl1,
  degree_dworklist_wrt_expr n1 wl1 ->
  degree_dworklist_wrt_expr (S n1) wl1.
Proof.
pose proof degree_dwork_wrt_expr_S_degree_dworklist_wrt_expr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dworklist_wrt_expr_S : lngen.

Lemma degree_expr_wrt_expr_O :
forall n1 e1,
  degree_expr_wrt_expr O e1 ->
  degree_expr_wrt_expr n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_expr_wrt_expr_O : lngen.

Lemma degree_body_wrt_expr_O :
forall n1 b1,
  degree_body_wrt_expr O b1 ->
  degree_body_wrt_expr n1 b1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_body_wrt_expr_O : lngen.

Lemma degree_context_wrt_expr_O :
forall n1 G1,
  degree_context_wrt_expr O G1 ->
  degree_context_wrt_expr n1 G1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_context_wrt_expr_O : lngen.

Lemma degree_obindd_wrt_expr_O :
forall n1 ob1,
  degree_obindd_wrt_expr O ob1 ->
  degree_obindd_wrt_expr n1 ob1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_obindd_wrt_expr_O : lngen.

Lemma degree_dwork_wrt_expr_O :
forall n1 w1,
  degree_dwork_wrt_expr O w1 ->
  degree_dwork_wrt_expr n1 w1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_dwork_wrt_expr_O : lngen.

Lemma degree_dworklist_wrt_expr_O :
forall n1 wl1,
  degree_dworklist_wrt_expr O wl1 ->
  degree_dworklist_wrt_expr n1 wl1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_dworklist_wrt_expr_O : lngen.

(* begin hide *)

Lemma degree_expr_wrt_expr_close_expr_wrt_expr_rec_degree_body_wrt_expr_close_body_wrt_expr_rec_mutual :
(forall e1 x1 n1,
  degree_expr_wrt_expr n1 e1 ->
  degree_expr_wrt_expr (S n1) (close_expr_wrt_expr_rec n1 x1 e1)) /\
(forall b1 x1 n1,
  degree_body_wrt_expr n1 b1 ->
  degree_body_wrt_expr (S n1) (close_body_wrt_expr_rec n1 x1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_expr_wrt_expr_close_expr_wrt_expr_rec :
forall e1 x1 n1,
  degree_expr_wrt_expr n1 e1 ->
  degree_expr_wrt_expr (S n1) (close_expr_wrt_expr_rec n1 x1 e1).
Proof.
pose proof degree_expr_wrt_expr_close_expr_wrt_expr_rec_degree_body_wrt_expr_close_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_expr_wrt_expr_close_expr_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_expr_close_body_wrt_expr_rec :
forall b1 x1 n1,
  degree_body_wrt_expr n1 b1 ->
  degree_body_wrt_expr (S n1) (close_body_wrt_expr_rec n1 x1 b1).
Proof.
pose proof degree_expr_wrt_expr_close_expr_wrt_expr_rec_degree_body_wrt_expr_close_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_body_wrt_expr_close_body_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_context_wrt_expr_close_context_wrt_expr_rec_mutual :
(forall G1 x1 n1,
  degree_context_wrt_expr n1 G1 ->
  degree_context_wrt_expr (S n1) (close_context_wrt_expr_rec n1 x1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_context_wrt_expr_close_context_wrt_expr_rec :
forall G1 x1 n1,
  degree_context_wrt_expr n1 G1 ->
  degree_context_wrt_expr (S n1) (close_context_wrt_expr_rec n1 x1 G1).
Proof.
pose proof degree_context_wrt_expr_close_context_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_context_wrt_expr_close_context_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_obindd_wrt_expr_close_obindd_wrt_expr_rec_mutual :
(forall ob1 x1 n1,
  degree_obindd_wrt_expr n1 ob1 ->
  degree_obindd_wrt_expr (S n1) (close_obindd_wrt_expr_rec n1 x1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_obindd_wrt_expr_close_obindd_wrt_expr_rec :
forall ob1 x1 n1,
  degree_obindd_wrt_expr n1 ob1 ->
  degree_obindd_wrt_expr (S n1) (close_obindd_wrt_expr_rec n1 x1 ob1).
Proof.
pose proof degree_obindd_wrt_expr_close_obindd_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_obindd_wrt_expr_close_obindd_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dwork_wrt_expr_close_dwork_wrt_expr_rec_degree_dworklist_wrt_expr_close_dworklist_wrt_expr_rec_mutual :
(forall w1 x1 n1,
  degree_dwork_wrt_expr n1 w1 ->
  degree_dwork_wrt_expr (S n1) (close_dwork_wrt_expr_rec n1 x1 w1)) /\
(forall wl1 x1 n1,
  degree_dworklist_wrt_expr n1 wl1 ->
  degree_dworklist_wrt_expr (S n1) (close_dworklist_wrt_expr_rec n1 x1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dwork_wrt_expr_close_dwork_wrt_expr_rec :
forall w1 x1 n1,
  degree_dwork_wrt_expr n1 w1 ->
  degree_dwork_wrt_expr (S n1) (close_dwork_wrt_expr_rec n1 x1 w1).
Proof.
pose proof degree_dwork_wrt_expr_close_dwork_wrt_expr_rec_degree_dworklist_wrt_expr_close_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dwork_wrt_expr_close_dwork_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dworklist_wrt_expr_close_dworklist_wrt_expr_rec :
forall wl1 x1 n1,
  degree_dworklist_wrt_expr n1 wl1 ->
  degree_dworklist_wrt_expr (S n1) (close_dworklist_wrt_expr_rec n1 x1 wl1).
Proof.
pose proof degree_dwork_wrt_expr_close_dwork_wrt_expr_rec_degree_dworklist_wrt_expr_close_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dworklist_wrt_expr_close_dworklist_wrt_expr_rec : lngen.

(* end hide *)

Lemma degree_expr_wrt_expr_close_expr_wrt_expr :
forall e1 x1,
  degree_expr_wrt_expr 0 e1 ->
  degree_expr_wrt_expr 1 (close_expr_wrt_expr x1 e1).
Proof.
unfold close_expr_wrt_expr; default_simp.
Qed.

Hint Resolve degree_expr_wrt_expr_close_expr_wrt_expr : lngen.

Lemma degree_body_wrt_expr_close_body_wrt_expr :
forall b1 x1,
  degree_body_wrt_expr 0 b1 ->
  degree_body_wrt_expr 1 (close_body_wrt_expr x1 b1).
Proof.
unfold close_body_wrt_expr; default_simp.
Qed.

Hint Resolve degree_body_wrt_expr_close_body_wrt_expr : lngen.

Lemma degree_context_wrt_expr_close_context_wrt_expr :
forall G1 x1,
  degree_context_wrt_expr 0 G1 ->
  degree_context_wrt_expr 1 (close_context_wrt_expr x1 G1).
Proof.
unfold close_context_wrt_expr; default_simp.
Qed.

Hint Resolve degree_context_wrt_expr_close_context_wrt_expr : lngen.

Lemma degree_obindd_wrt_expr_close_obindd_wrt_expr :
forall ob1 x1,
  degree_obindd_wrt_expr 0 ob1 ->
  degree_obindd_wrt_expr 1 (close_obindd_wrt_expr x1 ob1).
Proof.
unfold close_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve degree_obindd_wrt_expr_close_obindd_wrt_expr : lngen.

Lemma degree_dwork_wrt_expr_close_dwork_wrt_expr :
forall w1 x1,
  degree_dwork_wrt_expr 0 w1 ->
  degree_dwork_wrt_expr 1 (close_dwork_wrt_expr x1 w1).
Proof.
unfold close_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve degree_dwork_wrt_expr_close_dwork_wrt_expr : lngen.

Lemma degree_dworklist_wrt_expr_close_dworklist_wrt_expr :
forall wl1 x1,
  degree_dworklist_wrt_expr 0 wl1 ->
  degree_dworklist_wrt_expr 1 (close_dworklist_wrt_expr x1 wl1).
Proof.
unfold close_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve degree_dworklist_wrt_expr_close_dworklist_wrt_expr : lngen.

(* begin hide *)

Lemma degree_expr_wrt_expr_close_expr_wrt_expr_rec_inv_degree_body_wrt_expr_close_body_wrt_expr_rec_inv_mutual :
(forall e1 x1 n1,
  degree_expr_wrt_expr (S n1) (close_expr_wrt_expr_rec n1 x1 e1) ->
  degree_expr_wrt_expr n1 e1) /\
(forall b1 x1 n1,
  degree_body_wrt_expr (S n1) (close_body_wrt_expr_rec n1 x1 b1) ->
  degree_body_wrt_expr n1 b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_expr_wrt_expr_close_expr_wrt_expr_rec_inv :
forall e1 x1 n1,
  degree_expr_wrt_expr (S n1) (close_expr_wrt_expr_rec n1 x1 e1) ->
  degree_expr_wrt_expr n1 e1.
Proof.
pose proof degree_expr_wrt_expr_close_expr_wrt_expr_rec_inv_degree_body_wrt_expr_close_body_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_expr_wrt_expr_close_expr_wrt_expr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_expr_close_body_wrt_expr_rec_inv :
forall b1 x1 n1,
  degree_body_wrt_expr (S n1) (close_body_wrt_expr_rec n1 x1 b1) ->
  degree_body_wrt_expr n1 b1.
Proof.
pose proof degree_expr_wrt_expr_close_expr_wrt_expr_rec_inv_degree_body_wrt_expr_close_body_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_body_wrt_expr_close_body_wrt_expr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_context_wrt_expr_close_context_wrt_expr_rec_inv_mutual :
(forall G1 x1 n1,
  degree_context_wrt_expr (S n1) (close_context_wrt_expr_rec n1 x1 G1) ->
  degree_context_wrt_expr n1 G1).
Proof.
apply_mutual_ind context_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_context_wrt_expr_close_context_wrt_expr_rec_inv :
forall G1 x1 n1,
  degree_context_wrt_expr (S n1) (close_context_wrt_expr_rec n1 x1 G1) ->
  degree_context_wrt_expr n1 G1.
Proof.
pose proof degree_context_wrt_expr_close_context_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_context_wrt_expr_close_context_wrt_expr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_obindd_wrt_expr_close_obindd_wrt_expr_rec_inv_mutual :
(forall ob1 x1 n1,
  degree_obindd_wrt_expr (S n1) (close_obindd_wrt_expr_rec n1 x1 ob1) ->
  degree_obindd_wrt_expr n1 ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_obindd_wrt_expr_close_obindd_wrt_expr_rec_inv :
forall ob1 x1 n1,
  degree_obindd_wrt_expr (S n1) (close_obindd_wrt_expr_rec n1 x1 ob1) ->
  degree_obindd_wrt_expr n1 ob1.
Proof.
pose proof degree_obindd_wrt_expr_close_obindd_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_obindd_wrt_expr_close_obindd_wrt_expr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dwork_wrt_expr_close_dwork_wrt_expr_rec_inv_degree_dworklist_wrt_expr_close_dworklist_wrt_expr_rec_inv_mutual :
(forall w1 x1 n1,
  degree_dwork_wrt_expr (S n1) (close_dwork_wrt_expr_rec n1 x1 w1) ->
  degree_dwork_wrt_expr n1 w1) /\
(forall wl1 x1 n1,
  degree_dworklist_wrt_expr (S n1) (close_dworklist_wrt_expr_rec n1 x1 wl1) ->
  degree_dworklist_wrt_expr n1 wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dwork_wrt_expr_close_dwork_wrt_expr_rec_inv :
forall w1 x1 n1,
  degree_dwork_wrt_expr (S n1) (close_dwork_wrt_expr_rec n1 x1 w1) ->
  degree_dwork_wrt_expr n1 w1.
Proof.
pose proof degree_dwork_wrt_expr_close_dwork_wrt_expr_rec_inv_degree_dworklist_wrt_expr_close_dworklist_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_dwork_wrt_expr_close_dwork_wrt_expr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dworklist_wrt_expr_close_dworklist_wrt_expr_rec_inv :
forall wl1 x1 n1,
  degree_dworklist_wrt_expr (S n1) (close_dworklist_wrt_expr_rec n1 x1 wl1) ->
  degree_dworklist_wrt_expr n1 wl1.
Proof.
pose proof degree_dwork_wrt_expr_close_dwork_wrt_expr_rec_inv_degree_dworklist_wrt_expr_close_dworklist_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_dworklist_wrt_expr_close_dworklist_wrt_expr_rec_inv : lngen.

(* end hide *)

Lemma degree_expr_wrt_expr_close_expr_wrt_expr_inv :
forall e1 x1,
  degree_expr_wrt_expr 1 (close_expr_wrt_expr x1 e1) ->
  degree_expr_wrt_expr 0 e1.
Proof.
unfold close_expr_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_expr_wrt_expr_close_expr_wrt_expr_inv : lngen.

Lemma degree_body_wrt_expr_close_body_wrt_expr_inv :
forall b1 x1,
  degree_body_wrt_expr 1 (close_body_wrt_expr x1 b1) ->
  degree_body_wrt_expr 0 b1.
Proof.
unfold close_body_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_body_wrt_expr_close_body_wrt_expr_inv : lngen.

Lemma degree_context_wrt_expr_close_context_wrt_expr_inv :
forall G1 x1,
  degree_context_wrt_expr 1 (close_context_wrt_expr x1 G1) ->
  degree_context_wrt_expr 0 G1.
Proof.
unfold close_context_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_context_wrt_expr_close_context_wrt_expr_inv : lngen.

Lemma degree_obindd_wrt_expr_close_obindd_wrt_expr_inv :
forall ob1 x1,
  degree_obindd_wrt_expr 1 (close_obindd_wrt_expr x1 ob1) ->
  degree_obindd_wrt_expr 0 ob1.
Proof.
unfold close_obindd_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_obindd_wrt_expr_close_obindd_wrt_expr_inv : lngen.

Lemma degree_dwork_wrt_expr_close_dwork_wrt_expr_inv :
forall w1 x1,
  degree_dwork_wrt_expr 1 (close_dwork_wrt_expr x1 w1) ->
  degree_dwork_wrt_expr 0 w1.
Proof.
unfold close_dwork_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_dwork_wrt_expr_close_dwork_wrt_expr_inv : lngen.

Lemma degree_dworklist_wrt_expr_close_dworklist_wrt_expr_inv :
forall wl1 x1,
  degree_dworklist_wrt_expr 1 (close_dworklist_wrt_expr x1 wl1) ->
  degree_dworklist_wrt_expr 0 wl1.
Proof.
unfold close_dworklist_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_dworklist_wrt_expr_close_dworklist_wrt_expr_inv : lngen.

(* begin hide *)

Lemma degree_expr_wrt_expr_open_expr_wrt_expr_rec_degree_body_wrt_expr_open_body_wrt_expr_rec_mutual :
(forall e1 e2 n1,
  degree_expr_wrt_expr (S n1) e1 ->
  degree_expr_wrt_expr n1 e2 ->
  degree_expr_wrt_expr n1 (open_expr_wrt_expr_rec n1 e2 e1)) /\
(forall b1 e1 n1,
  degree_body_wrt_expr (S n1) b1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_body_wrt_expr n1 (open_body_wrt_expr_rec n1 e1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_expr_wrt_expr_open_expr_wrt_expr_rec :
forall e1 e2 n1,
  degree_expr_wrt_expr (S n1) e1 ->
  degree_expr_wrt_expr n1 e2 ->
  degree_expr_wrt_expr n1 (open_expr_wrt_expr_rec n1 e2 e1).
Proof.
pose proof degree_expr_wrt_expr_open_expr_wrt_expr_rec_degree_body_wrt_expr_open_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_expr_wrt_expr_open_expr_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_expr_open_body_wrt_expr_rec :
forall b1 e1 n1,
  degree_body_wrt_expr (S n1) b1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_body_wrt_expr n1 (open_body_wrt_expr_rec n1 e1 b1).
Proof.
pose proof degree_expr_wrt_expr_open_expr_wrt_expr_rec_degree_body_wrt_expr_open_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_body_wrt_expr_open_body_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_context_wrt_expr_open_context_wrt_expr_rec_mutual :
(forall G1 e1 n1,
  degree_context_wrt_expr (S n1) G1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_context_wrt_expr n1 (open_context_wrt_expr_rec n1 e1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_context_wrt_expr_open_context_wrt_expr_rec :
forall G1 e1 n1,
  degree_context_wrt_expr (S n1) G1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_context_wrt_expr n1 (open_context_wrt_expr_rec n1 e1 G1).
Proof.
pose proof degree_context_wrt_expr_open_context_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_context_wrt_expr_open_context_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_obindd_wrt_expr_open_obindd_wrt_expr_rec_mutual :
(forall ob1 e1 n1,
  degree_obindd_wrt_expr (S n1) ob1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_obindd_wrt_expr n1 (open_obindd_wrt_expr_rec n1 e1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_obindd_wrt_expr_open_obindd_wrt_expr_rec :
forall ob1 e1 n1,
  degree_obindd_wrt_expr (S n1) ob1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_obindd_wrt_expr n1 (open_obindd_wrt_expr_rec n1 e1 ob1).
Proof.
pose proof degree_obindd_wrt_expr_open_obindd_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_obindd_wrt_expr_open_obindd_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dwork_wrt_expr_open_dwork_wrt_expr_rec_degree_dworklist_wrt_expr_open_dworklist_wrt_expr_rec_mutual :
(forall w1 e1 n1,
  degree_dwork_wrt_expr (S n1) w1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_dwork_wrt_expr n1 (open_dwork_wrt_expr_rec n1 e1 w1)) /\
(forall wl1 e1 n1,
  degree_dworklist_wrt_expr (S n1) wl1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_dworklist_wrt_expr n1 (open_dworklist_wrt_expr_rec n1 e1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dwork_wrt_expr_open_dwork_wrt_expr_rec :
forall w1 e1 n1,
  degree_dwork_wrt_expr (S n1) w1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_dwork_wrt_expr n1 (open_dwork_wrt_expr_rec n1 e1 w1).
Proof.
pose proof degree_dwork_wrt_expr_open_dwork_wrt_expr_rec_degree_dworklist_wrt_expr_open_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dwork_wrt_expr_open_dwork_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dworklist_wrt_expr_open_dworklist_wrt_expr_rec :
forall wl1 e1 n1,
  degree_dworklist_wrt_expr (S n1) wl1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_dworklist_wrt_expr n1 (open_dworklist_wrt_expr_rec n1 e1 wl1).
Proof.
pose proof degree_dwork_wrt_expr_open_dwork_wrt_expr_rec_degree_dworklist_wrt_expr_open_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dworklist_wrt_expr_open_dworklist_wrt_expr_rec : lngen.

(* end hide *)

Lemma degree_expr_wrt_expr_open_expr_wrt_expr :
forall e1 e2,
  degree_expr_wrt_expr 1 e1 ->
  degree_expr_wrt_expr 0 e2 ->
  degree_expr_wrt_expr 0 (open_expr_wrt_expr e1 e2).
Proof.
unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve degree_expr_wrt_expr_open_expr_wrt_expr : lngen.

Lemma degree_body_wrt_expr_open_body_wrt_expr :
forall b1 e1,
  degree_body_wrt_expr 1 b1 ->
  degree_expr_wrt_expr 0 e1 ->
  degree_body_wrt_expr 0 (open_body_wrt_expr b1 e1).
Proof.
unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve degree_body_wrt_expr_open_body_wrt_expr : lngen.

Lemma degree_context_wrt_expr_open_context_wrt_expr :
forall G1 e1,
  degree_context_wrt_expr 1 G1 ->
  degree_expr_wrt_expr 0 e1 ->
  degree_context_wrt_expr 0 (open_context_wrt_expr G1 e1).
Proof.
unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve degree_context_wrt_expr_open_context_wrt_expr : lngen.

Lemma degree_obindd_wrt_expr_open_obindd_wrt_expr :
forall ob1 e1,
  degree_obindd_wrt_expr 1 ob1 ->
  degree_expr_wrt_expr 0 e1 ->
  degree_obindd_wrt_expr 0 (open_obindd_wrt_expr ob1 e1).
Proof.
unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve degree_obindd_wrt_expr_open_obindd_wrt_expr : lngen.

Lemma degree_dwork_wrt_expr_open_dwork_wrt_expr :
forall w1 e1,
  degree_dwork_wrt_expr 1 w1 ->
  degree_expr_wrt_expr 0 e1 ->
  degree_dwork_wrt_expr 0 (open_dwork_wrt_expr w1 e1).
Proof.
unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve degree_dwork_wrt_expr_open_dwork_wrt_expr : lngen.

Lemma degree_dworklist_wrt_expr_open_dworklist_wrt_expr :
forall wl1 e1,
  degree_dworklist_wrt_expr 1 wl1 ->
  degree_expr_wrt_expr 0 e1 ->
  degree_dworklist_wrt_expr 0 (open_dworklist_wrt_expr wl1 e1).
Proof.
unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve degree_dworklist_wrt_expr_open_dworklist_wrt_expr : lngen.

(* begin hide *)

Lemma degree_expr_wrt_expr_open_expr_wrt_expr_rec_inv_degree_body_wrt_expr_open_body_wrt_expr_rec_inv_mutual :
(forall e1 e2 n1,
  degree_expr_wrt_expr n1 (open_expr_wrt_expr_rec n1 e2 e1) ->
  degree_expr_wrt_expr (S n1) e1) /\
(forall b1 e1 n1,
  degree_body_wrt_expr n1 (open_body_wrt_expr_rec n1 e1 b1) ->
  degree_body_wrt_expr (S n1) b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_expr_wrt_expr_open_expr_wrt_expr_rec_inv :
forall e1 e2 n1,
  degree_expr_wrt_expr n1 (open_expr_wrt_expr_rec n1 e2 e1) ->
  degree_expr_wrt_expr (S n1) e1.
Proof.
pose proof degree_expr_wrt_expr_open_expr_wrt_expr_rec_inv_degree_body_wrt_expr_open_body_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_expr_wrt_expr_open_expr_wrt_expr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_expr_open_body_wrt_expr_rec_inv :
forall b1 e1 n1,
  degree_body_wrt_expr n1 (open_body_wrt_expr_rec n1 e1 b1) ->
  degree_body_wrt_expr (S n1) b1.
Proof.
pose proof degree_expr_wrt_expr_open_expr_wrt_expr_rec_inv_degree_body_wrt_expr_open_body_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_body_wrt_expr_open_body_wrt_expr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_context_wrt_expr_open_context_wrt_expr_rec_inv_mutual :
(forall G1 e1 n1,
  degree_context_wrt_expr n1 (open_context_wrt_expr_rec n1 e1 G1) ->
  degree_context_wrt_expr (S n1) G1).
Proof.
apply_mutual_ind context_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_context_wrt_expr_open_context_wrt_expr_rec_inv :
forall G1 e1 n1,
  degree_context_wrt_expr n1 (open_context_wrt_expr_rec n1 e1 G1) ->
  degree_context_wrt_expr (S n1) G1.
Proof.
pose proof degree_context_wrt_expr_open_context_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_context_wrt_expr_open_context_wrt_expr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_obindd_wrt_expr_open_obindd_wrt_expr_rec_inv_mutual :
(forall ob1 e1 n1,
  degree_obindd_wrt_expr n1 (open_obindd_wrt_expr_rec n1 e1 ob1) ->
  degree_obindd_wrt_expr (S n1) ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_obindd_wrt_expr_open_obindd_wrt_expr_rec_inv :
forall ob1 e1 n1,
  degree_obindd_wrt_expr n1 (open_obindd_wrt_expr_rec n1 e1 ob1) ->
  degree_obindd_wrt_expr (S n1) ob1.
Proof.
pose proof degree_obindd_wrt_expr_open_obindd_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_obindd_wrt_expr_open_obindd_wrt_expr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dwork_wrt_expr_open_dwork_wrt_expr_rec_inv_degree_dworklist_wrt_expr_open_dworklist_wrt_expr_rec_inv_mutual :
(forall w1 e1 n1,
  degree_dwork_wrt_expr n1 (open_dwork_wrt_expr_rec n1 e1 w1) ->
  degree_dwork_wrt_expr (S n1) w1) /\
(forall wl1 e1 n1,
  degree_dworklist_wrt_expr n1 (open_dworklist_wrt_expr_rec n1 e1 wl1) ->
  degree_dworklist_wrt_expr (S n1) wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dwork_wrt_expr_open_dwork_wrt_expr_rec_inv :
forall w1 e1 n1,
  degree_dwork_wrt_expr n1 (open_dwork_wrt_expr_rec n1 e1 w1) ->
  degree_dwork_wrt_expr (S n1) w1.
Proof.
pose proof degree_dwork_wrt_expr_open_dwork_wrt_expr_rec_inv_degree_dworklist_wrt_expr_open_dworklist_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_dwork_wrt_expr_open_dwork_wrt_expr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dworklist_wrt_expr_open_dworklist_wrt_expr_rec_inv :
forall wl1 e1 n1,
  degree_dworklist_wrt_expr n1 (open_dworklist_wrt_expr_rec n1 e1 wl1) ->
  degree_dworklist_wrt_expr (S n1) wl1.
Proof.
pose proof degree_dwork_wrt_expr_open_dwork_wrt_expr_rec_inv_degree_dworklist_wrt_expr_open_dworklist_wrt_expr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_dworklist_wrt_expr_open_dworklist_wrt_expr_rec_inv : lngen.

(* end hide *)

Lemma degree_expr_wrt_expr_open_expr_wrt_expr_inv :
forall e1 e2,
  degree_expr_wrt_expr 0 (open_expr_wrt_expr e1 e2) ->
  degree_expr_wrt_expr 1 e1.
Proof.
unfold open_expr_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_expr_wrt_expr_open_expr_wrt_expr_inv : lngen.

Lemma degree_body_wrt_expr_open_body_wrt_expr_inv :
forall b1 e1,
  degree_body_wrt_expr 0 (open_body_wrt_expr b1 e1) ->
  degree_body_wrt_expr 1 b1.
Proof.
unfold open_body_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_body_wrt_expr_open_body_wrt_expr_inv : lngen.

Lemma degree_context_wrt_expr_open_context_wrt_expr_inv :
forall G1 e1,
  degree_context_wrt_expr 0 (open_context_wrt_expr G1 e1) ->
  degree_context_wrt_expr 1 G1.
Proof.
unfold open_context_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_context_wrt_expr_open_context_wrt_expr_inv : lngen.

Lemma degree_obindd_wrt_expr_open_obindd_wrt_expr_inv :
forall ob1 e1,
  degree_obindd_wrt_expr 0 (open_obindd_wrt_expr ob1 e1) ->
  degree_obindd_wrt_expr 1 ob1.
Proof.
unfold open_obindd_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_obindd_wrt_expr_open_obindd_wrt_expr_inv : lngen.

Lemma degree_dwork_wrt_expr_open_dwork_wrt_expr_inv :
forall w1 e1,
  degree_dwork_wrt_expr 0 (open_dwork_wrt_expr w1 e1) ->
  degree_dwork_wrt_expr 1 w1.
Proof.
unfold open_dwork_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_dwork_wrt_expr_open_dwork_wrt_expr_inv : lngen.

Lemma degree_dworklist_wrt_expr_open_dworklist_wrt_expr_inv :
forall wl1 e1,
  degree_dworklist_wrt_expr 0 (open_dworklist_wrt_expr wl1 e1) ->
  degree_dworklist_wrt_expr 1 wl1.
Proof.
unfold open_dworklist_wrt_expr; eauto with lngen.
Qed.

Hint Immediate degree_dworklist_wrt_expr_open_dworklist_wrt_expr_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_expr_wrt_expr_rec_inj_close_body_wrt_expr_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_expr_wrt_expr_rec n1 x1 e1 = close_expr_wrt_expr_rec n1 x1 e2 ->
  e1 = e2) /\
(forall b1 b2 x1 n1,
  close_body_wrt_expr_rec n1 x1 b1 = close_body_wrt_expr_rec n1 x1 b2 ->
  b1 = b2).
Proof.
apply_mutual_ind expr_body_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_expr_wrt_expr_rec_inj :
forall e1 e2 x1 n1,
  close_expr_wrt_expr_rec n1 x1 e1 = close_expr_wrt_expr_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_expr_wrt_expr_rec_inj_close_body_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_expr_wrt_expr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_expr_rec_inj :
forall b1 b2 x1 n1,
  close_body_wrt_expr_rec n1 x1 b1 = close_body_wrt_expr_rec n1 x1 b2 ->
  b1 = b2.
Proof.
pose proof close_expr_wrt_expr_rec_inj_close_body_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_body_wrt_expr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_context_wrt_expr_rec_inj_mutual :
(forall G1 G2 x1 n1,
  close_context_wrt_expr_rec n1 x1 G1 = close_context_wrt_expr_rec n1 x1 G2 ->
  G1 = G2).
Proof.
apply_mutual_ind context_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_context_wrt_expr_rec_inj :
forall G1 G2 x1 n1,
  close_context_wrt_expr_rec n1 x1 G1 = close_context_wrt_expr_rec n1 x1 G2 ->
  G1 = G2.
Proof.
pose proof close_context_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_context_wrt_expr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_obindd_wrt_expr_rec_inj_mutual :
(forall ob1 ob2 x1 n1,
  close_obindd_wrt_expr_rec n1 x1 ob1 = close_obindd_wrt_expr_rec n1 x1 ob2 ->
  ob1 = ob2).
Proof.
apply_mutual_ind obindd_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_obindd_wrt_expr_rec_inj :
forall ob1 ob2 x1 n1,
  close_obindd_wrt_expr_rec n1 x1 ob1 = close_obindd_wrt_expr_rec n1 x1 ob2 ->
  ob1 = ob2.
Proof.
pose proof close_obindd_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_obindd_wrt_expr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dwork_wrt_expr_rec_inj_close_dworklist_wrt_expr_rec_inj_mutual :
(forall w1 w2 x1 n1,
  close_dwork_wrt_expr_rec n1 x1 w1 = close_dwork_wrt_expr_rec n1 x1 w2 ->
  w1 = w2) /\
(forall wl1 wl2 x1 n1,
  close_dworklist_wrt_expr_rec n1 x1 wl1 = close_dworklist_wrt_expr_rec n1 x1 wl2 ->
  wl1 = wl2).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dwork_wrt_expr_rec_inj :
forall w1 w2 x1 n1,
  close_dwork_wrt_expr_rec n1 x1 w1 = close_dwork_wrt_expr_rec n1 x1 w2 ->
  w1 = w2.
Proof.
pose proof close_dwork_wrt_expr_rec_inj_close_dworklist_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_dwork_wrt_expr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dworklist_wrt_expr_rec_inj :
forall wl1 wl2 x1 n1,
  close_dworklist_wrt_expr_rec n1 x1 wl1 = close_dworklist_wrt_expr_rec n1 x1 wl2 ->
  wl1 = wl2.
Proof.
pose proof close_dwork_wrt_expr_rec_inj_close_dworklist_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_dworklist_wrt_expr_rec_inj : lngen.

(* end hide *)

Lemma close_expr_wrt_expr_inj :
forall e1 e2 x1,
  close_expr_wrt_expr x1 e1 = close_expr_wrt_expr x1 e2 ->
  e1 = e2.
Proof.
unfold close_expr_wrt_expr; eauto with lngen.
Qed.

Hint Immediate close_expr_wrt_expr_inj : lngen.

Lemma close_body_wrt_expr_inj :
forall b1 b2 x1,
  close_body_wrt_expr x1 b1 = close_body_wrt_expr x1 b2 ->
  b1 = b2.
Proof.
unfold close_body_wrt_expr; eauto with lngen.
Qed.

Hint Immediate close_body_wrt_expr_inj : lngen.

Lemma close_context_wrt_expr_inj :
forall G1 G2 x1,
  close_context_wrt_expr x1 G1 = close_context_wrt_expr x1 G2 ->
  G1 = G2.
Proof.
unfold close_context_wrt_expr; eauto with lngen.
Qed.

Hint Immediate close_context_wrt_expr_inj : lngen.

Lemma close_obindd_wrt_expr_inj :
forall ob1 ob2 x1,
  close_obindd_wrt_expr x1 ob1 = close_obindd_wrt_expr x1 ob2 ->
  ob1 = ob2.
Proof.
unfold close_obindd_wrt_expr; eauto with lngen.
Qed.

Hint Immediate close_obindd_wrt_expr_inj : lngen.

Lemma close_dwork_wrt_expr_inj :
forall w1 w2 x1,
  close_dwork_wrt_expr x1 w1 = close_dwork_wrt_expr x1 w2 ->
  w1 = w2.
Proof.
unfold close_dwork_wrt_expr; eauto with lngen.
Qed.

Hint Immediate close_dwork_wrt_expr_inj : lngen.

Lemma close_dworklist_wrt_expr_inj :
forall wl1 wl2 x1,
  close_dworklist_wrt_expr x1 wl1 = close_dworklist_wrt_expr x1 wl2 ->
  wl1 = wl2.
Proof.
unfold close_dworklist_wrt_expr; eauto with lngen.
Qed.

Hint Immediate close_dworklist_wrt_expr_inj : lngen.

(* begin hide *)

Lemma close_expr_wrt_expr_rec_open_expr_wrt_expr_rec_close_body_wrt_expr_rec_open_body_wrt_expr_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_expr e1 ->
  close_expr_wrt_expr_rec n1 x1 (open_expr_wrt_expr_rec n1 (e_var_f x1) e1) = e1) /\
(forall b1 x1 n1,
  x1 `notin` fv_body b1 ->
  close_body_wrt_expr_rec n1 x1 (open_body_wrt_expr_rec n1 (e_var_f x1) b1) = b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_expr_wrt_expr_rec_open_expr_wrt_expr_rec :
forall e1 x1 n1,
  x1 `notin` fv_expr e1 ->
  close_expr_wrt_expr_rec n1 x1 (open_expr_wrt_expr_rec n1 (e_var_f x1) e1) = e1.
Proof.
pose proof close_expr_wrt_expr_rec_open_expr_wrt_expr_rec_close_body_wrt_expr_rec_open_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_expr_wrt_expr_rec_open_expr_wrt_expr_rec : lngen.
Hint Rewrite close_expr_wrt_expr_rec_open_expr_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_expr_rec_open_body_wrt_expr_rec :
forall b1 x1 n1,
  x1 `notin` fv_body b1 ->
  close_body_wrt_expr_rec n1 x1 (open_body_wrt_expr_rec n1 (e_var_f x1) b1) = b1.
Proof.
pose proof close_expr_wrt_expr_rec_open_expr_wrt_expr_rec_close_body_wrt_expr_rec_open_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_body_wrt_expr_rec_open_body_wrt_expr_rec : lngen.
Hint Rewrite close_body_wrt_expr_rec_open_body_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_context_wrt_expr_rec_open_context_wrt_expr_rec_mutual :
(forall G1 x1 n1,
  x1 `notin` fv_context G1 ->
  close_context_wrt_expr_rec n1 x1 (open_context_wrt_expr_rec n1 (e_var_f x1) G1) = G1).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_context_wrt_expr_rec_open_context_wrt_expr_rec :
forall G1 x1 n1,
  x1 `notin` fv_context G1 ->
  close_context_wrt_expr_rec n1 x1 (open_context_wrt_expr_rec n1 (e_var_f x1) G1) = G1.
Proof.
pose proof close_context_wrt_expr_rec_open_context_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_context_wrt_expr_rec_open_context_wrt_expr_rec : lngen.
Hint Rewrite close_context_wrt_expr_rec_open_context_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_obindd_wrt_expr_rec_open_obindd_wrt_expr_rec_mutual :
(forall ob1 x1 n1,
  x1 `notin` fv_obindd ob1 ->
  close_obindd_wrt_expr_rec n1 x1 (open_obindd_wrt_expr_rec n1 (e_var_f x1) ob1) = ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_obindd_wrt_expr_rec_open_obindd_wrt_expr_rec :
forall ob1 x1 n1,
  x1 `notin` fv_obindd ob1 ->
  close_obindd_wrt_expr_rec n1 x1 (open_obindd_wrt_expr_rec n1 (e_var_f x1) ob1) = ob1.
Proof.
pose proof close_obindd_wrt_expr_rec_open_obindd_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_obindd_wrt_expr_rec_open_obindd_wrt_expr_rec : lngen.
Hint Rewrite close_obindd_wrt_expr_rec_open_obindd_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dwork_wrt_expr_rec_open_dwork_wrt_expr_rec_close_dworklist_wrt_expr_rec_open_dworklist_wrt_expr_rec_mutual :
(forall w1 x1 n1,
  x1 `notin` fv_dwork w1 ->
  close_dwork_wrt_expr_rec n1 x1 (open_dwork_wrt_expr_rec n1 (e_var_f x1) w1) = w1) /\
(forall wl1 x1 n1,
  x1 `notin` fv_dworklist wl1 ->
  close_dworklist_wrt_expr_rec n1 x1 (open_dworklist_wrt_expr_rec n1 (e_var_f x1) wl1) = wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dwork_wrt_expr_rec_open_dwork_wrt_expr_rec :
forall w1 x1 n1,
  x1 `notin` fv_dwork w1 ->
  close_dwork_wrt_expr_rec n1 x1 (open_dwork_wrt_expr_rec n1 (e_var_f x1) w1) = w1.
Proof.
pose proof close_dwork_wrt_expr_rec_open_dwork_wrt_expr_rec_close_dworklist_wrt_expr_rec_open_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_dwork_wrt_expr_rec_open_dwork_wrt_expr_rec : lngen.
Hint Rewrite close_dwork_wrt_expr_rec_open_dwork_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dworklist_wrt_expr_rec_open_dworklist_wrt_expr_rec :
forall wl1 x1 n1,
  x1 `notin` fv_dworklist wl1 ->
  close_dworklist_wrt_expr_rec n1 x1 (open_dworklist_wrt_expr_rec n1 (e_var_f x1) wl1) = wl1.
Proof.
pose proof close_dwork_wrt_expr_rec_open_dwork_wrt_expr_rec_close_dworklist_wrt_expr_rec_open_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_dworklist_wrt_expr_rec_open_dworklist_wrt_expr_rec : lngen.
Hint Rewrite close_dworklist_wrt_expr_rec_open_dworklist_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_expr_wrt_expr_open_expr_wrt_expr :
forall e1 x1,
  x1 `notin` fv_expr e1 ->
  close_expr_wrt_expr x1 (open_expr_wrt_expr e1 (e_var_f x1)) = e1.
Proof.
unfold close_expr_wrt_expr; unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve close_expr_wrt_expr_open_expr_wrt_expr : lngen.
Hint Rewrite close_expr_wrt_expr_open_expr_wrt_expr using solve [auto] : lngen.

Lemma close_body_wrt_expr_open_body_wrt_expr :
forall b1 x1,
  x1 `notin` fv_body b1 ->
  close_body_wrt_expr x1 (open_body_wrt_expr b1 (e_var_f x1)) = b1.
Proof.
unfold close_body_wrt_expr; unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve close_body_wrt_expr_open_body_wrt_expr : lngen.
Hint Rewrite close_body_wrt_expr_open_body_wrt_expr using solve [auto] : lngen.

Lemma close_context_wrt_expr_open_context_wrt_expr :
forall G1 x1,
  x1 `notin` fv_context G1 ->
  close_context_wrt_expr x1 (open_context_wrt_expr G1 (e_var_f x1)) = G1.
Proof.
unfold close_context_wrt_expr; unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve close_context_wrt_expr_open_context_wrt_expr : lngen.
Hint Rewrite close_context_wrt_expr_open_context_wrt_expr using solve [auto] : lngen.

Lemma close_obindd_wrt_expr_open_obindd_wrt_expr :
forall ob1 x1,
  x1 `notin` fv_obindd ob1 ->
  close_obindd_wrt_expr x1 (open_obindd_wrt_expr ob1 (e_var_f x1)) = ob1.
Proof.
unfold close_obindd_wrt_expr; unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve close_obindd_wrt_expr_open_obindd_wrt_expr : lngen.
Hint Rewrite close_obindd_wrt_expr_open_obindd_wrt_expr using solve [auto] : lngen.

Lemma close_dwork_wrt_expr_open_dwork_wrt_expr :
forall w1 x1,
  x1 `notin` fv_dwork w1 ->
  close_dwork_wrt_expr x1 (open_dwork_wrt_expr w1 (e_var_f x1)) = w1.
Proof.
unfold close_dwork_wrt_expr; unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve close_dwork_wrt_expr_open_dwork_wrt_expr : lngen.
Hint Rewrite close_dwork_wrt_expr_open_dwork_wrt_expr using solve [auto] : lngen.

Lemma close_dworklist_wrt_expr_open_dworklist_wrt_expr :
forall wl1 x1,
  x1 `notin` fv_dworklist wl1 ->
  close_dworklist_wrt_expr x1 (open_dworklist_wrt_expr wl1 (e_var_f x1)) = wl1.
Proof.
unfold close_dworklist_wrt_expr; unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve close_dworklist_wrt_expr_open_dworklist_wrt_expr : lngen.
Hint Rewrite close_dworklist_wrt_expr_open_dworklist_wrt_expr using solve [auto] : lngen.

(* begin hide *)

Lemma open_expr_wrt_expr_rec_close_expr_wrt_expr_rec_open_body_wrt_expr_rec_close_body_wrt_expr_rec_mutual :
(forall e1 x1 n1,
  open_expr_wrt_expr_rec n1 (e_var_f x1) (close_expr_wrt_expr_rec n1 x1 e1) = e1) /\
(forall b1 x1 n1,
  open_body_wrt_expr_rec n1 (e_var_f x1) (close_body_wrt_expr_rec n1 x1 b1) = b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_expr_wrt_expr_rec_close_expr_wrt_expr_rec :
forall e1 x1 n1,
  open_expr_wrt_expr_rec n1 (e_var_f x1) (close_expr_wrt_expr_rec n1 x1 e1) = e1.
Proof.
pose proof open_expr_wrt_expr_rec_close_expr_wrt_expr_rec_open_body_wrt_expr_rec_close_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_expr_wrt_expr_rec_close_expr_wrt_expr_rec : lngen.
Hint Rewrite open_expr_wrt_expr_rec_close_expr_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_expr_rec_close_body_wrt_expr_rec :
forall b1 x1 n1,
  open_body_wrt_expr_rec n1 (e_var_f x1) (close_body_wrt_expr_rec n1 x1 b1) = b1.
Proof.
pose proof open_expr_wrt_expr_rec_close_expr_wrt_expr_rec_open_body_wrt_expr_rec_close_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_body_wrt_expr_rec_close_body_wrt_expr_rec : lngen.
Hint Rewrite open_body_wrt_expr_rec_close_body_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_context_wrt_expr_rec_close_context_wrt_expr_rec_mutual :
(forall G1 x1 n1,
  open_context_wrt_expr_rec n1 (e_var_f x1) (close_context_wrt_expr_rec n1 x1 G1) = G1).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_context_wrt_expr_rec_close_context_wrt_expr_rec :
forall G1 x1 n1,
  open_context_wrt_expr_rec n1 (e_var_f x1) (close_context_wrt_expr_rec n1 x1 G1) = G1.
Proof.
pose proof open_context_wrt_expr_rec_close_context_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_context_wrt_expr_rec_close_context_wrt_expr_rec : lngen.
Hint Rewrite open_context_wrt_expr_rec_close_context_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_obindd_wrt_expr_rec_close_obindd_wrt_expr_rec_mutual :
(forall ob1 x1 n1,
  open_obindd_wrt_expr_rec n1 (e_var_f x1) (close_obindd_wrt_expr_rec n1 x1 ob1) = ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_obindd_wrt_expr_rec_close_obindd_wrt_expr_rec :
forall ob1 x1 n1,
  open_obindd_wrt_expr_rec n1 (e_var_f x1) (close_obindd_wrt_expr_rec n1 x1 ob1) = ob1.
Proof.
pose proof open_obindd_wrt_expr_rec_close_obindd_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_obindd_wrt_expr_rec_close_obindd_wrt_expr_rec : lngen.
Hint Rewrite open_obindd_wrt_expr_rec_close_obindd_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dwork_wrt_expr_rec_close_dwork_wrt_expr_rec_open_dworklist_wrt_expr_rec_close_dworklist_wrt_expr_rec_mutual :
(forall w1 x1 n1,
  open_dwork_wrt_expr_rec n1 (e_var_f x1) (close_dwork_wrt_expr_rec n1 x1 w1) = w1) /\
(forall wl1 x1 n1,
  open_dworklist_wrt_expr_rec n1 (e_var_f x1) (close_dworklist_wrt_expr_rec n1 x1 wl1) = wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dwork_wrt_expr_rec_close_dwork_wrt_expr_rec :
forall w1 x1 n1,
  open_dwork_wrt_expr_rec n1 (e_var_f x1) (close_dwork_wrt_expr_rec n1 x1 w1) = w1.
Proof.
pose proof open_dwork_wrt_expr_rec_close_dwork_wrt_expr_rec_open_dworklist_wrt_expr_rec_close_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_dwork_wrt_expr_rec_close_dwork_wrt_expr_rec : lngen.
Hint Rewrite open_dwork_wrt_expr_rec_close_dwork_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dworklist_wrt_expr_rec_close_dworklist_wrt_expr_rec :
forall wl1 x1 n1,
  open_dworklist_wrt_expr_rec n1 (e_var_f x1) (close_dworklist_wrt_expr_rec n1 x1 wl1) = wl1.
Proof.
pose proof open_dwork_wrt_expr_rec_close_dwork_wrt_expr_rec_open_dworklist_wrt_expr_rec_close_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_dworklist_wrt_expr_rec_close_dworklist_wrt_expr_rec : lngen.
Hint Rewrite open_dworklist_wrt_expr_rec_close_dworklist_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_expr_wrt_expr_close_expr_wrt_expr :
forall e1 x1,
  open_expr_wrt_expr (close_expr_wrt_expr x1 e1) (e_var_f x1) = e1.
Proof.
unfold close_expr_wrt_expr; unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve open_expr_wrt_expr_close_expr_wrt_expr : lngen.
Hint Rewrite open_expr_wrt_expr_close_expr_wrt_expr using solve [auto] : lngen.

Lemma open_body_wrt_expr_close_body_wrt_expr :
forall b1 x1,
  open_body_wrt_expr (close_body_wrt_expr x1 b1) (e_var_f x1) = b1.
Proof.
unfold close_body_wrt_expr; unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve open_body_wrt_expr_close_body_wrt_expr : lngen.
Hint Rewrite open_body_wrt_expr_close_body_wrt_expr using solve [auto] : lngen.

Lemma open_context_wrt_expr_close_context_wrt_expr :
forall G1 x1,
  open_context_wrt_expr (close_context_wrt_expr x1 G1) (e_var_f x1) = G1.
Proof.
unfold close_context_wrt_expr; unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve open_context_wrt_expr_close_context_wrt_expr : lngen.
Hint Rewrite open_context_wrt_expr_close_context_wrt_expr using solve [auto] : lngen.

Lemma open_obindd_wrt_expr_close_obindd_wrt_expr :
forall ob1 x1,
  open_obindd_wrt_expr (close_obindd_wrt_expr x1 ob1) (e_var_f x1) = ob1.
Proof.
unfold close_obindd_wrt_expr; unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve open_obindd_wrt_expr_close_obindd_wrt_expr : lngen.
Hint Rewrite open_obindd_wrt_expr_close_obindd_wrt_expr using solve [auto] : lngen.

Lemma open_dwork_wrt_expr_close_dwork_wrt_expr :
forall w1 x1,
  open_dwork_wrt_expr (close_dwork_wrt_expr x1 w1) (e_var_f x1) = w1.
Proof.
unfold close_dwork_wrt_expr; unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve open_dwork_wrt_expr_close_dwork_wrt_expr : lngen.
Hint Rewrite open_dwork_wrt_expr_close_dwork_wrt_expr using solve [auto] : lngen.

Lemma open_dworklist_wrt_expr_close_dworklist_wrt_expr :
forall wl1 x1,
  open_dworklist_wrt_expr (close_dworklist_wrt_expr x1 wl1) (e_var_f x1) = wl1.
Proof.
unfold close_dworklist_wrt_expr; unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve open_dworklist_wrt_expr_close_dworklist_wrt_expr : lngen.
Hint Rewrite open_dworklist_wrt_expr_close_dworklist_wrt_expr using solve [auto] : lngen.

(* begin hide *)

Lemma open_expr_wrt_expr_rec_inj_open_body_wrt_expr_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_expr e2 ->
  x1 `notin` fv_expr e1 ->
  open_expr_wrt_expr_rec n1 (e_var_f x1) e2 = open_expr_wrt_expr_rec n1 (e_var_f x1) e1 ->
  e2 = e1) /\
(forall b2 b1 x1 n1,
  x1 `notin` fv_body b2 ->
  x1 `notin` fv_body b1 ->
  open_body_wrt_expr_rec n1 (e_var_f x1) b2 = open_body_wrt_expr_rec n1 (e_var_f x1) b1 ->
  b2 = b1).
Proof.
apply_mutual_ind expr_body_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_expr_wrt_expr_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_expr e2 ->
  x1 `notin` fv_expr e1 ->
  open_expr_wrt_expr_rec n1 (e_var_f x1) e2 = open_expr_wrt_expr_rec n1 (e_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_expr_wrt_expr_rec_inj_open_body_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_expr_wrt_expr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_expr_rec_inj :
forall b2 b1 x1 n1,
  x1 `notin` fv_body b2 ->
  x1 `notin` fv_body b1 ->
  open_body_wrt_expr_rec n1 (e_var_f x1) b2 = open_body_wrt_expr_rec n1 (e_var_f x1) b1 ->
  b2 = b1.
Proof.
pose proof open_expr_wrt_expr_rec_inj_open_body_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_body_wrt_expr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_context_wrt_expr_rec_inj_mutual :
(forall G2 G1 x1 n1,
  x1 `notin` fv_context G2 ->
  x1 `notin` fv_context G1 ->
  open_context_wrt_expr_rec n1 (e_var_f x1) G2 = open_context_wrt_expr_rec n1 (e_var_f x1) G1 ->
  G2 = G1).
Proof.
apply_mutual_ind context_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_context_wrt_expr_rec_inj :
forall G2 G1 x1 n1,
  x1 `notin` fv_context G2 ->
  x1 `notin` fv_context G1 ->
  open_context_wrt_expr_rec n1 (e_var_f x1) G2 = open_context_wrt_expr_rec n1 (e_var_f x1) G1 ->
  G2 = G1.
Proof.
pose proof open_context_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_context_wrt_expr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_obindd_wrt_expr_rec_inj_mutual :
(forall ob2 ob1 x1 n1,
  x1 `notin` fv_obindd ob2 ->
  x1 `notin` fv_obindd ob1 ->
  open_obindd_wrt_expr_rec n1 (e_var_f x1) ob2 = open_obindd_wrt_expr_rec n1 (e_var_f x1) ob1 ->
  ob2 = ob1).
Proof.
apply_mutual_ind obindd_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_obindd_wrt_expr_rec_inj :
forall ob2 ob1 x1 n1,
  x1 `notin` fv_obindd ob2 ->
  x1 `notin` fv_obindd ob1 ->
  open_obindd_wrt_expr_rec n1 (e_var_f x1) ob2 = open_obindd_wrt_expr_rec n1 (e_var_f x1) ob1 ->
  ob2 = ob1.
Proof.
pose proof open_obindd_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_obindd_wrt_expr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dwork_wrt_expr_rec_inj_open_dworklist_wrt_expr_rec_inj_mutual :
(forall w2 w1 x1 n1,
  x1 `notin` fv_dwork w2 ->
  x1 `notin` fv_dwork w1 ->
  open_dwork_wrt_expr_rec n1 (e_var_f x1) w2 = open_dwork_wrt_expr_rec n1 (e_var_f x1) w1 ->
  w2 = w1) /\
(forall wl2 wl1 x1 n1,
  x1 `notin` fv_dworklist wl2 ->
  x1 `notin` fv_dworklist wl1 ->
  open_dworklist_wrt_expr_rec n1 (e_var_f x1) wl2 = open_dworklist_wrt_expr_rec n1 (e_var_f x1) wl1 ->
  wl2 = wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dwork_wrt_expr_rec_inj :
forall w2 w1 x1 n1,
  x1 `notin` fv_dwork w2 ->
  x1 `notin` fv_dwork w1 ->
  open_dwork_wrt_expr_rec n1 (e_var_f x1) w2 = open_dwork_wrt_expr_rec n1 (e_var_f x1) w1 ->
  w2 = w1.
Proof.
pose proof open_dwork_wrt_expr_rec_inj_open_dworklist_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_dwork_wrt_expr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dworklist_wrt_expr_rec_inj :
forall wl2 wl1 x1 n1,
  x1 `notin` fv_dworklist wl2 ->
  x1 `notin` fv_dworklist wl1 ->
  open_dworklist_wrt_expr_rec n1 (e_var_f x1) wl2 = open_dworklist_wrt_expr_rec n1 (e_var_f x1) wl1 ->
  wl2 = wl1.
Proof.
pose proof open_dwork_wrt_expr_rec_inj_open_dworklist_wrt_expr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_dworklist_wrt_expr_rec_inj : lngen.

(* end hide *)

Lemma open_expr_wrt_expr_inj :
forall e2 e1 x1,
  x1 `notin` fv_expr e2 ->
  x1 `notin` fv_expr e1 ->
  open_expr_wrt_expr e2 (e_var_f x1) = open_expr_wrt_expr e1 (e_var_f x1) ->
  e2 = e1.
Proof.
unfold open_expr_wrt_expr; eauto with lngen.
Qed.

Hint Immediate open_expr_wrt_expr_inj : lngen.

Lemma open_body_wrt_expr_inj :
forall b2 b1 x1,
  x1 `notin` fv_body b2 ->
  x1 `notin` fv_body b1 ->
  open_body_wrt_expr b2 (e_var_f x1) = open_body_wrt_expr b1 (e_var_f x1) ->
  b2 = b1.
Proof.
unfold open_body_wrt_expr; eauto with lngen.
Qed.

Hint Immediate open_body_wrt_expr_inj : lngen.

Lemma open_context_wrt_expr_inj :
forall G2 G1 x1,
  x1 `notin` fv_context G2 ->
  x1 `notin` fv_context G1 ->
  open_context_wrt_expr G2 (e_var_f x1) = open_context_wrt_expr G1 (e_var_f x1) ->
  G2 = G1.
Proof.
unfold open_context_wrt_expr; eauto with lngen.
Qed.

Hint Immediate open_context_wrt_expr_inj : lngen.

Lemma open_obindd_wrt_expr_inj :
forall ob2 ob1 x1,
  x1 `notin` fv_obindd ob2 ->
  x1 `notin` fv_obindd ob1 ->
  open_obindd_wrt_expr ob2 (e_var_f x1) = open_obindd_wrt_expr ob1 (e_var_f x1) ->
  ob2 = ob1.
Proof.
unfold open_obindd_wrt_expr; eauto with lngen.
Qed.

Hint Immediate open_obindd_wrt_expr_inj : lngen.

Lemma open_dwork_wrt_expr_inj :
forall w2 w1 x1,
  x1 `notin` fv_dwork w2 ->
  x1 `notin` fv_dwork w1 ->
  open_dwork_wrt_expr w2 (e_var_f x1) = open_dwork_wrt_expr w1 (e_var_f x1) ->
  w2 = w1.
Proof.
unfold open_dwork_wrt_expr; eauto with lngen.
Qed.

Hint Immediate open_dwork_wrt_expr_inj : lngen.

Lemma open_dworklist_wrt_expr_inj :
forall wl2 wl1 x1,
  x1 `notin` fv_dworklist wl2 ->
  x1 `notin` fv_dworklist wl1 ->
  open_dworklist_wrt_expr wl2 (e_var_f x1) = open_dworklist_wrt_expr wl1 (e_var_f x1) ->
  wl2 = wl1.
Proof.
unfold open_dworklist_wrt_expr; eauto with lngen.
Qed.

Hint Immediate open_dworklist_wrt_expr_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_expr_wrt_expr_of_lc_expr_degree_body_wrt_expr_of_lc_body_mutual :
(forall e1,
  lc_expr e1 ->
  degree_expr_wrt_expr 0 e1) /\
(forall b1,
  lc_body b1 ->
  degree_body_wrt_expr 0 b1).
Proof.
apply_mutual_ind lc_expr_lc_body_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_expr_wrt_expr_of_lc_expr :
forall e1,
  lc_expr e1 ->
  degree_expr_wrt_expr 0 e1.
Proof.
pose proof degree_expr_wrt_expr_of_lc_expr_degree_body_wrt_expr_of_lc_body_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_expr_wrt_expr_of_lc_expr : lngen.

Lemma degree_body_wrt_expr_of_lc_body :
forall b1,
  lc_body b1 ->
  degree_body_wrt_expr 0 b1.
Proof.
pose proof degree_expr_wrt_expr_of_lc_expr_degree_body_wrt_expr_of_lc_body_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_body_wrt_expr_of_lc_body : lngen.

(* begin hide *)

Lemma degree_context_wrt_expr_of_lc_context_mutual :
(forall G1,
  lc_context G1 ->
  degree_context_wrt_expr 0 G1).
Proof.
apply_mutual_ind lc_context_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_context_wrt_expr_of_lc_context :
forall G1,
  lc_context G1 ->
  degree_context_wrt_expr 0 G1.
Proof.
pose proof degree_context_wrt_expr_of_lc_context_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_context_wrt_expr_of_lc_context : lngen.

(* begin hide *)

Lemma degree_obindd_wrt_expr_of_lc_obindd_mutual :
(forall ob1,
  lc_obindd ob1 ->
  degree_obindd_wrt_expr 0 ob1).
Proof.
apply_mutual_ind lc_obindd_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_obindd_wrt_expr_of_lc_obindd :
forall ob1,
  lc_obindd ob1 ->
  degree_obindd_wrt_expr 0 ob1.
Proof.
pose proof degree_obindd_wrt_expr_of_lc_obindd_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_obindd_wrt_expr_of_lc_obindd : lngen.

(* begin hide *)

Lemma degree_dwork_wrt_expr_of_lc_dwork_degree_dworklist_wrt_expr_of_lc_dworklist_mutual :
(forall w1,
  lc_dwork w1 ->
  degree_dwork_wrt_expr 0 w1) /\
(forall wl1,
  lc_dworklist wl1 ->
  degree_dworklist_wrt_expr 0 wl1).
Proof.
apply_mutual_ind lc_dwork_lc_dworklist_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_dwork_wrt_expr_of_lc_dwork :
forall w1,
  lc_dwork w1 ->
  degree_dwork_wrt_expr 0 w1.
Proof.
pose proof degree_dwork_wrt_expr_of_lc_dwork_degree_dworklist_wrt_expr_of_lc_dworklist_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dwork_wrt_expr_of_lc_dwork : lngen.

Lemma degree_dworklist_wrt_expr_of_lc_dworklist :
forall wl1,
  lc_dworklist wl1 ->
  degree_dworklist_wrt_expr 0 wl1.
Proof.
pose proof degree_dwork_wrt_expr_of_lc_dwork_degree_dworklist_wrt_expr_of_lc_dworklist_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dworklist_wrt_expr_of_lc_dworklist : lngen.

(* begin hide *)

Lemma lc_expr_of_degree_lc_body_of_degree_size_mutual :
forall i1,
(forall e1,
  size_expr e1 = i1 ->
  degree_expr_wrt_expr 0 e1 ->
  lc_expr e1) /\
(forall b1,
  size_body b1 = i1 ->
  degree_body_wrt_expr 0 b1 ->
  lc_body b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind expr_body_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_expr_of_degree :
forall e1,
  degree_expr_wrt_expr 0 e1 ->
  lc_expr e1.
Proof.
intros e1; intros;
pose proof (lc_expr_of_degree_lc_body_of_degree_size_mutual (size_expr e1));
intuition eauto.
Qed.

Hint Resolve lc_expr_of_degree : lngen.

Lemma lc_body_of_degree :
forall b1,
  degree_body_wrt_expr 0 b1 ->
  lc_body b1.
Proof.
intros b1; intros;
pose proof (lc_expr_of_degree_lc_body_of_degree_size_mutual (size_body b1));
intuition eauto.
Qed.

Hint Resolve lc_body_of_degree : lngen.

(* begin hide *)

Lemma lc_context_of_degree_size_mutual :
forall i1,
(forall G1,
  size_context G1 = i1 ->
  degree_context_wrt_expr 0 G1 ->
  lc_context G1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind context_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_context_of_degree :
forall G1,
  degree_context_wrt_expr 0 G1 ->
  lc_context G1.
Proof.
intros G1; intros;
pose proof (lc_context_of_degree_size_mutual (size_context G1));
intuition eauto.
Qed.

Hint Resolve lc_context_of_degree : lngen.

(* begin hide *)

Lemma lc_obindd_of_degree_size_mutual :
forall i1,
(forall ob1,
  size_obindd ob1 = i1 ->
  degree_obindd_wrt_expr 0 ob1 ->
  lc_obindd ob1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind obindd_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_obindd_of_degree :
forall ob1,
  degree_obindd_wrt_expr 0 ob1 ->
  lc_obindd ob1.
Proof.
intros ob1; intros;
pose proof (lc_obindd_of_degree_size_mutual (size_obindd ob1));
intuition eauto.
Qed.

Hint Resolve lc_obindd_of_degree : lngen.

(* begin hide *)

Lemma lc_dwork_of_degree_lc_dworklist_of_degree_size_mutual :
forall i1,
(forall w1,
  size_dwork w1 = i1 ->
  degree_dwork_wrt_expr 0 w1 ->
  lc_dwork w1) /\
(forall wl1,
  size_dworklist wl1 = i1 ->
  degree_dworklist_wrt_expr 0 wl1 ->
  lc_dworklist wl1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dwork_dworklist_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_dwork_of_degree :
forall w1,
  degree_dwork_wrt_expr 0 w1 ->
  lc_dwork w1.
Proof.
intros w1; intros;
pose proof (lc_dwork_of_degree_lc_dworklist_of_degree_size_mutual (size_dwork w1));
intuition eauto.
Qed.

Hint Resolve lc_dwork_of_degree : lngen.

Lemma lc_dworklist_of_degree :
forall wl1,
  degree_dworklist_wrt_expr 0 wl1 ->
  lc_dworklist wl1.
Proof.
intros wl1; intros;
pose proof (lc_dwork_of_degree_lc_dworklist_of_degree_size_mutual (size_dworklist wl1));
intuition eauto.
Qed.

Hint Resolve lc_dworklist_of_degree : lngen.

Ltac kind_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac expr_body_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_expr_wrt_expr_of_lc_expr in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_body_wrt_expr_of_lc_body in J1; clear H
          end).

Ltac context_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_context_wrt_expr_of_lc_context in J1; clear H
          end).

Ltac dir_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac obindd_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_obindd_wrt_expr_of_lc_obindd in J1; clear H
          end).

Ltac dwork_dworklist_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_dwork_wrt_expr_of_lc_dwork in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_dworklist_wrt_expr_of_lc_dworklist in J1; clear H
          end).

Lemma lc_e_abs_exists :
forall x1 A1 b1,
  lc_expr A1 ->
  lc_body (open_body_wrt_expr b1 (e_var_f x1)) ->
  lc_expr (e_abs A1 b1).
Proof.
intros; expr_body_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_e_pi_exists :
forall x1 A1 B1,
  lc_expr A1 ->
  lc_expr (open_expr_wrt_expr B1 (e_var_f x1)) ->
  lc_expr (e_pi A1 B1).
Proof.
intros; expr_body_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_e_bind_exists :
forall x1 A1 b1,
  lc_expr A1 ->
  lc_body (open_body_wrt_expr b1 (e_var_f x1)) ->
  lc_expr (e_bind A1 b1).
Proof.
intros; expr_body_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_e_all_exists :
forall x1 A1 B1,
  lc_expr A1 ->
  lc_expr (open_expr_wrt_expr B1 (e_var_f x1)) ->
  lc_expr (e_all A1 B1).
Proof.
intros; expr_body_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_dw_infer_exists :
forall x1 e1 e2 wl1,
  lc_expr e1 ->
  lc_expr e2 ->
  lc_dworklist (open_dworklist_wrt_expr wl1 (e_var_f x1)) ->
  lc_dwork (dw_infer e1 e2 wl1).
Proof.
intros; dwork_dworklist_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_dw_infer_app_exists :
forall x1 A1 e1 e2 wl1,
  lc_expr A1 ->
  lc_expr e1 ->
  lc_expr e2 ->
  lc_dworklist (open_dworklist_wrt_expr wl1 (e_var_f x1)) ->
  lc_dwork (dw_infer_app A1 e1 e2 wl1).
Proof.
intros; dwork_dworklist_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_dw_reduce_exists :
forall x1 e1 wl1,
  lc_expr e1 ->
  lc_dworklist (open_dworklist_wrt_expr wl1 (e_var_f x1)) ->
  lc_dwork (dw_reduce e1 wl1).
Proof.
intros; dwork_dworklist_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_expr (e_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_abs_exists x1) : core.

Hint Extern 1 (lc_expr (e_pi _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_pi_exists x1) : core.

Hint Extern 1 (lc_expr (e_bind _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_bind_exists x1) : core.

Hint Extern 1 (lc_expr (e_all _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_all_exists x1) : core.

Hint Extern 1 (lc_dwork (dw_infer _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_dw_infer_exists x1) : core.

Hint Extern 1 (lc_dwork (dw_infer_app _ _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_dw_infer_app_exists x1) : core.

Hint Extern 1 (lc_dwork (dw_reduce _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_dw_reduce_exists x1) : core.

Lemma lc_body_expr_wrt_expr :
forall e1 e2,
  body_expr_wrt_expr e1 ->
  lc_expr e2 ->
  lc_expr (open_expr_wrt_expr e1 e2).
Proof.
unfold body_expr_wrt_expr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
expr_body_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_expr_wrt_expr : lngen.

Lemma lc_body_body_wrt_expr :
forall b1 e1,
  body_body_wrt_expr b1 ->
  lc_expr e1 ->
  lc_body (open_body_wrt_expr b1 e1).
Proof.
unfold body_body_wrt_expr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
expr_body_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_body_wrt_expr : lngen.

Lemma lc_body_context_wrt_expr :
forall G1 e1,
  body_context_wrt_expr G1 ->
  lc_expr e1 ->
  lc_context (open_context_wrt_expr G1 e1).
Proof.
unfold body_context_wrt_expr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
context_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_context_wrt_expr : lngen.

Lemma lc_body_obindd_wrt_expr :
forall ob1 e1,
  body_obindd_wrt_expr ob1 ->
  lc_expr e1 ->
  lc_obindd (open_obindd_wrt_expr ob1 e1).
Proof.
unfold body_obindd_wrt_expr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
obindd_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_obindd_wrt_expr : lngen.

Lemma lc_body_dwork_wrt_expr :
forall w1 e1,
  body_dwork_wrt_expr w1 ->
  lc_expr e1 ->
  lc_dwork (open_dwork_wrt_expr w1 e1).
Proof.
unfold body_dwork_wrt_expr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
dwork_dworklist_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_dwork_wrt_expr : lngen.

Lemma lc_body_dworklist_wrt_expr :
forall wl1 e1,
  body_dworklist_wrt_expr wl1 ->
  lc_expr e1 ->
  lc_dworklist (open_dworklist_wrt_expr wl1 e1).
Proof.
unfold body_dworklist_wrt_expr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
dwork_dworklist_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_dworklist_wrt_expr : lngen.

Lemma lc_body_e_abs_2 :
forall A1 b1,
  lc_expr (e_abs A1 b1) ->
  body_body_wrt_expr b1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_abs_2 : lngen.

Lemma lc_body_e_pi_2 :
forall A1 B1,
  lc_expr (e_pi A1 B1) ->
  body_expr_wrt_expr B1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_pi_2 : lngen.

Lemma lc_body_e_bind_2 :
forall A1 b1,
  lc_expr (e_bind A1 b1) ->
  body_body_wrt_expr b1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_bind_2 : lngen.

Lemma lc_body_e_all_2 :
forall A1 B1,
  lc_expr (e_all A1 B1) ->
  body_expr_wrt_expr B1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_all_2 : lngen.

Lemma lc_body_dw_infer_3 :
forall e1 e2 wl1,
  lc_dwork (dw_infer e1 e2 wl1) ->
  body_dworklist_wrt_expr wl1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_dw_infer_3 : lngen.

Lemma lc_body_dw_infer_app_4 :
forall A1 e1 e2 wl1,
  lc_dwork (dw_infer_app A1 e1 e2 wl1) ->
  body_dworklist_wrt_expr wl1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_dw_infer_app_4 : lngen.

Lemma lc_body_dw_reduce_2 :
forall e1 wl1,
  lc_dwork (dw_reduce e1 wl1) ->
  body_dworklist_wrt_expr wl1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_dw_reduce_2 : lngen.

(* begin hide *)

Lemma lc_expr_unique_lc_body_unique_mutual :
(forall e1 (proof2 proof3 : lc_expr e1), proof2 = proof3) /\
(forall b1 (proof2 proof3 : lc_body b1), proof2 = proof3).
Proof.
apply_mutual_ind lc_expr_lc_body_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_expr_unique :
forall e1 (proof2 proof3 : lc_expr e1), proof2 = proof3.
Proof.
pose proof lc_expr_unique_lc_body_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_expr_unique : lngen.

Lemma lc_body_unique :
forall b1 (proof2 proof3 : lc_body b1), proof2 = proof3.
Proof.
pose proof lc_expr_unique_lc_body_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_body_unique : lngen.

(* begin hide *)

Lemma lc_context_unique_mutual :
(forall G1 (proof2 proof3 : lc_context G1), proof2 = proof3).
Proof.
apply_mutual_ind lc_context_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_context_unique :
forall G1 (proof2 proof3 : lc_context G1), proof2 = proof3.
Proof.
pose proof lc_context_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_context_unique : lngen.

(* begin hide *)

Lemma lc_obindd_unique_mutual :
(forall ob1 (proof2 proof3 : lc_obindd ob1), proof2 = proof3).
Proof.
apply_mutual_ind lc_obindd_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_obindd_unique :
forall ob1 (proof2 proof3 : lc_obindd ob1), proof2 = proof3.
Proof.
pose proof lc_obindd_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_obindd_unique : lngen.

(* begin hide *)

Lemma lc_dwork_unique_lc_dworklist_unique_mutual :
(forall w1 (proof2 proof3 : lc_dwork w1), proof2 = proof3) /\
(forall wl1 (proof2 proof3 : lc_dworklist wl1), proof2 = proof3).
Proof.
apply_mutual_ind lc_dwork_lc_dworklist_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_dwork_unique :
forall w1 (proof2 proof3 : lc_dwork w1), proof2 = proof3.
Proof.
pose proof lc_dwork_unique_lc_dworklist_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_dwork_unique : lngen.

Lemma lc_dworklist_unique :
forall wl1 (proof2 proof3 : lc_dworklist wl1), proof2 = proof3.
Proof.
pose proof lc_dwork_unique_lc_dworklist_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_dworklist_unique : lngen.

(* begin hide *)

Lemma lc_expr_of_lc_set_expr_lc_body_of_lc_set_body_mutual :
(forall e1, lc_set_expr e1 -> lc_expr e1) /\
(forall b1, lc_set_body b1 -> lc_body b1).
Proof.
apply_mutual_ind lc_set_expr_lc_set_body_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_expr_of_lc_set_expr :
forall e1, lc_set_expr e1 -> lc_expr e1.
Proof.
pose proof lc_expr_of_lc_set_expr_lc_body_of_lc_set_body_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_expr_of_lc_set_expr : lngen.

Lemma lc_body_of_lc_set_body :
forall b1, lc_set_body b1 -> lc_body b1.
Proof.
pose proof lc_expr_of_lc_set_expr_lc_body_of_lc_set_body_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_body_of_lc_set_body : lngen.

(* begin hide *)

Lemma lc_context_of_lc_set_context_mutual :
(forall G1, lc_set_context G1 -> lc_context G1).
Proof.
apply_mutual_ind lc_set_context_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_context_of_lc_set_context :
forall G1, lc_set_context G1 -> lc_context G1.
Proof.
pose proof lc_context_of_lc_set_context_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_context_of_lc_set_context : lngen.

(* begin hide *)

Lemma lc_obindd_of_lc_set_obindd_mutual :
(forall ob1, lc_set_obindd ob1 -> lc_obindd ob1).
Proof.
apply_mutual_ind lc_set_obindd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_obindd_of_lc_set_obindd :
forall ob1, lc_set_obindd ob1 -> lc_obindd ob1.
Proof.
pose proof lc_obindd_of_lc_set_obindd_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_obindd_of_lc_set_obindd : lngen.

(* begin hide *)

Lemma lc_dwork_of_lc_set_dwork_lc_dworklist_of_lc_set_dworklist_mutual :
(forall w1, lc_set_dwork w1 -> lc_dwork w1) /\
(forall wl1, lc_set_dworklist wl1 -> lc_dworklist wl1).
Proof.
apply_mutual_ind lc_set_dwork_lc_set_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_dwork_of_lc_set_dwork :
forall w1, lc_set_dwork w1 -> lc_dwork w1.
Proof.
pose proof lc_dwork_of_lc_set_dwork_lc_dworklist_of_lc_set_dworklist_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_dwork_of_lc_set_dwork : lngen.

Lemma lc_dworklist_of_lc_set_dworklist :
forall wl1, lc_set_dworklist wl1 -> lc_dworklist wl1.
Proof.
pose proof lc_dwork_of_lc_set_dwork_lc_dworklist_of_lc_set_dworklist_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_dworklist_of_lc_set_dworklist : lngen.

(* begin hide *)

Lemma lc_set_expr_of_lc_expr_lc_set_body_of_lc_body_size_mutual :
forall i1,
(forall e1,
  size_expr e1 = i1 ->
  lc_expr e1 ->
  lc_set_expr e1) *
(forall b1,
  size_body b1 = i1 ->
  lc_body b1 ->
  lc_set_body b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind expr_body_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_expr_of_lc_expr
 | apply lc_set_body_of_lc_body
 | apply lc_set_kind_of_lc_kind
 | apply lc_set_expr_of_lc_expr
 | apply lc_set_body_of_lc_body
 | apply lc_set_kind_of_lc_kind];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_expr_of_lc_expr :
forall e1,
  lc_expr e1 ->
  lc_set_expr e1.
Proof.
intros e1; intros;
pose proof (lc_set_expr_of_lc_expr_lc_set_body_of_lc_body_size_mutual (size_expr e1));
intuition eauto.
Qed.

Hint Resolve lc_set_expr_of_lc_expr : lngen.

Lemma lc_set_body_of_lc_body :
forall b1,
  lc_body b1 ->
  lc_set_body b1.
Proof.
intros b1; intros;
pose proof (lc_set_expr_of_lc_expr_lc_set_body_of_lc_body_size_mutual (size_body b1));
intuition eauto.
Qed.

Hint Resolve lc_set_body_of_lc_body : lngen.

(* begin hide *)

Lemma lc_set_context_of_lc_context_size_mutual :
forall i1,
(forall G1,
  size_context G1 = i1 ->
  lc_context G1 ->
  lc_set_context G1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind context_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_expr_of_lc_expr
 | apply lc_set_context_of_lc_context
 | apply lc_set_body_of_lc_body
 | apply lc_set_kind_of_lc_kind];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_context_of_lc_context :
forall G1,
  lc_context G1 ->
  lc_set_context G1.
Proof.
intros G1; intros;
pose proof (lc_set_context_of_lc_context_size_mutual (size_context G1));
intuition eauto.
Qed.

Hint Resolve lc_set_context_of_lc_context : lngen.

(* begin hide *)

Lemma lc_set_obindd_of_lc_obindd_size_mutual :
forall i1,
(forall ob1,
  size_obindd ob1 = i1 ->
  lc_obindd ob1 ->
  lc_set_obindd ob1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind obindd_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_expr_of_lc_expr
 | apply lc_set_body_of_lc_body
 | apply lc_set_kind_of_lc_kind
 | apply lc_set_obindd_of_lc_obindd];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_obindd_of_lc_obindd :
forall ob1,
  lc_obindd ob1 ->
  lc_set_obindd ob1.
Proof.
intros ob1; intros;
pose proof (lc_set_obindd_of_lc_obindd_size_mutual (size_obindd ob1));
intuition eauto.
Qed.

Hint Resolve lc_set_obindd_of_lc_obindd : lngen.

(* begin hide *)

Lemma lc_set_dwork_of_lc_dwork_lc_set_dworklist_of_lc_dworklist_size_mutual :
forall i1,
(forall w1,
  size_dwork w1 = i1 ->
  lc_dwork w1 ->
  lc_set_dwork w1) *
(forall wl1,
  size_dworklist wl1 = i1 ->
  lc_dworklist wl1 ->
  lc_set_dworklist wl1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dwork_dworklist_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_expr_of_lc_expr
 | apply lc_set_body_of_lc_body
 | apply lc_set_dwork_of_lc_dwork
 | apply lc_set_dworklist_of_lc_dworklist
 | apply lc_set_kind_of_lc_kind
 | apply lc_set_obindd_of_lc_obindd
 | apply lc_set_expr_of_lc_expr
 | apply lc_set_body_of_lc_body
 | apply lc_set_dwork_of_lc_dwork
 | apply lc_set_dworklist_of_lc_dworklist
 | apply lc_set_kind_of_lc_kind
 | apply lc_set_obindd_of_lc_obindd];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_dwork_of_lc_dwork :
forall w1,
  lc_dwork w1 ->
  lc_set_dwork w1.
Proof.
intros w1; intros;
pose proof (lc_set_dwork_of_lc_dwork_lc_set_dworklist_of_lc_dworklist_size_mutual (size_dwork w1));
intuition eauto.
Qed.

Hint Resolve lc_set_dwork_of_lc_dwork : lngen.

Lemma lc_set_dworklist_of_lc_dworklist :
forall wl1,
  lc_dworklist wl1 ->
  lc_set_dworklist wl1.
Proof.
intros wl1; intros;
pose proof (lc_set_dwork_of_lc_dwork_lc_set_dworklist_of_lc_dworklist_size_mutual (size_dworklist wl1));
intuition eauto.
Qed.

Hint Resolve lc_set_dworklist_of_lc_dworklist : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_expr_wrt_expr_rec_degree_expr_wrt_expr_close_body_wrt_expr_rec_degree_body_wrt_expr_mutual :
(forall e1 x1 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 `notin` fv_expr e1 ->
  close_expr_wrt_expr_rec n1 x1 e1 = e1) /\
(forall b1 x1 n1,
  degree_body_wrt_expr n1 b1 ->
  x1 `notin` fv_body b1 ->
  close_body_wrt_expr_rec n1 x1 b1 = b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_expr_wrt_expr_rec_degree_expr_wrt_expr :
forall e1 x1 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 `notin` fv_expr e1 ->
  close_expr_wrt_expr_rec n1 x1 e1 = e1.
Proof.
pose proof close_expr_wrt_expr_rec_degree_expr_wrt_expr_close_body_wrt_expr_rec_degree_body_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_expr_wrt_expr_rec_degree_expr_wrt_expr : lngen.
Hint Rewrite close_expr_wrt_expr_rec_degree_expr_wrt_expr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_expr_rec_degree_body_wrt_expr :
forall b1 x1 n1,
  degree_body_wrt_expr n1 b1 ->
  x1 `notin` fv_body b1 ->
  close_body_wrt_expr_rec n1 x1 b1 = b1.
Proof.
pose proof close_expr_wrt_expr_rec_degree_expr_wrt_expr_close_body_wrt_expr_rec_degree_body_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_body_wrt_expr_rec_degree_body_wrt_expr : lngen.
Hint Rewrite close_body_wrt_expr_rec_degree_body_wrt_expr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_context_wrt_expr_rec_degree_context_wrt_expr_mutual :
(forall G1 x1 n1,
  degree_context_wrt_expr n1 G1 ->
  x1 `notin` fv_context G1 ->
  close_context_wrt_expr_rec n1 x1 G1 = G1).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_context_wrt_expr_rec_degree_context_wrt_expr :
forall G1 x1 n1,
  degree_context_wrt_expr n1 G1 ->
  x1 `notin` fv_context G1 ->
  close_context_wrt_expr_rec n1 x1 G1 = G1.
Proof.
pose proof close_context_wrt_expr_rec_degree_context_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_context_wrt_expr_rec_degree_context_wrt_expr : lngen.
Hint Rewrite close_context_wrt_expr_rec_degree_context_wrt_expr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_obindd_wrt_expr_rec_degree_obindd_wrt_expr_mutual :
(forall ob1 x1 n1,
  degree_obindd_wrt_expr n1 ob1 ->
  x1 `notin` fv_obindd ob1 ->
  close_obindd_wrt_expr_rec n1 x1 ob1 = ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_obindd_wrt_expr_rec_degree_obindd_wrt_expr :
forall ob1 x1 n1,
  degree_obindd_wrt_expr n1 ob1 ->
  x1 `notin` fv_obindd ob1 ->
  close_obindd_wrt_expr_rec n1 x1 ob1 = ob1.
Proof.
pose proof close_obindd_wrt_expr_rec_degree_obindd_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_obindd_wrt_expr_rec_degree_obindd_wrt_expr : lngen.
Hint Rewrite close_obindd_wrt_expr_rec_degree_obindd_wrt_expr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dwork_wrt_expr_rec_degree_dwork_wrt_expr_close_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr_mutual :
(forall w1 x1 n1,
  degree_dwork_wrt_expr n1 w1 ->
  x1 `notin` fv_dwork w1 ->
  close_dwork_wrt_expr_rec n1 x1 w1 = w1) /\
(forall wl1 x1 n1,
  degree_dworklist_wrt_expr n1 wl1 ->
  x1 `notin` fv_dworklist wl1 ->
  close_dworklist_wrt_expr_rec n1 x1 wl1 = wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dwork_wrt_expr_rec_degree_dwork_wrt_expr :
forall w1 x1 n1,
  degree_dwork_wrt_expr n1 w1 ->
  x1 `notin` fv_dwork w1 ->
  close_dwork_wrt_expr_rec n1 x1 w1 = w1.
Proof.
pose proof close_dwork_wrt_expr_rec_degree_dwork_wrt_expr_close_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_dwork_wrt_expr_rec_degree_dwork_wrt_expr : lngen.
Hint Rewrite close_dwork_wrt_expr_rec_degree_dwork_wrt_expr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr :
forall wl1 x1 n1,
  degree_dworklist_wrt_expr n1 wl1 ->
  x1 `notin` fv_dworklist wl1 ->
  close_dworklist_wrt_expr_rec n1 x1 wl1 = wl1.
Proof.
pose proof close_dwork_wrt_expr_rec_degree_dwork_wrt_expr_close_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr : lngen.
Hint Rewrite close_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr using solve [auto] : lngen.

(* end hide *)

Lemma close_expr_wrt_expr_lc_expr :
forall e1 x1,
  lc_expr e1 ->
  x1 `notin` fv_expr e1 ->
  close_expr_wrt_expr x1 e1 = e1.
Proof.
unfold close_expr_wrt_expr; default_simp.
Qed.

Hint Resolve close_expr_wrt_expr_lc_expr : lngen.
Hint Rewrite close_expr_wrt_expr_lc_expr using solve [auto] : lngen.

Lemma close_body_wrt_expr_lc_body :
forall b1 x1,
  lc_body b1 ->
  x1 `notin` fv_body b1 ->
  close_body_wrt_expr x1 b1 = b1.
Proof.
unfold close_body_wrt_expr; default_simp.
Qed.

Hint Resolve close_body_wrt_expr_lc_body : lngen.
Hint Rewrite close_body_wrt_expr_lc_body using solve [auto] : lngen.

Lemma close_context_wrt_expr_lc_context :
forall G1 x1,
  lc_context G1 ->
  x1 `notin` fv_context G1 ->
  close_context_wrt_expr x1 G1 = G1.
Proof.
unfold close_context_wrt_expr; default_simp.
Qed.

Hint Resolve close_context_wrt_expr_lc_context : lngen.
Hint Rewrite close_context_wrt_expr_lc_context using solve [auto] : lngen.

Lemma close_obindd_wrt_expr_lc_obindd :
forall ob1 x1,
  lc_obindd ob1 ->
  x1 `notin` fv_obindd ob1 ->
  close_obindd_wrt_expr x1 ob1 = ob1.
Proof.
unfold close_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve close_obindd_wrt_expr_lc_obindd : lngen.
Hint Rewrite close_obindd_wrt_expr_lc_obindd using solve [auto] : lngen.

Lemma close_dwork_wrt_expr_lc_dwork :
forall w1 x1,
  lc_dwork w1 ->
  x1 `notin` fv_dwork w1 ->
  close_dwork_wrt_expr x1 w1 = w1.
Proof.
unfold close_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve close_dwork_wrt_expr_lc_dwork : lngen.
Hint Rewrite close_dwork_wrt_expr_lc_dwork using solve [auto] : lngen.

Lemma close_dworklist_wrt_expr_lc_dworklist :
forall wl1 x1,
  lc_dworklist wl1 ->
  x1 `notin` fv_dworklist wl1 ->
  close_dworklist_wrt_expr x1 wl1 = wl1.
Proof.
unfold close_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve close_dworklist_wrt_expr_lc_dworklist : lngen.
Hint Rewrite close_dworklist_wrt_expr_lc_dworklist using solve [auto] : lngen.

(* begin hide *)

Lemma open_expr_wrt_expr_rec_degree_expr_wrt_expr_open_body_wrt_expr_rec_degree_body_wrt_expr_mutual :
(forall e2 e1 n1,
  degree_expr_wrt_expr n1 e2 ->
  open_expr_wrt_expr_rec n1 e1 e2 = e2) /\
(forall b1 e1 n1,
  degree_body_wrt_expr n1 b1 ->
  open_body_wrt_expr_rec n1 e1 b1 = b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_expr_wrt_expr_rec_degree_expr_wrt_expr :
forall e2 e1 n1,
  degree_expr_wrt_expr n1 e2 ->
  open_expr_wrt_expr_rec n1 e1 e2 = e2.
Proof.
pose proof open_expr_wrt_expr_rec_degree_expr_wrt_expr_open_body_wrt_expr_rec_degree_body_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_expr_wrt_expr_rec_degree_expr_wrt_expr : lngen.
Hint Rewrite open_expr_wrt_expr_rec_degree_expr_wrt_expr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_expr_rec_degree_body_wrt_expr :
forall b1 e1 n1,
  degree_body_wrt_expr n1 b1 ->
  open_body_wrt_expr_rec n1 e1 b1 = b1.
Proof.
pose proof open_expr_wrt_expr_rec_degree_expr_wrt_expr_open_body_wrt_expr_rec_degree_body_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_body_wrt_expr_rec_degree_body_wrt_expr : lngen.
Hint Rewrite open_body_wrt_expr_rec_degree_body_wrt_expr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_context_wrt_expr_rec_degree_context_wrt_expr_mutual :
(forall G1 e1 n1,
  degree_context_wrt_expr n1 G1 ->
  open_context_wrt_expr_rec n1 e1 G1 = G1).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_context_wrt_expr_rec_degree_context_wrt_expr :
forall G1 e1 n1,
  degree_context_wrt_expr n1 G1 ->
  open_context_wrt_expr_rec n1 e1 G1 = G1.
Proof.
pose proof open_context_wrt_expr_rec_degree_context_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_context_wrt_expr_rec_degree_context_wrt_expr : lngen.
Hint Rewrite open_context_wrt_expr_rec_degree_context_wrt_expr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_obindd_wrt_expr_rec_degree_obindd_wrt_expr_mutual :
(forall ob1 e1 n1,
  degree_obindd_wrt_expr n1 ob1 ->
  open_obindd_wrt_expr_rec n1 e1 ob1 = ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_obindd_wrt_expr_rec_degree_obindd_wrt_expr :
forall ob1 e1 n1,
  degree_obindd_wrt_expr n1 ob1 ->
  open_obindd_wrt_expr_rec n1 e1 ob1 = ob1.
Proof.
pose proof open_obindd_wrt_expr_rec_degree_obindd_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_obindd_wrt_expr_rec_degree_obindd_wrt_expr : lngen.
Hint Rewrite open_obindd_wrt_expr_rec_degree_obindd_wrt_expr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dwork_wrt_expr_rec_degree_dwork_wrt_expr_open_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr_mutual :
(forall w1 e1 n1,
  degree_dwork_wrt_expr n1 w1 ->
  open_dwork_wrt_expr_rec n1 e1 w1 = w1) /\
(forall wl1 e1 n1,
  degree_dworklist_wrt_expr n1 wl1 ->
  open_dworklist_wrt_expr_rec n1 e1 wl1 = wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dwork_wrt_expr_rec_degree_dwork_wrt_expr :
forall w1 e1 n1,
  degree_dwork_wrt_expr n1 w1 ->
  open_dwork_wrt_expr_rec n1 e1 w1 = w1.
Proof.
pose proof open_dwork_wrt_expr_rec_degree_dwork_wrt_expr_open_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_dwork_wrt_expr_rec_degree_dwork_wrt_expr : lngen.
Hint Rewrite open_dwork_wrt_expr_rec_degree_dwork_wrt_expr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr :
forall wl1 e1 n1,
  degree_dworklist_wrt_expr n1 wl1 ->
  open_dworklist_wrt_expr_rec n1 e1 wl1 = wl1.
Proof.
pose proof open_dwork_wrt_expr_rec_degree_dwork_wrt_expr_open_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr : lngen.
Hint Rewrite open_dworklist_wrt_expr_rec_degree_dworklist_wrt_expr using solve [auto] : lngen.

(* end hide *)

Lemma open_expr_wrt_expr_lc_expr :
forall e2 e1,
  lc_expr e2 ->
  open_expr_wrt_expr e2 e1 = e2.
Proof.
unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve open_expr_wrt_expr_lc_expr : lngen.
Hint Rewrite open_expr_wrt_expr_lc_expr using solve [auto] : lngen.

Lemma open_body_wrt_expr_lc_body :
forall b1 e1,
  lc_body b1 ->
  open_body_wrt_expr b1 e1 = b1.
Proof.
unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve open_body_wrt_expr_lc_body : lngen.
Hint Rewrite open_body_wrt_expr_lc_body using solve [auto] : lngen.

Lemma open_context_wrt_expr_lc_context :
forall G1 e1,
  lc_context G1 ->
  open_context_wrt_expr G1 e1 = G1.
Proof.
unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve open_context_wrt_expr_lc_context : lngen.
Hint Rewrite open_context_wrt_expr_lc_context using solve [auto] : lngen.

Lemma open_obindd_wrt_expr_lc_obindd :
forall ob1 e1,
  lc_obindd ob1 ->
  open_obindd_wrt_expr ob1 e1 = ob1.
Proof.
unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve open_obindd_wrt_expr_lc_obindd : lngen.
Hint Rewrite open_obindd_wrt_expr_lc_obindd using solve [auto] : lngen.

Lemma open_dwork_wrt_expr_lc_dwork :
forall w1 e1,
  lc_dwork w1 ->
  open_dwork_wrt_expr w1 e1 = w1.
Proof.
unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve open_dwork_wrt_expr_lc_dwork : lngen.
Hint Rewrite open_dwork_wrt_expr_lc_dwork using solve [auto] : lngen.

Lemma open_dworklist_wrt_expr_lc_dworklist :
forall wl1 e1,
  lc_dworklist wl1 ->
  open_dworklist_wrt_expr wl1 e1 = wl1.
Proof.
unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve open_dworklist_wrt_expr_lc_dworklist : lngen.
Hint Rewrite open_dworklist_wrt_expr_lc_dworklist using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_expr_close_expr_wrt_expr_rec_fv_body_close_body_wrt_expr_rec_mutual :
(forall e1 x1 n1,
  fv_expr (close_expr_wrt_expr_rec n1 x1 e1) [=] remove x1 (fv_expr e1)) /\
(forall b1 x1 n1,
  fv_body (close_body_wrt_expr_rec n1 x1 b1) [=] remove x1 (fv_body b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_expr_close_expr_wrt_expr_rec :
forall e1 x1 n1,
  fv_expr (close_expr_wrt_expr_rec n1 x1 e1) [=] remove x1 (fv_expr e1).
Proof.
pose proof fv_expr_close_expr_wrt_expr_rec_fv_body_close_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_expr_close_expr_wrt_expr_rec : lngen.
Hint Rewrite fv_expr_close_expr_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_body_close_body_wrt_expr_rec :
forall b1 x1 n1,
  fv_body (close_body_wrt_expr_rec n1 x1 b1) [=] remove x1 (fv_body b1).
Proof.
pose proof fv_expr_close_expr_wrt_expr_rec_fv_body_close_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_body_close_body_wrt_expr_rec : lngen.
Hint Rewrite fv_body_close_body_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_context_close_context_wrt_expr_rec_mutual :
(forall G1 x1 n1,
  fv_context (close_context_wrt_expr_rec n1 x1 G1) [=] remove x1 (fv_context G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_context_close_context_wrt_expr_rec :
forall G1 x1 n1,
  fv_context (close_context_wrt_expr_rec n1 x1 G1) [=] remove x1 (fv_context G1).
Proof.
pose proof fv_context_close_context_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_context_close_context_wrt_expr_rec : lngen.
Hint Rewrite fv_context_close_context_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_obindd_close_obindd_wrt_expr_rec_mutual :
(forall ob1 x1 n1,
  fv_obindd (close_obindd_wrt_expr_rec n1 x1 ob1) [=] remove x1 (fv_obindd ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_obindd_close_obindd_wrt_expr_rec :
forall ob1 x1 n1,
  fv_obindd (close_obindd_wrt_expr_rec n1 x1 ob1) [=] remove x1 (fv_obindd ob1).
Proof.
pose proof fv_obindd_close_obindd_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obindd_close_obindd_wrt_expr_rec : lngen.
Hint Rewrite fv_obindd_close_obindd_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_dwork_close_dwork_wrt_expr_rec_fv_dworklist_close_dworklist_wrt_expr_rec_mutual :
(forall w1 x1 n1,
  fv_dwork (close_dwork_wrt_expr_rec n1 x1 w1) [=] remove x1 (fv_dwork w1)) /\
(forall wl1 x1 n1,
  fv_dworklist (close_dworklist_wrt_expr_rec n1 x1 wl1) [=] remove x1 (fv_dworklist wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_dwork_close_dwork_wrt_expr_rec :
forall w1 x1 n1,
  fv_dwork (close_dwork_wrt_expr_rec n1 x1 w1) [=] remove x1 (fv_dwork w1).
Proof.
pose proof fv_dwork_close_dwork_wrt_expr_rec_fv_dworklist_close_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dwork_close_dwork_wrt_expr_rec : lngen.
Hint Rewrite fv_dwork_close_dwork_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_dworklist_close_dworklist_wrt_expr_rec :
forall wl1 x1 n1,
  fv_dworklist (close_dworklist_wrt_expr_rec n1 x1 wl1) [=] remove x1 (fv_dworklist wl1).
Proof.
pose proof fv_dwork_close_dwork_wrt_expr_rec_fv_dworklist_close_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dworklist_close_dworklist_wrt_expr_rec : lngen.
Hint Rewrite fv_dworklist_close_dworklist_wrt_expr_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_expr_close_expr_wrt_expr :
forall e1 x1,
  fv_expr (close_expr_wrt_expr x1 e1) [=] remove x1 (fv_expr e1).
Proof.
unfold close_expr_wrt_expr; default_simp.
Qed.

Hint Resolve fv_expr_close_expr_wrt_expr : lngen.
Hint Rewrite fv_expr_close_expr_wrt_expr using solve [auto] : lngen.

Lemma fv_body_close_body_wrt_expr :
forall b1 x1,
  fv_body (close_body_wrt_expr x1 b1) [=] remove x1 (fv_body b1).
Proof.
unfold close_body_wrt_expr; default_simp.
Qed.

Hint Resolve fv_body_close_body_wrt_expr : lngen.
Hint Rewrite fv_body_close_body_wrt_expr using solve [auto] : lngen.

Lemma fv_context_close_context_wrt_expr :
forall G1 x1,
  fv_context (close_context_wrt_expr x1 G1) [=] remove x1 (fv_context G1).
Proof.
unfold close_context_wrt_expr; default_simp.
Qed.

Hint Resolve fv_context_close_context_wrt_expr : lngen.
Hint Rewrite fv_context_close_context_wrt_expr using solve [auto] : lngen.

Lemma fv_obindd_close_obindd_wrt_expr :
forall ob1 x1,
  fv_obindd (close_obindd_wrt_expr x1 ob1) [=] remove x1 (fv_obindd ob1).
Proof.
unfold close_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve fv_obindd_close_obindd_wrt_expr : lngen.
Hint Rewrite fv_obindd_close_obindd_wrt_expr using solve [auto] : lngen.

Lemma fv_dwork_close_dwork_wrt_expr :
forall w1 x1,
  fv_dwork (close_dwork_wrt_expr x1 w1) [=] remove x1 (fv_dwork w1).
Proof.
unfold close_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve fv_dwork_close_dwork_wrt_expr : lngen.
Hint Rewrite fv_dwork_close_dwork_wrt_expr using solve [auto] : lngen.

Lemma fv_dworklist_close_dworklist_wrt_expr :
forall wl1 x1,
  fv_dworklist (close_dworklist_wrt_expr x1 wl1) [=] remove x1 (fv_dworklist wl1).
Proof.
unfold close_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve fv_dworklist_close_dworklist_wrt_expr : lngen.
Hint Rewrite fv_dworklist_close_dworklist_wrt_expr using solve [auto] : lngen.

(* begin hide *)

Lemma fv_expr_open_expr_wrt_expr_rec_lower_fv_body_open_body_wrt_expr_rec_lower_mutual :
(forall e1 e2 n1,
  fv_expr e1 [<=] fv_expr (open_expr_wrt_expr_rec n1 e2 e1)) /\
(forall b1 e1 n1,
  fv_body b1 [<=] fv_body (open_body_wrt_expr_rec n1 e1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_expr_open_expr_wrt_expr_rec_lower :
forall e1 e2 n1,
  fv_expr e1 [<=] fv_expr (open_expr_wrt_expr_rec n1 e2 e1).
Proof.
pose proof fv_expr_open_expr_wrt_expr_rec_lower_fv_body_open_body_wrt_expr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_expr_open_expr_wrt_expr_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_body_open_body_wrt_expr_rec_lower :
forall b1 e1 n1,
  fv_body b1 [<=] fv_body (open_body_wrt_expr_rec n1 e1 b1).
Proof.
pose proof fv_expr_open_expr_wrt_expr_rec_lower_fv_body_open_body_wrt_expr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_body_open_body_wrt_expr_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_context_open_context_wrt_expr_rec_lower_mutual :
(forall G1 e1 n1,
  fv_context G1 [<=] fv_context (open_context_wrt_expr_rec n1 e1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_context_open_context_wrt_expr_rec_lower :
forall G1 e1 n1,
  fv_context G1 [<=] fv_context (open_context_wrt_expr_rec n1 e1 G1).
Proof.
pose proof fv_context_open_context_wrt_expr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_context_open_context_wrt_expr_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_obindd_open_obindd_wrt_expr_rec_lower_mutual :
(forall ob1 e1 n1,
  fv_obindd ob1 [<=] fv_obindd (open_obindd_wrt_expr_rec n1 e1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_obindd_open_obindd_wrt_expr_rec_lower :
forall ob1 e1 n1,
  fv_obindd ob1 [<=] fv_obindd (open_obindd_wrt_expr_rec n1 e1 ob1).
Proof.
pose proof fv_obindd_open_obindd_wrt_expr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obindd_open_obindd_wrt_expr_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_dwork_open_dwork_wrt_expr_rec_lower_fv_dworklist_open_dworklist_wrt_expr_rec_lower_mutual :
(forall w1 e1 n1,
  fv_dwork w1 [<=] fv_dwork (open_dwork_wrt_expr_rec n1 e1 w1)) /\
(forall wl1 e1 n1,
  fv_dworklist wl1 [<=] fv_dworklist (open_dworklist_wrt_expr_rec n1 e1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_dwork_open_dwork_wrt_expr_rec_lower :
forall w1 e1 n1,
  fv_dwork w1 [<=] fv_dwork (open_dwork_wrt_expr_rec n1 e1 w1).
Proof.
pose proof fv_dwork_open_dwork_wrt_expr_rec_lower_fv_dworklist_open_dworklist_wrt_expr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dwork_open_dwork_wrt_expr_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_dworklist_open_dworklist_wrt_expr_rec_lower :
forall wl1 e1 n1,
  fv_dworklist wl1 [<=] fv_dworklist (open_dworklist_wrt_expr_rec n1 e1 wl1).
Proof.
pose proof fv_dwork_open_dwork_wrt_expr_rec_lower_fv_dworklist_open_dworklist_wrt_expr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dworklist_open_dworklist_wrt_expr_rec_lower : lngen.

(* end hide *)

Lemma fv_expr_open_expr_wrt_expr_lower :
forall e1 e2,
  fv_expr e1 [<=] fv_expr (open_expr_wrt_expr e1 e2).
Proof.
unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve fv_expr_open_expr_wrt_expr_lower : lngen.

Lemma fv_body_open_body_wrt_expr_lower :
forall b1 e1,
  fv_body b1 [<=] fv_body (open_body_wrt_expr b1 e1).
Proof.
unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve fv_body_open_body_wrt_expr_lower : lngen.

Lemma fv_context_open_context_wrt_expr_lower :
forall G1 e1,
  fv_context G1 [<=] fv_context (open_context_wrt_expr G1 e1).
Proof.
unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve fv_context_open_context_wrt_expr_lower : lngen.

Lemma fv_obindd_open_obindd_wrt_expr_lower :
forall ob1 e1,
  fv_obindd ob1 [<=] fv_obindd (open_obindd_wrt_expr ob1 e1).
Proof.
unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve fv_obindd_open_obindd_wrt_expr_lower : lngen.

Lemma fv_dwork_open_dwork_wrt_expr_lower :
forall w1 e1,
  fv_dwork w1 [<=] fv_dwork (open_dwork_wrt_expr w1 e1).
Proof.
unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve fv_dwork_open_dwork_wrt_expr_lower : lngen.

Lemma fv_dworklist_open_dworklist_wrt_expr_lower :
forall wl1 e1,
  fv_dworklist wl1 [<=] fv_dworklist (open_dworklist_wrt_expr wl1 e1).
Proof.
unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve fv_dworklist_open_dworklist_wrt_expr_lower : lngen.

(* begin hide *)

Lemma fv_expr_open_expr_wrt_expr_rec_upper_fv_body_open_body_wrt_expr_rec_upper_mutual :
(forall e1 e2 n1,
  fv_expr (open_expr_wrt_expr_rec n1 e2 e1) [<=] fv_expr e2 `union` fv_expr e1) /\
(forall b1 e1 n1,
  fv_body (open_body_wrt_expr_rec n1 e1 b1) [<=] fv_expr e1 `union` fv_body b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_expr_open_expr_wrt_expr_rec_upper :
forall e1 e2 n1,
  fv_expr (open_expr_wrt_expr_rec n1 e2 e1) [<=] fv_expr e2 `union` fv_expr e1.
Proof.
pose proof fv_expr_open_expr_wrt_expr_rec_upper_fv_body_open_body_wrt_expr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_expr_open_expr_wrt_expr_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_body_open_body_wrt_expr_rec_upper :
forall b1 e1 n1,
  fv_body (open_body_wrt_expr_rec n1 e1 b1) [<=] fv_expr e1 `union` fv_body b1.
Proof.
pose proof fv_expr_open_expr_wrt_expr_rec_upper_fv_body_open_body_wrt_expr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_body_open_body_wrt_expr_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_context_open_context_wrt_expr_rec_upper_mutual :
(forall G1 e1 n1,
  fv_context (open_context_wrt_expr_rec n1 e1 G1) [<=] fv_expr e1 `union` fv_context G1).
Proof.
apply_mutual_ind context_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_context_open_context_wrt_expr_rec_upper :
forall G1 e1 n1,
  fv_context (open_context_wrt_expr_rec n1 e1 G1) [<=] fv_expr e1 `union` fv_context G1.
Proof.
pose proof fv_context_open_context_wrt_expr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_context_open_context_wrt_expr_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_obindd_open_obindd_wrt_expr_rec_upper_mutual :
(forall ob1 e1 n1,
  fv_obindd (open_obindd_wrt_expr_rec n1 e1 ob1) [<=] fv_expr e1 `union` fv_obindd ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_obindd_open_obindd_wrt_expr_rec_upper :
forall ob1 e1 n1,
  fv_obindd (open_obindd_wrt_expr_rec n1 e1 ob1) [<=] fv_expr e1 `union` fv_obindd ob1.
Proof.
pose proof fv_obindd_open_obindd_wrt_expr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obindd_open_obindd_wrt_expr_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_dwork_open_dwork_wrt_expr_rec_upper_fv_dworklist_open_dworklist_wrt_expr_rec_upper_mutual :
(forall w1 e1 n1,
  fv_dwork (open_dwork_wrt_expr_rec n1 e1 w1) [<=] fv_expr e1 `union` fv_dwork w1) /\
(forall wl1 e1 n1,
  fv_dworklist (open_dworklist_wrt_expr_rec n1 e1 wl1) [<=] fv_expr e1 `union` fv_dworklist wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_dwork_open_dwork_wrt_expr_rec_upper :
forall w1 e1 n1,
  fv_dwork (open_dwork_wrt_expr_rec n1 e1 w1) [<=] fv_expr e1 `union` fv_dwork w1.
Proof.
pose proof fv_dwork_open_dwork_wrt_expr_rec_upper_fv_dworklist_open_dworklist_wrt_expr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dwork_open_dwork_wrt_expr_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_dworklist_open_dworklist_wrt_expr_rec_upper :
forall wl1 e1 n1,
  fv_dworklist (open_dworklist_wrt_expr_rec n1 e1 wl1) [<=] fv_expr e1 `union` fv_dworklist wl1.
Proof.
pose proof fv_dwork_open_dwork_wrt_expr_rec_upper_fv_dworklist_open_dworklist_wrt_expr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dworklist_open_dworklist_wrt_expr_rec_upper : lngen.

(* end hide *)

Lemma fv_expr_open_expr_wrt_expr_upper :
forall e1 e2,
  fv_expr (open_expr_wrt_expr e1 e2) [<=] fv_expr e2 `union` fv_expr e1.
Proof.
unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve fv_expr_open_expr_wrt_expr_upper : lngen.

Lemma fv_body_open_body_wrt_expr_upper :
forall b1 e1,
  fv_body (open_body_wrt_expr b1 e1) [<=] fv_expr e1 `union` fv_body b1.
Proof.
unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve fv_body_open_body_wrt_expr_upper : lngen.

Lemma fv_context_open_context_wrt_expr_upper :
forall G1 e1,
  fv_context (open_context_wrt_expr G1 e1) [<=] fv_expr e1 `union` fv_context G1.
Proof.
unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve fv_context_open_context_wrt_expr_upper : lngen.

Lemma fv_obindd_open_obindd_wrt_expr_upper :
forall ob1 e1,
  fv_obindd (open_obindd_wrt_expr ob1 e1) [<=] fv_expr e1 `union` fv_obindd ob1.
Proof.
unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve fv_obindd_open_obindd_wrt_expr_upper : lngen.

Lemma fv_dwork_open_dwork_wrt_expr_upper :
forall w1 e1,
  fv_dwork (open_dwork_wrt_expr w1 e1) [<=] fv_expr e1 `union` fv_dwork w1.
Proof.
unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve fv_dwork_open_dwork_wrt_expr_upper : lngen.

Lemma fv_dworklist_open_dworklist_wrt_expr_upper :
forall wl1 e1,
  fv_dworklist (open_dworklist_wrt_expr wl1 e1) [<=] fv_expr e1 `union` fv_dworklist wl1.
Proof.
unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve fv_dworklist_open_dworklist_wrt_expr_upper : lngen.

(* begin hide *)

Lemma fv_expr_subst_expr_fresh_fv_body_subst_body_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_expr e1 ->
  fv_expr (subst_expr e2 x1 e1) [=] fv_expr e1) /\
(forall b1 e1 x1,
  x1 `notin` fv_body b1 ->
  fv_body (subst_body e1 x1 b1) [=] fv_body b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_expr_subst_expr_fresh :
forall e1 e2 x1,
  x1 `notin` fv_expr e1 ->
  fv_expr (subst_expr e2 x1 e1) [=] fv_expr e1.
Proof.
pose proof fv_expr_subst_expr_fresh_fv_body_subst_body_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_expr_subst_expr_fresh : lngen.
Hint Rewrite fv_expr_subst_expr_fresh using solve [auto] : lngen.

Lemma fv_body_subst_body_fresh :
forall b1 e1 x1,
  x1 `notin` fv_body b1 ->
  fv_body (subst_body e1 x1 b1) [=] fv_body b1.
Proof.
pose proof fv_expr_subst_expr_fresh_fv_body_subst_body_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_body_subst_body_fresh : lngen.
Hint Rewrite fv_body_subst_body_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_context_subst_context_fresh_mutual :
(forall G1 e1 x1,
  x1 `notin` fv_context G1 ->
  fv_context (subst_context e1 x1 G1) [=] fv_context G1).
Proof.
apply_mutual_ind context_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_context_subst_context_fresh :
forall G1 e1 x1,
  x1 `notin` fv_context G1 ->
  fv_context (subst_context e1 x1 G1) [=] fv_context G1.
Proof.
pose proof fv_context_subst_context_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_context_subst_context_fresh : lngen.
Hint Rewrite fv_context_subst_context_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_obindd_subst_obindd_fresh_mutual :
(forall ob1 e1 x1,
  x1 `notin` fv_obindd ob1 ->
  fv_obindd (subst_obindd e1 x1 ob1) [=] fv_obindd ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_obindd_subst_obindd_fresh :
forall ob1 e1 x1,
  x1 `notin` fv_obindd ob1 ->
  fv_obindd (subst_obindd e1 x1 ob1) [=] fv_obindd ob1.
Proof.
pose proof fv_obindd_subst_obindd_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obindd_subst_obindd_fresh : lngen.
Hint Rewrite fv_obindd_subst_obindd_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_dwork_subst_dwork_fresh_fv_dworklist_subst_dworklist_fresh_mutual :
(forall w1 e1 x1,
  x1 `notin` fv_dwork w1 ->
  fv_dwork (subst_dwork e1 x1 w1) [=] fv_dwork w1) /\
(forall wl1 e1 x1,
  x1 `notin` fv_dworklist wl1 ->
  fv_dworklist (subst_dworklist e1 x1 wl1) [=] fv_dworklist wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dwork_subst_dwork_fresh :
forall w1 e1 x1,
  x1 `notin` fv_dwork w1 ->
  fv_dwork (subst_dwork e1 x1 w1) [=] fv_dwork w1.
Proof.
pose proof fv_dwork_subst_dwork_fresh_fv_dworklist_subst_dworklist_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dwork_subst_dwork_fresh : lngen.
Hint Rewrite fv_dwork_subst_dwork_fresh using solve [auto] : lngen.

Lemma fv_dworklist_subst_dworklist_fresh :
forall wl1 e1 x1,
  x1 `notin` fv_dworklist wl1 ->
  fv_dworklist (subst_dworklist e1 x1 wl1) [=] fv_dworklist wl1.
Proof.
pose proof fv_dwork_subst_dwork_fresh_fv_dworklist_subst_dworklist_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dworklist_subst_dworklist_fresh : lngen.
Hint Rewrite fv_dworklist_subst_dworklist_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_expr_subst_expr_lower_fv_body_subst_body_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_expr e1) [<=] fv_expr (subst_expr e2 x1 e1)) /\
(forall b1 e1 x1,
  remove x1 (fv_body b1) [<=] fv_body (subst_body e1 x1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_expr_subst_expr_lower :
forall e1 e2 x1,
  remove x1 (fv_expr e1) [<=] fv_expr (subst_expr e2 x1 e1).
Proof.
pose proof fv_expr_subst_expr_lower_fv_body_subst_body_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_expr_subst_expr_lower : lngen.

Lemma fv_body_subst_body_lower :
forall b1 e1 x1,
  remove x1 (fv_body b1) [<=] fv_body (subst_body e1 x1 b1).
Proof.
pose proof fv_expr_subst_expr_lower_fv_body_subst_body_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_body_subst_body_lower : lngen.

(* begin hide *)

Lemma fv_context_subst_context_lower_mutual :
(forall G1 e1 x1,
  remove x1 (fv_context G1) [<=] fv_context (subst_context e1 x1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_context_subst_context_lower :
forall G1 e1 x1,
  remove x1 (fv_context G1) [<=] fv_context (subst_context e1 x1 G1).
Proof.
pose proof fv_context_subst_context_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_context_subst_context_lower : lngen.

(* begin hide *)

Lemma fv_obindd_subst_obindd_lower_mutual :
(forall ob1 e1 x1,
  remove x1 (fv_obindd ob1) [<=] fv_obindd (subst_obindd e1 x1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_obindd_subst_obindd_lower :
forall ob1 e1 x1,
  remove x1 (fv_obindd ob1) [<=] fv_obindd (subst_obindd e1 x1 ob1).
Proof.
pose proof fv_obindd_subst_obindd_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obindd_subst_obindd_lower : lngen.

(* begin hide *)

Lemma fv_dwork_subst_dwork_lower_fv_dworklist_subst_dworklist_lower_mutual :
(forall w1 e1 x1,
  remove x1 (fv_dwork w1) [<=] fv_dwork (subst_dwork e1 x1 w1)) /\
(forall wl1 e1 x1,
  remove x1 (fv_dworklist wl1) [<=] fv_dworklist (subst_dworklist e1 x1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dwork_subst_dwork_lower :
forall w1 e1 x1,
  remove x1 (fv_dwork w1) [<=] fv_dwork (subst_dwork e1 x1 w1).
Proof.
pose proof fv_dwork_subst_dwork_lower_fv_dworklist_subst_dworklist_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dwork_subst_dwork_lower : lngen.

Lemma fv_dworklist_subst_dworklist_lower :
forall wl1 e1 x1,
  remove x1 (fv_dworklist wl1) [<=] fv_dworklist (subst_dworklist e1 x1 wl1).
Proof.
pose proof fv_dwork_subst_dwork_lower_fv_dworklist_subst_dworklist_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dworklist_subst_dworklist_lower : lngen.

(* begin hide *)

Lemma fv_expr_subst_expr_notin_fv_body_subst_body_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_expr e2 ->
  x2 `notin` fv_expr (subst_expr e2 x1 e1)) /\
(forall b1 e1 x1 x2,
  x2 `notin` fv_body b1 ->
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_body (subst_body e1 x1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_expr_subst_expr_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_expr e2 ->
  x2 `notin` fv_expr (subst_expr e2 x1 e1).
Proof.
pose proof fv_expr_subst_expr_notin_fv_body_subst_body_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_expr_subst_expr_notin : lngen.

Lemma fv_body_subst_body_notin :
forall b1 e1 x1 x2,
  x2 `notin` fv_body b1 ->
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_body (subst_body e1 x1 b1).
Proof.
pose proof fv_expr_subst_expr_notin_fv_body_subst_body_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_body_subst_body_notin : lngen.

(* begin hide *)

Lemma fv_context_subst_context_notin_mutual :
(forall G1 e1 x1 x2,
  x2 `notin` fv_context G1 ->
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_context (subst_context e1 x1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_context_subst_context_notin :
forall G1 e1 x1 x2,
  x2 `notin` fv_context G1 ->
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_context (subst_context e1 x1 G1).
Proof.
pose proof fv_context_subst_context_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_context_subst_context_notin : lngen.

(* begin hide *)

Lemma fv_obindd_subst_obindd_notin_mutual :
(forall ob1 e1 x1 x2,
  x2 `notin` fv_obindd ob1 ->
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_obindd (subst_obindd e1 x1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_obindd_subst_obindd_notin :
forall ob1 e1 x1 x2,
  x2 `notin` fv_obindd ob1 ->
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_obindd (subst_obindd e1 x1 ob1).
Proof.
pose proof fv_obindd_subst_obindd_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obindd_subst_obindd_notin : lngen.

(* begin hide *)

Lemma fv_dwork_subst_dwork_notin_fv_dworklist_subst_dworklist_notin_mutual :
(forall w1 e1 x1 x2,
  x2 `notin` fv_dwork w1 ->
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_dwork (subst_dwork e1 x1 w1)) /\
(forall wl1 e1 x1 x2,
  x2 `notin` fv_dworklist wl1 ->
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_dworklist (subst_dworklist e1 x1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dwork_subst_dwork_notin :
forall w1 e1 x1 x2,
  x2 `notin` fv_dwork w1 ->
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_dwork (subst_dwork e1 x1 w1).
Proof.
pose proof fv_dwork_subst_dwork_notin_fv_dworklist_subst_dworklist_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dwork_subst_dwork_notin : lngen.

Lemma fv_dworklist_subst_dworklist_notin :
forall wl1 e1 x1 x2,
  x2 `notin` fv_dworklist wl1 ->
  x2 `notin` fv_expr e1 ->
  x2 `notin` fv_dworklist (subst_dworklist e1 x1 wl1).
Proof.
pose proof fv_dwork_subst_dwork_notin_fv_dworklist_subst_dworklist_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dworklist_subst_dworklist_notin : lngen.

(* begin hide *)

Lemma fv_expr_subst_expr_upper_fv_body_subst_body_upper_mutual :
(forall e1 e2 x1,
  fv_expr (subst_expr e2 x1 e1) [<=] fv_expr e2 `union` remove x1 (fv_expr e1)) /\
(forall b1 e1 x1,
  fv_body (subst_body e1 x1 b1) [<=] fv_expr e1 `union` remove x1 (fv_body b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_expr_subst_expr_upper :
forall e1 e2 x1,
  fv_expr (subst_expr e2 x1 e1) [<=] fv_expr e2 `union` remove x1 (fv_expr e1).
Proof.
pose proof fv_expr_subst_expr_upper_fv_body_subst_body_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_expr_subst_expr_upper : lngen.

Lemma fv_body_subst_body_upper :
forall b1 e1 x1,
  fv_body (subst_body e1 x1 b1) [<=] fv_expr e1 `union` remove x1 (fv_body b1).
Proof.
pose proof fv_expr_subst_expr_upper_fv_body_subst_body_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_body_subst_body_upper : lngen.

(* begin hide *)

Lemma fv_context_subst_context_upper_mutual :
(forall G1 e1 x1,
  fv_context (subst_context e1 x1 G1) [<=] fv_expr e1 `union` remove x1 (fv_context G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_context_subst_context_upper :
forall G1 e1 x1,
  fv_context (subst_context e1 x1 G1) [<=] fv_expr e1 `union` remove x1 (fv_context G1).
Proof.
pose proof fv_context_subst_context_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_context_subst_context_upper : lngen.

(* begin hide *)

Lemma fv_obindd_subst_obindd_upper_mutual :
(forall ob1 e1 x1,
  fv_obindd (subst_obindd e1 x1 ob1) [<=] fv_expr e1 `union` remove x1 (fv_obindd ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_obindd_subst_obindd_upper :
forall ob1 e1 x1,
  fv_obindd (subst_obindd e1 x1 ob1) [<=] fv_expr e1 `union` remove x1 (fv_obindd ob1).
Proof.
pose proof fv_obindd_subst_obindd_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obindd_subst_obindd_upper : lngen.

(* begin hide *)

Lemma fv_dwork_subst_dwork_upper_fv_dworklist_subst_dworklist_upper_mutual :
(forall w1 e1 x1,
  fv_dwork (subst_dwork e1 x1 w1) [<=] fv_expr e1 `union` remove x1 (fv_dwork w1)) /\
(forall wl1 e1 x1,
  fv_dworklist (subst_dworklist e1 x1 wl1) [<=] fv_expr e1 `union` remove x1 (fv_dworklist wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dwork_subst_dwork_upper :
forall w1 e1 x1,
  fv_dwork (subst_dwork e1 x1 w1) [<=] fv_expr e1 `union` remove x1 (fv_dwork w1).
Proof.
pose proof fv_dwork_subst_dwork_upper_fv_dworklist_subst_dworklist_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dwork_subst_dwork_upper : lngen.

Lemma fv_dworklist_subst_dworklist_upper :
forall wl1 e1 x1,
  fv_dworklist (subst_dworklist e1 x1 wl1) [<=] fv_expr e1 `union` remove x1 (fv_dworklist wl1).
Proof.
pose proof fv_dwork_subst_dwork_upper_fv_dworklist_subst_dworklist_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dworklist_subst_dworklist_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_expr_close_expr_wrt_expr_rec_subst_body_close_body_wrt_expr_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_expr e1 x1 (close_expr_wrt_expr_rec n1 x2 e2) = close_expr_wrt_expr_rec n1 x2 (subst_expr e1 x1 e2)) /\
(forall b1 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_body e1 x1 (close_body_wrt_expr_rec n1 x2 b1) = close_body_wrt_expr_rec n1 x2 (subst_body e1 x1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_expr_close_expr_wrt_expr_rec :
forall e2 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_expr e1 x1 (close_expr_wrt_expr_rec n1 x2 e2) = close_expr_wrt_expr_rec n1 x2 (subst_expr e1 x1 e2).
Proof.
pose proof subst_expr_close_expr_wrt_expr_rec_subst_body_close_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_expr_close_expr_wrt_expr_rec : lngen.

Lemma subst_body_close_body_wrt_expr_rec :
forall b1 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_body e1 x1 (close_body_wrt_expr_rec n1 x2 b1) = close_body_wrt_expr_rec n1 x2 (subst_body e1 x1 b1).
Proof.
pose proof subst_expr_close_expr_wrt_expr_rec_subst_body_close_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_body_close_body_wrt_expr_rec : lngen.

(* begin hide *)

Lemma subst_context_close_context_wrt_expr_rec_mutual :
(forall G1 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_context e1 x1 (close_context_wrt_expr_rec n1 x2 G1) = close_context_wrt_expr_rec n1 x2 (subst_context e1 x1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_context_close_context_wrt_expr_rec :
forall G1 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_context e1 x1 (close_context_wrt_expr_rec n1 x2 G1) = close_context_wrt_expr_rec n1 x2 (subst_context e1 x1 G1).
Proof.
pose proof subst_context_close_context_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_context_close_context_wrt_expr_rec : lngen.

(* begin hide *)

Lemma subst_obindd_close_obindd_wrt_expr_rec_mutual :
(forall ob1 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_obindd e1 x1 (close_obindd_wrt_expr_rec n1 x2 ob1) = close_obindd_wrt_expr_rec n1 x2 (subst_obindd e1 x1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obindd_close_obindd_wrt_expr_rec :
forall ob1 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_obindd e1 x1 (close_obindd_wrt_expr_rec n1 x2 ob1) = close_obindd_wrt_expr_rec n1 x2 (subst_obindd e1 x1 ob1).
Proof.
pose proof subst_obindd_close_obindd_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obindd_close_obindd_wrt_expr_rec : lngen.

(* begin hide *)

Lemma subst_dwork_close_dwork_wrt_expr_rec_subst_dworklist_close_dworklist_wrt_expr_rec_mutual :
(forall w1 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_dwork e1 x1 (close_dwork_wrt_expr_rec n1 x2 w1) = close_dwork_wrt_expr_rec n1 x2 (subst_dwork e1 x1 w1)) /\
(forall wl1 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_dworklist e1 x1 (close_dworklist_wrt_expr_rec n1 x2 wl1) = close_dworklist_wrt_expr_rec n1 x2 (subst_dworklist e1 x1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dwork_close_dwork_wrt_expr_rec :
forall w1 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_dwork e1 x1 (close_dwork_wrt_expr_rec n1 x2 w1) = close_dwork_wrt_expr_rec n1 x2 (subst_dwork e1 x1 w1).
Proof.
pose proof subst_dwork_close_dwork_wrt_expr_rec_subst_dworklist_close_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dwork_close_dwork_wrt_expr_rec : lngen.

Lemma subst_dworklist_close_dworklist_wrt_expr_rec :
forall wl1 e1 x1 x2 n1,
  degree_expr_wrt_expr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_dworklist e1 x1 (close_dworklist_wrt_expr_rec n1 x2 wl1) = close_dworklist_wrt_expr_rec n1 x2 (subst_dworklist e1 x1 wl1).
Proof.
pose proof subst_dwork_close_dwork_wrt_expr_rec_subst_dworklist_close_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dworklist_close_dworklist_wrt_expr_rec : lngen.

Lemma subst_expr_close_expr_wrt_expr :
forall e2 e1 x1 x2,
  lc_expr e1 ->  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_expr e1 x1 (close_expr_wrt_expr x2 e2) = close_expr_wrt_expr x2 (subst_expr e1 x1 e2).
Proof.
unfold close_expr_wrt_expr; default_simp.
Qed.

Hint Resolve subst_expr_close_expr_wrt_expr : lngen.

Lemma subst_body_close_body_wrt_expr :
forall b1 e1 x1 x2,
  lc_expr e1 ->  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_body e1 x1 (close_body_wrt_expr x2 b1) = close_body_wrt_expr x2 (subst_body e1 x1 b1).
Proof.
unfold close_body_wrt_expr; default_simp.
Qed.

Hint Resolve subst_body_close_body_wrt_expr : lngen.

Lemma subst_context_close_context_wrt_expr :
forall G1 e1 x1 x2,
  lc_expr e1 ->  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_context e1 x1 (close_context_wrt_expr x2 G1) = close_context_wrt_expr x2 (subst_context e1 x1 G1).
Proof.
unfold close_context_wrt_expr; default_simp.
Qed.

Hint Resolve subst_context_close_context_wrt_expr : lngen.

Lemma subst_obindd_close_obindd_wrt_expr :
forall ob1 e1 x1 x2,
  lc_expr e1 ->  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_obindd e1 x1 (close_obindd_wrt_expr x2 ob1) = close_obindd_wrt_expr x2 (subst_obindd e1 x1 ob1).
Proof.
unfold close_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve subst_obindd_close_obindd_wrt_expr : lngen.

Lemma subst_dwork_close_dwork_wrt_expr :
forall w1 e1 x1 x2,
  lc_expr e1 ->  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_dwork e1 x1 (close_dwork_wrt_expr x2 w1) = close_dwork_wrt_expr x2 (subst_dwork e1 x1 w1).
Proof.
unfold close_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dwork_close_dwork_wrt_expr : lngen.

Lemma subst_dworklist_close_dworklist_wrt_expr :
forall wl1 e1 x1 x2,
  lc_expr e1 ->  x1 <> x2 ->
  x2 `notin` fv_expr e1 ->
  subst_dworklist e1 x1 (close_dworklist_wrt_expr x2 wl1) = close_dworklist_wrt_expr x2 (subst_dworklist e1 x1 wl1).
Proof.
unfold close_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dworklist_close_dworklist_wrt_expr : lngen.

(* begin hide *)

Lemma subst_expr_degree_expr_wrt_expr_subst_body_degree_body_wrt_expr_mutual :
(forall e1 e2 x1 n1,
  degree_expr_wrt_expr n1 e1 ->
  degree_expr_wrt_expr n1 e2 ->
  degree_expr_wrt_expr n1 (subst_expr e2 x1 e1)) /\
(forall b1 e1 x1 n1,
  degree_body_wrt_expr n1 b1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_body_wrt_expr n1 (subst_body e1 x1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_expr_degree_expr_wrt_expr :
forall e1 e2 x1 n1,
  degree_expr_wrt_expr n1 e1 ->
  degree_expr_wrt_expr n1 e2 ->
  degree_expr_wrt_expr n1 (subst_expr e2 x1 e1).
Proof.
pose proof subst_expr_degree_expr_wrt_expr_subst_body_degree_body_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_expr_degree_expr_wrt_expr : lngen.

Lemma subst_body_degree_body_wrt_expr :
forall b1 e1 x1 n1,
  degree_body_wrt_expr n1 b1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_body_wrt_expr n1 (subst_body e1 x1 b1).
Proof.
pose proof subst_expr_degree_expr_wrt_expr_subst_body_degree_body_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_body_degree_body_wrt_expr : lngen.

(* begin hide *)

Lemma subst_context_degree_context_wrt_expr_mutual :
(forall G1 e1 x1 n1,
  degree_context_wrt_expr n1 G1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_context_wrt_expr n1 (subst_context e1 x1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_context_degree_context_wrt_expr :
forall G1 e1 x1 n1,
  degree_context_wrt_expr n1 G1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_context_wrt_expr n1 (subst_context e1 x1 G1).
Proof.
pose proof subst_context_degree_context_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_context_degree_context_wrt_expr : lngen.

(* begin hide *)

Lemma subst_obindd_degree_obindd_wrt_expr_mutual :
(forall ob1 e1 x1 n1,
  degree_obindd_wrt_expr n1 ob1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_obindd_wrt_expr n1 (subst_obindd e1 x1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obindd_degree_obindd_wrt_expr :
forall ob1 e1 x1 n1,
  degree_obindd_wrt_expr n1 ob1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_obindd_wrt_expr n1 (subst_obindd e1 x1 ob1).
Proof.
pose proof subst_obindd_degree_obindd_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obindd_degree_obindd_wrt_expr : lngen.

(* begin hide *)

Lemma subst_dwork_degree_dwork_wrt_expr_subst_dworklist_degree_dworklist_wrt_expr_mutual :
(forall w1 e1 x1 n1,
  degree_dwork_wrt_expr n1 w1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_dwork_wrt_expr n1 (subst_dwork e1 x1 w1)) /\
(forall wl1 e1 x1 n1,
  degree_dworklist_wrt_expr n1 wl1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_dworklist_wrt_expr n1 (subst_dworklist e1 x1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dwork_degree_dwork_wrt_expr :
forall w1 e1 x1 n1,
  degree_dwork_wrt_expr n1 w1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_dwork_wrt_expr n1 (subst_dwork e1 x1 w1).
Proof.
pose proof subst_dwork_degree_dwork_wrt_expr_subst_dworklist_degree_dworklist_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dwork_degree_dwork_wrt_expr : lngen.

Lemma subst_dworklist_degree_dworklist_wrt_expr :
forall wl1 e1 x1 n1,
  degree_dworklist_wrt_expr n1 wl1 ->
  degree_expr_wrt_expr n1 e1 ->
  degree_dworklist_wrt_expr n1 (subst_dworklist e1 x1 wl1).
Proof.
pose proof subst_dwork_degree_dwork_wrt_expr_subst_dworklist_degree_dworklist_wrt_expr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dworklist_degree_dworklist_wrt_expr : lngen.

(* begin hide *)

Lemma subst_expr_fresh_eq_subst_body_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_expr e2 ->
  subst_expr e1 x1 e2 = e2) /\
(forall b1 e1 x1,
  x1 `notin` fv_body b1 ->
  subst_body e1 x1 b1 = b1).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_expr_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_expr e2 ->
  subst_expr e1 x1 e2 = e2.
Proof.
pose proof subst_expr_fresh_eq_subst_body_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_expr_fresh_eq : lngen.
Hint Rewrite subst_expr_fresh_eq using solve [auto] : lngen.

Lemma subst_body_fresh_eq :
forall b1 e1 x1,
  x1 `notin` fv_body b1 ->
  subst_body e1 x1 b1 = b1.
Proof.
pose proof subst_expr_fresh_eq_subst_body_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_body_fresh_eq : lngen.
Hint Rewrite subst_body_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_context_fresh_eq_mutual :
(forall G1 e1 x1,
  x1 `notin` fv_context G1 ->
  subst_context e1 x1 G1 = G1).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_context_fresh_eq :
forall G1 e1 x1,
  x1 `notin` fv_context G1 ->
  subst_context e1 x1 G1 = G1.
Proof.
pose proof subst_context_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_context_fresh_eq : lngen.
Hint Rewrite subst_context_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_obindd_fresh_eq_mutual :
(forall ob1 e1 x1,
  x1 `notin` fv_obindd ob1 ->
  subst_obindd e1 x1 ob1 = ob1).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obindd_fresh_eq :
forall ob1 e1 x1,
  x1 `notin` fv_obindd ob1 ->
  subst_obindd e1 x1 ob1 = ob1.
Proof.
pose proof subst_obindd_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obindd_fresh_eq : lngen.
Hint Rewrite subst_obindd_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_dwork_fresh_eq_subst_dworklist_fresh_eq_mutual :
(forall w1 e1 x1,
  x1 `notin` fv_dwork w1 ->
  subst_dwork e1 x1 w1 = w1) /\
(forall wl1 e1 x1,
  x1 `notin` fv_dworklist wl1 ->
  subst_dworklist e1 x1 wl1 = wl1).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dwork_fresh_eq :
forall w1 e1 x1,
  x1 `notin` fv_dwork w1 ->
  subst_dwork e1 x1 w1 = w1.
Proof.
pose proof subst_dwork_fresh_eq_subst_dworklist_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dwork_fresh_eq : lngen.
Hint Rewrite subst_dwork_fresh_eq using solve [auto] : lngen.

Lemma subst_dworklist_fresh_eq :
forall wl1 e1 x1,
  x1 `notin` fv_dworklist wl1 ->
  subst_dworklist e1 x1 wl1 = wl1.
Proof.
pose proof subst_dwork_fresh_eq_subst_dworklist_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dworklist_fresh_eq : lngen.
Hint Rewrite subst_dworklist_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_expr_fresh_same_subst_body_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_expr (subst_expr e1 x1 e2)) /\
(forall b1 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_body (subst_body e1 x1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_expr_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_expr (subst_expr e1 x1 e2).
Proof.
pose proof subst_expr_fresh_same_subst_body_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_expr_fresh_same : lngen.

Lemma subst_body_fresh_same :
forall b1 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_body (subst_body e1 x1 b1).
Proof.
pose proof subst_expr_fresh_same_subst_body_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_body_fresh_same : lngen.

(* begin hide *)

Lemma subst_context_fresh_same_mutual :
(forall G1 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_context (subst_context e1 x1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_context_fresh_same :
forall G1 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_context (subst_context e1 x1 G1).
Proof.
pose proof subst_context_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_context_fresh_same : lngen.

(* begin hide *)

Lemma subst_obindd_fresh_same_mutual :
(forall ob1 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_obindd (subst_obindd e1 x1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obindd_fresh_same :
forall ob1 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_obindd (subst_obindd e1 x1 ob1).
Proof.
pose proof subst_obindd_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obindd_fresh_same : lngen.

(* begin hide *)

Lemma subst_dwork_fresh_same_subst_dworklist_fresh_same_mutual :
(forall w1 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_dwork (subst_dwork e1 x1 w1)) /\
(forall wl1 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_dworklist (subst_dworklist e1 x1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dwork_fresh_same :
forall w1 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_dwork (subst_dwork e1 x1 w1).
Proof.
pose proof subst_dwork_fresh_same_subst_dworklist_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dwork_fresh_same : lngen.

Lemma subst_dworklist_fresh_same :
forall wl1 e1 x1,
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_dworklist (subst_dworklist e1 x1 wl1).
Proof.
pose proof subst_dwork_fresh_same_subst_dworklist_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dworklist_fresh_same : lngen.

(* begin hide *)

Lemma subst_expr_fresh_subst_body_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_expr e2 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_expr (subst_expr e1 x2 e2)) /\
(forall b1 e1 x1 x2,
  x1 `notin` fv_body b1 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_body (subst_body e1 x2 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_expr_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_expr e2 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_expr (subst_expr e1 x2 e2).
Proof.
pose proof subst_expr_fresh_subst_body_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_expr_fresh : lngen.

Lemma subst_body_fresh :
forall b1 e1 x1 x2,
  x1 `notin` fv_body b1 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_body (subst_body e1 x2 b1).
Proof.
pose proof subst_expr_fresh_subst_body_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_body_fresh : lngen.

(* begin hide *)

Lemma subst_context_fresh_mutual :
(forall G1 e1 x1 x2,
  x1 `notin` fv_context G1 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_context (subst_context e1 x2 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_context_fresh :
forall G1 e1 x1 x2,
  x1 `notin` fv_context G1 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_context (subst_context e1 x2 G1).
Proof.
pose proof subst_context_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_context_fresh : lngen.

(* begin hide *)

Lemma subst_obindd_fresh_mutual :
(forall ob1 e1 x1 x2,
  x1 `notin` fv_obindd ob1 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_obindd (subst_obindd e1 x2 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obindd_fresh :
forall ob1 e1 x1 x2,
  x1 `notin` fv_obindd ob1 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_obindd (subst_obindd e1 x2 ob1).
Proof.
pose proof subst_obindd_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obindd_fresh : lngen.

(* begin hide *)

Lemma subst_dwork_fresh_subst_dworklist_fresh_mutual :
(forall w1 e1 x1 x2,
  x1 `notin` fv_dwork w1 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_dwork (subst_dwork e1 x2 w1)) /\
(forall wl1 e1 x1 x2,
  x1 `notin` fv_dworklist wl1 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_dworklist (subst_dworklist e1 x2 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dwork_fresh :
forall w1 e1 x1 x2,
  x1 `notin` fv_dwork w1 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_dwork (subst_dwork e1 x2 w1).
Proof.
pose proof subst_dwork_fresh_subst_dworklist_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dwork_fresh : lngen.

Lemma subst_dworklist_fresh :
forall wl1 e1 x1 x2,
  x1 `notin` fv_dworklist wl1 ->
  x1 `notin` fv_expr e1 ->
  x1 `notin` fv_dworklist (subst_dworklist e1 x2 wl1).
Proof.
pose proof subst_dwork_fresh_subst_dworklist_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dworklist_fresh : lngen.

Lemma subst_expr_lc_expr :
forall e1 e2 x1,
  lc_expr e1 ->
  lc_expr e2 ->
  lc_expr (subst_expr e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_expr_lc_expr : lngen.

Lemma subst_body_lc_body :
forall b1 e1 x1,
  lc_body b1 ->
  lc_expr e1 ->
  lc_body (subst_body e1 x1 b1).
Proof.
default_simp.
Qed.

Hint Resolve subst_body_lc_body : lngen.

Lemma subst_context_lc_context :
forall G1 e1 x1,
  lc_context G1 ->
  lc_expr e1 ->
  lc_context (subst_context e1 x1 G1).
Proof.
default_simp.
Qed.

Hint Resolve subst_context_lc_context : lngen.

Lemma subst_obindd_lc_obindd :
forall ob1 e1 x1,
  lc_obindd ob1 ->
  lc_expr e1 ->
  lc_obindd (subst_obindd e1 x1 ob1).
Proof.
default_simp.
Qed.

Hint Resolve subst_obindd_lc_obindd : lngen.

Lemma subst_dwork_lc_dwork :
forall w1 e1 x1,
  lc_dwork w1 ->
  lc_expr e1 ->
  lc_dwork (subst_dwork e1 x1 w1).
Proof.
default_simp.
Qed.

Hint Resolve subst_dwork_lc_dwork : lngen.

Lemma subst_dworklist_lc_dworklist :
forall wl1 e1 x1,
  lc_dworklist wl1 ->
  lc_expr e1 ->
  lc_dworklist (subst_dworklist e1 x1 wl1).
Proof.
default_simp.
Qed.

Hint Resolve subst_dworklist_lc_dworklist : lngen.

(* begin hide *)

Lemma subst_expr_open_expr_wrt_expr_rec_subst_body_open_body_wrt_expr_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_expr e1 x1 (open_expr_wrt_expr_rec n1 e2 e3) = open_expr_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_expr e1 x1 e3)) /\
(forall b1 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_body e1 x1 (open_body_wrt_expr_rec n1 e2 b1) = open_body_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_body e1 x1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_expr_open_expr_wrt_expr_rec :
forall e3 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_expr e1 x1 (open_expr_wrt_expr_rec n1 e2 e3) = open_expr_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_expr e1 x1 e3).
Proof.
pose proof subst_expr_open_expr_wrt_expr_rec_subst_body_open_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_expr_open_expr_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_body_open_body_wrt_expr_rec :
forall b1 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_body e1 x1 (open_body_wrt_expr_rec n1 e2 b1) = open_body_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_body e1 x1 b1).
Proof.
pose proof subst_expr_open_expr_wrt_expr_rec_subst_body_open_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_body_open_body_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_context_open_context_wrt_expr_rec_mutual :
(forall G1 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_context e1 x1 (open_context_wrt_expr_rec n1 e2 G1) = open_context_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_context e1 x1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_context_open_context_wrt_expr_rec :
forall G1 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_context e1 x1 (open_context_wrt_expr_rec n1 e2 G1) = open_context_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_context e1 x1 G1).
Proof.
pose proof subst_context_open_context_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_context_open_context_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_obindd_open_obindd_wrt_expr_rec_mutual :
(forall ob1 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_obindd e1 x1 (open_obindd_wrt_expr_rec n1 e2 ob1) = open_obindd_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_obindd e1 x1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_obindd_open_obindd_wrt_expr_rec :
forall ob1 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_obindd e1 x1 (open_obindd_wrt_expr_rec n1 e2 ob1) = open_obindd_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_obindd e1 x1 ob1).
Proof.
pose proof subst_obindd_open_obindd_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obindd_open_obindd_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dwork_open_dwork_wrt_expr_rec_subst_dworklist_open_dworklist_wrt_expr_rec_mutual :
(forall w1 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_dwork e1 x1 (open_dwork_wrt_expr_rec n1 e2 w1) = open_dwork_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_dwork e1 x1 w1)) /\
(forall wl1 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_dworklist e1 x1 (open_dworklist_wrt_expr_rec n1 e2 wl1) = open_dworklist_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_dworklist e1 x1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dwork_open_dwork_wrt_expr_rec :
forall w1 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_dwork e1 x1 (open_dwork_wrt_expr_rec n1 e2 w1) = open_dwork_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_dwork e1 x1 w1).
Proof.
pose proof subst_dwork_open_dwork_wrt_expr_rec_subst_dworklist_open_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dwork_open_dwork_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dworklist_open_dworklist_wrt_expr_rec :
forall wl1 e1 e2 x1 n1,
  lc_expr e1 ->
  subst_dworklist e1 x1 (open_dworklist_wrt_expr_rec n1 e2 wl1) = open_dworklist_wrt_expr_rec n1 (subst_expr e1 x1 e2) (subst_dworklist e1 x1 wl1).
Proof.
pose proof subst_dwork_open_dwork_wrt_expr_rec_subst_dworklist_open_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dworklist_open_dworklist_wrt_expr_rec : lngen.

(* end hide *)

Lemma subst_expr_open_expr_wrt_expr :
forall e3 e1 e2 x1,
  lc_expr e1 ->
  subst_expr e1 x1 (open_expr_wrt_expr e3 e2) = open_expr_wrt_expr (subst_expr e1 x1 e3) (subst_expr e1 x1 e2).
Proof.
unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve subst_expr_open_expr_wrt_expr : lngen.

Lemma subst_body_open_body_wrt_expr :
forall b1 e1 e2 x1,
  lc_expr e1 ->
  subst_body e1 x1 (open_body_wrt_expr b1 e2) = open_body_wrt_expr (subst_body e1 x1 b1) (subst_expr e1 x1 e2).
Proof.
unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve subst_body_open_body_wrt_expr : lngen.

Lemma subst_context_open_context_wrt_expr :
forall G1 e1 e2 x1,
  lc_expr e1 ->
  subst_context e1 x1 (open_context_wrt_expr G1 e2) = open_context_wrt_expr (subst_context e1 x1 G1) (subst_expr e1 x1 e2).
Proof.
unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve subst_context_open_context_wrt_expr : lngen.

Lemma subst_obindd_open_obindd_wrt_expr :
forall ob1 e1 e2 x1,
  lc_expr e1 ->
  subst_obindd e1 x1 (open_obindd_wrt_expr ob1 e2) = open_obindd_wrt_expr (subst_obindd e1 x1 ob1) (subst_expr e1 x1 e2).
Proof.
unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve subst_obindd_open_obindd_wrt_expr : lngen.

Lemma subst_dwork_open_dwork_wrt_expr :
forall w1 e1 e2 x1,
  lc_expr e1 ->
  subst_dwork e1 x1 (open_dwork_wrt_expr w1 e2) = open_dwork_wrt_expr (subst_dwork e1 x1 w1) (subst_expr e1 x1 e2).
Proof.
unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dwork_open_dwork_wrt_expr : lngen.

Lemma subst_dworklist_open_dworklist_wrt_expr :
forall wl1 e1 e2 x1,
  lc_expr e1 ->
  subst_dworklist e1 x1 (open_dworklist_wrt_expr wl1 e2) = open_dworklist_wrt_expr (subst_dworklist e1 x1 wl1) (subst_expr e1 x1 e2).
Proof.
unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dworklist_open_dworklist_wrt_expr : lngen.

Lemma subst_expr_open_expr_wrt_expr_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_expr e1 ->
  open_expr_wrt_expr (subst_expr e1 x1 e2) (e_var_f x2) = subst_expr e1 x1 (open_expr_wrt_expr e2 (e_var_f x2)).
Proof.
intros; rewrite subst_expr_open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve subst_expr_open_expr_wrt_expr_var : lngen.

Lemma subst_body_open_body_wrt_expr_var :
forall b1 e1 x1 x2,
  x1 <> x2 ->
  lc_expr e1 ->
  open_body_wrt_expr (subst_body e1 x1 b1) (e_var_f x2) = subst_body e1 x1 (open_body_wrt_expr b1 (e_var_f x2)).
Proof.
intros; rewrite subst_body_open_body_wrt_expr; default_simp.
Qed.

Hint Resolve subst_body_open_body_wrt_expr_var : lngen.

Lemma subst_context_open_context_wrt_expr_var :
forall G1 e1 x1 x2,
  x1 <> x2 ->
  lc_expr e1 ->
  open_context_wrt_expr (subst_context e1 x1 G1) (e_var_f x2) = subst_context e1 x1 (open_context_wrt_expr G1 (e_var_f x2)).
Proof.
intros; rewrite subst_context_open_context_wrt_expr; default_simp.
Qed.

Hint Resolve subst_context_open_context_wrt_expr_var : lngen.

Lemma subst_obindd_open_obindd_wrt_expr_var :
forall ob1 e1 x1 x2,
  x1 <> x2 ->
  lc_expr e1 ->
  open_obindd_wrt_expr (subst_obindd e1 x1 ob1) (e_var_f x2) = subst_obindd e1 x1 (open_obindd_wrt_expr ob1 (e_var_f x2)).
Proof.
intros; rewrite subst_obindd_open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve subst_obindd_open_obindd_wrt_expr_var : lngen.

Lemma subst_dwork_open_dwork_wrt_expr_var :
forall w1 e1 x1 x2,
  x1 <> x2 ->
  lc_expr e1 ->
  open_dwork_wrt_expr (subst_dwork e1 x1 w1) (e_var_f x2) = subst_dwork e1 x1 (open_dwork_wrt_expr w1 (e_var_f x2)).
Proof.
intros; rewrite subst_dwork_open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dwork_open_dwork_wrt_expr_var : lngen.

Lemma subst_dworklist_open_dworklist_wrt_expr_var :
forall wl1 e1 x1 x2,
  x1 <> x2 ->
  lc_expr e1 ->
  open_dworklist_wrt_expr (subst_dworklist e1 x1 wl1) (e_var_f x2) = subst_dworklist e1 x1 (open_dworklist_wrt_expr wl1 (e_var_f x2)).
Proof.
intros; rewrite subst_dworklist_open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dworklist_open_dworklist_wrt_expr_var : lngen.

(* begin hide *)

Lemma subst_expr_spec_rec_subst_body_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_expr e2 x1 e1 = open_expr_wrt_expr_rec n1 e2 (close_expr_wrt_expr_rec n1 x1 e1)) /\
(forall b1 e1 x1 n1,
  subst_body e1 x1 b1 = open_body_wrt_expr_rec n1 e1 (close_body_wrt_expr_rec n1 x1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_expr_spec_rec :
forall e1 e2 x1 n1,
  subst_expr e2 x1 e1 = open_expr_wrt_expr_rec n1 e2 (close_expr_wrt_expr_rec n1 x1 e1).
Proof.
pose proof subst_expr_spec_rec_subst_body_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_expr_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_body_spec_rec :
forall b1 e1 x1 n1,
  subst_body e1 x1 b1 = open_body_wrt_expr_rec n1 e1 (close_body_wrt_expr_rec n1 x1 b1).
Proof.
pose proof subst_expr_spec_rec_subst_body_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_body_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_context_spec_rec_mutual :
(forall G1 e1 x1 n1,
  subst_context e1 x1 G1 = open_context_wrt_expr_rec n1 e1 (close_context_wrt_expr_rec n1 x1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_context_spec_rec :
forall G1 e1 x1 n1,
  subst_context e1 x1 G1 = open_context_wrt_expr_rec n1 e1 (close_context_wrt_expr_rec n1 x1 G1).
Proof.
pose proof subst_context_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_context_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_obindd_spec_rec_mutual :
(forall ob1 e1 x1 n1,
  subst_obindd e1 x1 ob1 = open_obindd_wrt_expr_rec n1 e1 (close_obindd_wrt_expr_rec n1 x1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_obindd_spec_rec :
forall ob1 e1 x1 n1,
  subst_obindd e1 x1 ob1 = open_obindd_wrt_expr_rec n1 e1 (close_obindd_wrt_expr_rec n1 x1 ob1).
Proof.
pose proof subst_obindd_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obindd_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dwork_spec_rec_subst_dworklist_spec_rec_mutual :
(forall w1 e1 x1 n1,
  subst_dwork e1 x1 w1 = open_dwork_wrt_expr_rec n1 e1 (close_dwork_wrt_expr_rec n1 x1 w1)) /\
(forall wl1 e1 x1 n1,
  subst_dworklist e1 x1 wl1 = open_dworklist_wrt_expr_rec n1 e1 (close_dworklist_wrt_expr_rec n1 x1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dwork_spec_rec :
forall w1 e1 x1 n1,
  subst_dwork e1 x1 w1 = open_dwork_wrt_expr_rec n1 e1 (close_dwork_wrt_expr_rec n1 x1 w1).
Proof.
pose proof subst_dwork_spec_rec_subst_dworklist_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dwork_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dworklist_spec_rec :
forall wl1 e1 x1 n1,
  subst_dworklist e1 x1 wl1 = open_dworklist_wrt_expr_rec n1 e1 (close_dworklist_wrt_expr_rec n1 x1 wl1).
Proof.
pose proof subst_dwork_spec_rec_subst_dworklist_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dworklist_spec_rec : lngen.

(* end hide *)

Lemma subst_expr_spec :
forall e1 e2 x1,
  subst_expr e2 x1 e1 = open_expr_wrt_expr (close_expr_wrt_expr x1 e1) e2.
Proof.
unfold close_expr_wrt_expr; unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve subst_expr_spec : lngen.

Lemma subst_body_spec :
forall b1 e1 x1,
  subst_body e1 x1 b1 = open_body_wrt_expr (close_body_wrt_expr x1 b1) e1.
Proof.
unfold close_body_wrt_expr; unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve subst_body_spec : lngen.

Lemma subst_context_spec :
forall G1 e1 x1,
  subst_context e1 x1 G1 = open_context_wrt_expr (close_context_wrt_expr x1 G1) e1.
Proof.
unfold close_context_wrt_expr; unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve subst_context_spec : lngen.

Lemma subst_obindd_spec :
forall ob1 e1 x1,
  subst_obindd e1 x1 ob1 = open_obindd_wrt_expr (close_obindd_wrt_expr x1 ob1) e1.
Proof.
unfold close_obindd_wrt_expr; unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve subst_obindd_spec : lngen.

Lemma subst_dwork_spec :
forall w1 e1 x1,
  subst_dwork e1 x1 w1 = open_dwork_wrt_expr (close_dwork_wrt_expr x1 w1) e1.
Proof.
unfold close_dwork_wrt_expr; unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dwork_spec : lngen.

Lemma subst_dworklist_spec :
forall wl1 e1 x1,
  subst_dworklist e1 x1 wl1 = open_dworklist_wrt_expr (close_dworklist_wrt_expr x1 wl1) e1.
Proof.
unfold close_dworklist_wrt_expr; unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dworklist_spec : lngen.

(* begin hide *)

Lemma subst_expr_subst_expr_subst_body_subst_body_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_expr e2 ->
  x2 <> x1 ->
  subst_expr e2 x1 (subst_expr e3 x2 e1) = subst_expr (subst_expr e2 x1 e3) x2 (subst_expr e2 x1 e1)) /\
(forall b1 e1 e2 x2 x1,
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  subst_body e1 x1 (subst_body e2 x2 b1) = subst_body (subst_expr e1 x1 e2) x2 (subst_body e1 x1 b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_expr_subst_expr :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_expr e2 ->
  x2 <> x1 ->
  subst_expr e2 x1 (subst_expr e3 x2 e1) = subst_expr (subst_expr e2 x1 e3) x2 (subst_expr e2 x1 e1).
Proof.
pose proof subst_expr_subst_expr_subst_body_subst_body_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_expr_subst_expr : lngen.

Lemma subst_body_subst_body :
forall b1 e1 e2 x2 x1,
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  subst_body e1 x1 (subst_body e2 x2 b1) = subst_body (subst_expr e1 x1 e2) x2 (subst_body e1 x1 b1).
Proof.
pose proof subst_expr_subst_expr_subst_body_subst_body_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_body_subst_body : lngen.

(* begin hide *)

Lemma subst_context_subst_context_mutual :
(forall G1 e1 e2 x2 x1,
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  subst_context e1 x1 (subst_context e2 x2 G1) = subst_context (subst_expr e1 x1 e2) x2 (subst_context e1 x1 G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_context_subst_context :
forall G1 e1 e2 x2 x1,
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  subst_context e1 x1 (subst_context e2 x2 G1) = subst_context (subst_expr e1 x1 e2) x2 (subst_context e1 x1 G1).
Proof.
pose proof subst_context_subst_context_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_context_subst_context : lngen.

(* begin hide *)

Lemma subst_obindd_subst_obindd_mutual :
(forall ob1 e1 e2 x2 x1,
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  subst_obindd e1 x1 (subst_obindd e2 x2 ob1) = subst_obindd (subst_expr e1 x1 e2) x2 (subst_obindd e1 x1 ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obindd_subst_obindd :
forall ob1 e1 e2 x2 x1,
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  subst_obindd e1 x1 (subst_obindd e2 x2 ob1) = subst_obindd (subst_expr e1 x1 e2) x2 (subst_obindd e1 x1 ob1).
Proof.
pose proof subst_obindd_subst_obindd_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obindd_subst_obindd : lngen.

(* begin hide *)

Lemma subst_dwork_subst_dwork_subst_dworklist_subst_dworklist_mutual :
(forall w1 e1 e2 x2 x1,
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  subst_dwork e1 x1 (subst_dwork e2 x2 w1) = subst_dwork (subst_expr e1 x1 e2) x2 (subst_dwork e1 x1 w1)) /\
(forall wl1 e1 e2 x2 x1,
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  subst_dworklist e1 x1 (subst_dworklist e2 x2 wl1) = subst_dworklist (subst_expr e1 x1 e2) x2 (subst_dworklist e1 x1 wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dwork_subst_dwork :
forall w1 e1 e2 x2 x1,
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  subst_dwork e1 x1 (subst_dwork e2 x2 w1) = subst_dwork (subst_expr e1 x1 e2) x2 (subst_dwork e1 x1 w1).
Proof.
pose proof subst_dwork_subst_dwork_subst_dworklist_subst_dworklist_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dwork_subst_dwork : lngen.

Lemma subst_dworklist_subst_dworklist :
forall wl1 e1 e2 x2 x1,
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  subst_dworklist e1 x1 (subst_dworklist e2 x2 wl1) = subst_dworklist (subst_expr e1 x1 e2) x2 (subst_dworklist e1 x1 wl1).
Proof.
pose proof subst_dwork_subst_dwork_subst_dworklist_subst_dworklist_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dworklist_subst_dworklist : lngen.

(* begin hide *)

Lemma subst_expr_close_expr_wrt_expr_rec_open_expr_wrt_expr_rec_subst_body_close_body_wrt_expr_rec_open_body_wrt_expr_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_expr e2 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_expr e1 x1 e2 = close_expr_wrt_expr_rec n1 x2 (subst_expr e1 x1 (open_expr_wrt_expr_rec n1 (e_var_f x2) e2))) *
(forall b1 e1 x1 x2 n1,
  x2 `notin` fv_body b1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_body e1 x1 b1 = close_body_wrt_expr_rec n1 x2 (subst_body e1 x1 (open_body_wrt_expr_rec n1 (e_var_f x2) b1))).
Proof.
apply_mutual_ind expr_body_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_expr_close_expr_wrt_expr_rec_open_expr_wrt_expr_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_expr e2 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_expr e1 x1 e2 = close_expr_wrt_expr_rec n1 x2 (subst_expr e1 x1 (open_expr_wrt_expr_rec n1 (e_var_f x2) e2)).
Proof.
pose proof subst_expr_close_expr_wrt_expr_rec_open_expr_wrt_expr_rec_subst_body_close_body_wrt_expr_rec_open_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_expr_close_expr_wrt_expr_rec_open_expr_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_body_close_body_wrt_expr_rec_open_body_wrt_expr_rec :
forall b1 e1 x1 x2 n1,
  x2 `notin` fv_body b1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_body e1 x1 b1 = close_body_wrt_expr_rec n1 x2 (subst_body e1 x1 (open_body_wrt_expr_rec n1 (e_var_f x2) b1)).
Proof.
pose proof subst_expr_close_expr_wrt_expr_rec_open_expr_wrt_expr_rec_subst_body_close_body_wrt_expr_rec_open_body_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_body_close_body_wrt_expr_rec_open_body_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_context_close_context_wrt_expr_rec_open_context_wrt_expr_rec_mutual :
(forall G1 e1 x1 x2 n1,
  x2 `notin` fv_context G1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_context e1 x1 G1 = close_context_wrt_expr_rec n1 x2 (subst_context e1 x1 (open_context_wrt_expr_rec n1 (e_var_f x2) G1))).
Proof.
apply_mutual_ind context_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_context_close_context_wrt_expr_rec_open_context_wrt_expr_rec :
forall G1 e1 x1 x2 n1,
  x2 `notin` fv_context G1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_context e1 x1 G1 = close_context_wrt_expr_rec n1 x2 (subst_context e1 x1 (open_context_wrt_expr_rec n1 (e_var_f x2) G1)).
Proof.
pose proof subst_context_close_context_wrt_expr_rec_open_context_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_context_close_context_wrt_expr_rec_open_context_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_obindd_close_obindd_wrt_expr_rec_open_obindd_wrt_expr_rec_mutual :
(forall ob1 e1 x1 x2 n1,
  x2 `notin` fv_obindd ob1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_obindd e1 x1 ob1 = close_obindd_wrt_expr_rec n1 x2 (subst_obindd e1 x1 (open_obindd_wrt_expr_rec n1 (e_var_f x2) ob1))).
Proof.
apply_mutual_ind obindd_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_obindd_close_obindd_wrt_expr_rec_open_obindd_wrt_expr_rec :
forall ob1 e1 x1 x2 n1,
  x2 `notin` fv_obindd ob1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_obindd e1 x1 ob1 = close_obindd_wrt_expr_rec n1 x2 (subst_obindd e1 x1 (open_obindd_wrt_expr_rec n1 (e_var_f x2) ob1)).
Proof.
pose proof subst_obindd_close_obindd_wrt_expr_rec_open_obindd_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obindd_close_obindd_wrt_expr_rec_open_obindd_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dwork_close_dwork_wrt_expr_rec_open_dwork_wrt_expr_rec_subst_dworklist_close_dworklist_wrt_expr_rec_open_dworklist_wrt_expr_rec_mutual :
(forall w1 e1 x1 x2 n1,
  x2 `notin` fv_dwork w1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_dwork e1 x1 w1 = close_dwork_wrt_expr_rec n1 x2 (subst_dwork e1 x1 (open_dwork_wrt_expr_rec n1 (e_var_f x2) w1))) *
(forall wl1 e1 x1 x2 n1,
  x2 `notin` fv_dworklist wl1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_dworklist e1 x1 wl1 = close_dworklist_wrt_expr_rec n1 x2 (subst_dworklist e1 x1 (open_dworklist_wrt_expr_rec n1 (e_var_f x2) wl1))).
Proof.
apply_mutual_ind dwork_dworklist_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dwork_close_dwork_wrt_expr_rec_open_dwork_wrt_expr_rec :
forall w1 e1 x1 x2 n1,
  x2 `notin` fv_dwork w1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_dwork e1 x1 w1 = close_dwork_wrt_expr_rec n1 x2 (subst_dwork e1 x1 (open_dwork_wrt_expr_rec n1 (e_var_f x2) w1)).
Proof.
pose proof subst_dwork_close_dwork_wrt_expr_rec_open_dwork_wrt_expr_rec_subst_dworklist_close_dworklist_wrt_expr_rec_open_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dwork_close_dwork_wrt_expr_rec_open_dwork_wrt_expr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dworklist_close_dworklist_wrt_expr_rec_open_dworklist_wrt_expr_rec :
forall wl1 e1 x1 x2 n1,
  x2 `notin` fv_dworklist wl1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  degree_expr_wrt_expr n1 e1 ->
  subst_dworklist e1 x1 wl1 = close_dworklist_wrt_expr_rec n1 x2 (subst_dworklist e1 x1 (open_dworklist_wrt_expr_rec n1 (e_var_f x2) wl1)).
Proof.
pose proof subst_dwork_close_dwork_wrt_expr_rec_open_dwork_wrt_expr_rec_subst_dworklist_close_dworklist_wrt_expr_rec_open_dworklist_wrt_expr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dworklist_close_dworklist_wrt_expr_rec_open_dworklist_wrt_expr_rec : lngen.

(* end hide *)

Lemma subst_expr_close_expr_wrt_expr_open_expr_wrt_expr :
forall e2 e1 x1 x2,
  x2 `notin` fv_expr e2 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  lc_expr e1 ->
  subst_expr e1 x1 e2 = close_expr_wrt_expr x2 (subst_expr e1 x1 (open_expr_wrt_expr e2 (e_var_f x2))).
Proof.
unfold close_expr_wrt_expr; unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve subst_expr_close_expr_wrt_expr_open_expr_wrt_expr : lngen.

Lemma subst_body_close_body_wrt_expr_open_body_wrt_expr :
forall b1 e1 x1 x2,
  x2 `notin` fv_body b1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  lc_expr e1 ->
  subst_body e1 x1 b1 = close_body_wrt_expr x2 (subst_body e1 x1 (open_body_wrt_expr b1 (e_var_f x2))).
Proof.
unfold close_body_wrt_expr; unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve subst_body_close_body_wrt_expr_open_body_wrt_expr : lngen.

Lemma subst_context_close_context_wrt_expr_open_context_wrt_expr :
forall G1 e1 x1 x2,
  x2 `notin` fv_context G1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  lc_expr e1 ->
  subst_context e1 x1 G1 = close_context_wrt_expr x2 (subst_context e1 x1 (open_context_wrt_expr G1 (e_var_f x2))).
Proof.
unfold close_context_wrt_expr; unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve subst_context_close_context_wrt_expr_open_context_wrt_expr : lngen.

Lemma subst_obindd_close_obindd_wrt_expr_open_obindd_wrt_expr :
forall ob1 e1 x1 x2,
  x2 `notin` fv_obindd ob1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  lc_expr e1 ->
  subst_obindd e1 x1 ob1 = close_obindd_wrt_expr x2 (subst_obindd e1 x1 (open_obindd_wrt_expr ob1 (e_var_f x2))).
Proof.
unfold close_obindd_wrt_expr; unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve subst_obindd_close_obindd_wrt_expr_open_obindd_wrt_expr : lngen.

Lemma subst_dwork_close_dwork_wrt_expr_open_dwork_wrt_expr :
forall w1 e1 x1 x2,
  x2 `notin` fv_dwork w1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  lc_expr e1 ->
  subst_dwork e1 x1 w1 = close_dwork_wrt_expr x2 (subst_dwork e1 x1 (open_dwork_wrt_expr w1 (e_var_f x2))).
Proof.
unfold close_dwork_wrt_expr; unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dwork_close_dwork_wrt_expr_open_dwork_wrt_expr : lngen.

Lemma subst_dworklist_close_dworklist_wrt_expr_open_dworklist_wrt_expr :
forall wl1 e1 x1 x2,
  x2 `notin` fv_dworklist wl1 ->
  x2 `notin` fv_expr e1 ->
  x2 <> x1 ->
  lc_expr e1 ->
  subst_dworklist e1 x1 wl1 = close_dworklist_wrt_expr x2 (subst_dworklist e1 x1 (open_dworklist_wrt_expr wl1 (e_var_f x2))).
Proof.
unfold close_dworklist_wrt_expr; unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dworklist_close_dworklist_wrt_expr_open_dworklist_wrt_expr : lngen.

Lemma subst_expr_e_abs :
forall x2 A1 b1 e1 x1,
  lc_expr e1 ->
  x2 `notin` fv_expr e1 `union` fv_body b1 `union` singleton x1 ->
  subst_expr e1 x1 (e_abs A1 b1) = e_abs (subst_expr e1 x1 A1) (close_body_wrt_expr x2 (subst_body e1 x1 (open_body_wrt_expr b1 (e_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_expr_e_abs : lngen.

Lemma subst_expr_e_pi :
forall x2 A1 B1 e1 x1,
  lc_expr e1 ->
  x2 `notin` fv_expr e1 `union` fv_expr B1 `union` singleton x1 ->
  subst_expr e1 x1 (e_pi A1 B1) = e_pi (subst_expr e1 x1 A1) (close_expr_wrt_expr x2 (subst_expr e1 x1 (open_expr_wrt_expr B1 (e_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_expr_e_pi : lngen.

Lemma subst_expr_e_bind :
forall x2 A1 b1 e1 x1,
  lc_expr e1 ->
  x2 `notin` fv_expr e1 `union` fv_body b1 `union` singleton x1 ->
  subst_expr e1 x1 (e_bind A1 b1) = e_bind (subst_expr e1 x1 A1) (close_body_wrt_expr x2 (subst_body e1 x1 (open_body_wrt_expr b1 (e_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_expr_e_bind : lngen.

Lemma subst_expr_e_all :
forall x2 A1 B1 e1 x1,
  lc_expr e1 ->
  x2 `notin` fv_expr e1 `union` fv_expr B1 `union` singleton x1 ->
  subst_expr e1 x1 (e_all A1 B1) = e_all (subst_expr e1 x1 A1) (close_expr_wrt_expr x2 (subst_expr e1 x1 (open_expr_wrt_expr B1 (e_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_expr_e_all : lngen.

Lemma subst_dwork_dw_infer :
forall x2 e2 e3 wl1 e1 x1,
  lc_expr e1 ->
  x2 `notin` fv_expr e1 `union` fv_dworklist wl1 `union` singleton x1 ->
  subst_dwork e1 x1 (dw_infer e2 e3 wl1) = dw_infer (subst_expr e1 x1 e2) (subst_expr e1 x1 e3) (close_dworklist_wrt_expr x2 (subst_dworklist e1 x1 (open_dworklist_wrt_expr wl1 (e_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_dwork_dw_infer : lngen.

Lemma subst_dwork_dw_infer_app :
forall x2 A1 e2 e3 wl1 e1 x1,
  lc_expr e1 ->
  x2 `notin` fv_expr e1 `union` fv_dworklist wl1 `union` singleton x1 ->
  subst_dwork e1 x1 (dw_infer_app A1 e2 e3 wl1) = dw_infer_app (subst_expr e1 x1 A1) (subst_expr e1 x1 e2) (subst_expr e1 x1 e3) (close_dworklist_wrt_expr x2 (subst_dworklist e1 x1 (open_dworklist_wrt_expr wl1 (e_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_dwork_dw_infer_app : lngen.

Lemma subst_dwork_dw_reduce :
forall x2 e2 wl1 e1 x1,
  lc_expr e1 ->
  x2 `notin` fv_expr e1 `union` fv_dworklist wl1 `union` singleton x1 ->
  subst_dwork e1 x1 (dw_reduce e2 wl1) = dw_reduce (subst_expr e1 x1 e2) (close_dworklist_wrt_expr x2 (subst_dworklist e1 x1 (open_dworklist_wrt_expr wl1 (e_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_dwork_dw_reduce : lngen.

(* begin hide *)

Lemma subst_expr_intro_rec_subst_body_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_expr e1 ->
  open_expr_wrt_expr_rec n1 e2 e1 = subst_expr e2 x1 (open_expr_wrt_expr_rec n1 (e_var_f x1) e1)) /\
(forall b1 x1 e1 n1,
  x1 `notin` fv_body b1 ->
  open_body_wrt_expr_rec n1 e1 b1 = subst_body e1 x1 (open_body_wrt_expr_rec n1 (e_var_f x1) b1)).
Proof.
apply_mutual_ind expr_body_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_expr_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_expr e1 ->
  open_expr_wrt_expr_rec n1 e2 e1 = subst_expr e2 x1 (open_expr_wrt_expr_rec n1 (e_var_f x1) e1).
Proof.
pose proof subst_expr_intro_rec_subst_body_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_expr_intro_rec : lngen.
Hint Rewrite subst_expr_intro_rec using solve [auto] : lngen.

Lemma subst_body_intro_rec :
forall b1 x1 e1 n1,
  x1 `notin` fv_body b1 ->
  open_body_wrt_expr_rec n1 e1 b1 = subst_body e1 x1 (open_body_wrt_expr_rec n1 (e_var_f x1) b1).
Proof.
pose proof subst_expr_intro_rec_subst_body_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_body_intro_rec : lngen.
Hint Rewrite subst_body_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_context_intro_rec_mutual :
(forall G1 x1 e1 n1,
  x1 `notin` fv_context G1 ->
  open_context_wrt_expr_rec n1 e1 G1 = subst_context e1 x1 (open_context_wrt_expr_rec n1 (e_var_f x1) G1)).
Proof.
apply_mutual_ind context_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_context_intro_rec :
forall G1 x1 e1 n1,
  x1 `notin` fv_context G1 ->
  open_context_wrt_expr_rec n1 e1 G1 = subst_context e1 x1 (open_context_wrt_expr_rec n1 (e_var_f x1) G1).
Proof.
pose proof subst_context_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_context_intro_rec : lngen.
Hint Rewrite subst_context_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_obindd_intro_rec_mutual :
(forall ob1 x1 e1 n1,
  x1 `notin` fv_obindd ob1 ->
  open_obindd_wrt_expr_rec n1 e1 ob1 = subst_obindd e1 x1 (open_obindd_wrt_expr_rec n1 (e_var_f x1) ob1)).
Proof.
apply_mutual_ind obindd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obindd_intro_rec :
forall ob1 x1 e1 n1,
  x1 `notin` fv_obindd ob1 ->
  open_obindd_wrt_expr_rec n1 e1 ob1 = subst_obindd e1 x1 (open_obindd_wrt_expr_rec n1 (e_var_f x1) ob1).
Proof.
pose proof subst_obindd_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obindd_intro_rec : lngen.
Hint Rewrite subst_obindd_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_dwork_intro_rec_subst_dworklist_intro_rec_mutual :
(forall w1 x1 e1 n1,
  x1 `notin` fv_dwork w1 ->
  open_dwork_wrt_expr_rec n1 e1 w1 = subst_dwork e1 x1 (open_dwork_wrt_expr_rec n1 (e_var_f x1) w1)) /\
(forall wl1 x1 e1 n1,
  x1 `notin` fv_dworklist wl1 ->
  open_dworklist_wrt_expr_rec n1 e1 wl1 = subst_dworklist e1 x1 (open_dworklist_wrt_expr_rec n1 (e_var_f x1) wl1)).
Proof.
apply_mutual_ind dwork_dworklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dwork_intro_rec :
forall w1 x1 e1 n1,
  x1 `notin` fv_dwork w1 ->
  open_dwork_wrt_expr_rec n1 e1 w1 = subst_dwork e1 x1 (open_dwork_wrt_expr_rec n1 (e_var_f x1) w1).
Proof.
pose proof subst_dwork_intro_rec_subst_dworklist_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dwork_intro_rec : lngen.
Hint Rewrite subst_dwork_intro_rec using solve [auto] : lngen.

Lemma subst_dworklist_intro_rec :
forall wl1 x1 e1 n1,
  x1 `notin` fv_dworklist wl1 ->
  open_dworklist_wrt_expr_rec n1 e1 wl1 = subst_dworklist e1 x1 (open_dworklist_wrt_expr_rec n1 (e_var_f x1) wl1).
Proof.
pose proof subst_dwork_intro_rec_subst_dworklist_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dworklist_intro_rec : lngen.
Hint Rewrite subst_dworklist_intro_rec using solve [auto] : lngen.

Lemma subst_expr_intro :
forall x1 e1 e2,
  x1 `notin` fv_expr e1 ->
  open_expr_wrt_expr e1 e2 = subst_expr e2 x1 (open_expr_wrt_expr e1 (e_var_f x1)).
Proof.
unfold open_expr_wrt_expr; default_simp.
Qed.

Hint Resolve subst_expr_intro : lngen.

Lemma subst_body_intro :
forall x1 b1 e1,
  x1 `notin` fv_body b1 ->
  open_body_wrt_expr b1 e1 = subst_body e1 x1 (open_body_wrt_expr b1 (e_var_f x1)).
Proof.
unfold open_body_wrt_expr; default_simp.
Qed.

Hint Resolve subst_body_intro : lngen.

Lemma subst_context_intro :
forall x1 G1 e1,
  x1 `notin` fv_context G1 ->
  open_context_wrt_expr G1 e1 = subst_context e1 x1 (open_context_wrt_expr G1 (e_var_f x1)).
Proof.
unfold open_context_wrt_expr; default_simp.
Qed.

Hint Resolve subst_context_intro : lngen.

Lemma subst_obindd_intro :
forall x1 ob1 e1,
  x1 `notin` fv_obindd ob1 ->
  open_obindd_wrt_expr ob1 e1 = subst_obindd e1 x1 (open_obindd_wrt_expr ob1 (e_var_f x1)).
Proof.
unfold open_obindd_wrt_expr; default_simp.
Qed.

Hint Resolve subst_obindd_intro : lngen.

Lemma subst_dwork_intro :
forall x1 w1 e1,
  x1 `notin` fv_dwork w1 ->
  open_dwork_wrt_expr w1 e1 = subst_dwork e1 x1 (open_dwork_wrt_expr w1 (e_var_f x1)).
Proof.
unfold open_dwork_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dwork_intro : lngen.

Lemma subst_dworklist_intro :
forall x1 wl1 e1,
  x1 `notin` fv_dworklist wl1 ->
  open_dworklist_wrt_expr wl1 e1 = subst_dworklist e1 x1 (open_dworklist_wrt_expr wl1 (e_var_f x1)).
Proof.
unfold open_dworklist_wrt_expr; default_simp.
Qed.

Hint Resolve subst_dworklist_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
