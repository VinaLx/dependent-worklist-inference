Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export alg_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme akind_ind' := Induction for akind Sort Prop.

Definition akind_mutind :=
  fun H1 H2 H3 H4 =>
  akind_ind' H1 H2 H3 H4.

Scheme akind_rec' := Induction for akind Sort Set.

Definition akind_mutrec :=
  fun H1 H2 H3 H4 =>
  akind_rec' H1 H2 H3 H4.

Scheme aexpr_ind' := Induction for aexpr Sort Prop
  with abody_ind' := Induction for abody Sort Prop.

Definition aexpr_abody_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 =>
  (conj (aexpr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)
  (abody_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)).

Scheme aexpr_rec' := Induction for aexpr Sort Set
  with abody_rec' := Induction for abody Sort Set.

Definition aexpr_abody_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 =>
  (pair (aexpr_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)
  (abody_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)).

Scheme binding_ind' := Induction for binding Sort Prop.

Definition binding_mutind :=
  fun H1 H2 H3 H4 =>
  binding_ind' H1 H2 H3 H4.

Scheme binding_rec' := Induction for binding Sort Set.

Definition binding_mutrec :=
  fun H1 H2 H3 H4 =>
  binding_rec' H1 H2 H3 H4.

Scheme obind_ind' := Induction for obind Sort Prop.

Definition obind_mutind :=
  fun H1 H2 H3 =>
  obind_ind' H1 H2 H3.

Scheme obind_rec' := Induction for obind Sort Set.

Definition obind_mutrec :=
  fun H1 H2 H3 =>
  obind_rec' H1 H2 H3.

Scheme work_ind' := Induction for work Sort Prop
  with worklist_ind' := Induction for worklist Sort Prop.

Definition work_worklist_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (conj (work_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (worklist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Scheme work_rec' := Induction for work Sort Set
  with worklist_rec' := Induction for worklist Sort Set.

Definition work_worklist_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (pair (work_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (worklist_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_aexpr_wrt_aexpr_rec (n1 : nat) (x1 : aexprvar) (e1 : aexpr) {struct e1} : aexpr :=
  match e1 with
    | ae_var_f x2 => if (x1 == x2) then (ae_var_b n1) else (ae_var_f x2)
    | ae_var_b n2 => if (lt_ge_dec n2 n1) then (ae_var_b n2) else (ae_var_b (S n2))
    | ae_kind k1 => ae_kind k1
    | ae_ex ex1 => ae_ex ex1
    | ae_num n2 => ae_num n2
    | ae_int => ae_int
    | ae_bot A1 => ae_bot (close_aexpr_wrt_aexpr_rec n1 x1 A1)
    | ae_app e2 e3 => ae_app (close_aexpr_wrt_aexpr_rec n1 x1 e2) (close_aexpr_wrt_aexpr_rec n1 x1 e3)
    | ae_abs A1 ab1 => ae_abs (close_aexpr_wrt_aexpr_rec n1 x1 A1) (close_abody_wrt_aexpr_rec (S n1) x1 ab1)
    | ae_pi A1 B1 => ae_pi (close_aexpr_wrt_aexpr_rec n1 x1 A1) (close_aexpr_wrt_aexpr_rec (S n1) x1 B1)
    | ae_bind A1 ab1 => ae_bind (close_aexpr_wrt_aexpr_rec n1 x1 A1) (close_abody_wrt_aexpr_rec (S n1) x1 ab1)
    | ae_all A1 B1 => ae_all (close_aexpr_wrt_aexpr_rec n1 x1 A1) (close_aexpr_wrt_aexpr_rec (S n1) x1 B1)
    | ae_castup A1 e2 => ae_castup (close_aexpr_wrt_aexpr_rec n1 x1 A1) (close_aexpr_wrt_aexpr_rec n1 x1 e2)
    | ae_castdn e2 => ae_castdn (close_aexpr_wrt_aexpr_rec n1 x1 e2)
  end

with close_abody_wrt_aexpr_rec (n1 : nat) (x1 : aexprvar) (ab1 : abody) {struct ab1} : abody :=
  match ab1 with
    | ab_anno e1 A1 => ab_anno (close_aexpr_wrt_aexpr_rec n1 x1 e1) (close_aexpr_wrt_aexpr_rec n1 x1 A1)
  end.

Definition close_aexpr_wrt_aexpr x1 e1 := close_aexpr_wrt_aexpr_rec 0 x1 e1.

Definition close_abody_wrt_aexpr x1 ab1 := close_abody_wrt_aexpr_rec 0 x1 ab1.

Fixpoint close_binding_wrt_aexpr_rec (n1 : nat) (x1 : aexprvar) (b1 : binding) {struct b1} : binding :=
  match b1 with
    | b_var x2 A1 => b_var x2 (close_aexpr_wrt_aexpr_rec n1 x1 A1)
    | b_ex ex1 A1 => b_ex ex1 (close_aexpr_wrt_aexpr_rec n1 x1 A1)
    | b_kind kx1 => b_kind kx1
  end.

Definition close_binding_wrt_aexpr x1 b1 := close_binding_wrt_aexpr_rec 0 x1 b1.

Fixpoint close_obind_wrt_aexpr_rec (n1 : nat) (x1 : aexprvar) (ob1 : obind) {struct ob1} : obind :=
  match ob1 with
    | ob_none => ob_none
    | ob_bind x2 A1 => ob_bind x2 (close_aexpr_wrt_aexpr_rec n1 x1 A1)
  end.

Definition close_obind_wrt_aexpr x1 ob1 := close_obind_wrt_aexpr_rec 0 x1 ob1.

Fixpoint close_work_wrt_aexpr_rec (n1 : nat) (x1 : aexprvar) (w1 : work) {struct w1} : work :=
  match w1 with
    | w_check ob1 e1 e2 A1 => w_check (close_obind_wrt_aexpr_rec n1 x1 ob1) (close_aexpr_wrt_aexpr_rec n1 x1 e1) (close_aexpr_wrt_aexpr_rec n1 x1 e2) (close_aexpr_wrt_aexpr_rec n1 x1 A1)
    | w_infer e1 e2 wl1 => w_infer (close_aexpr_wrt_aexpr_rec n1 x1 e1) (close_aexpr_wrt_aexpr_rec n1 x1 e2) (close_worklist_wrt_aexpr_rec (S n1) x1 wl1)
    | w_infer_app A1 e1 e2 wl1 => w_infer_app (close_aexpr_wrt_aexpr_rec n1 x1 A1) (close_aexpr_wrt_aexpr_rec n1 x1 e1) (close_aexpr_wrt_aexpr_rec n1 x1 e2) (close_worklist_wrt_aexpr_rec (S n1) x1 wl1)
    | w_reduce e1 wl1 => w_reduce (close_aexpr_wrt_aexpr_rec n1 x1 e1) (close_worklist_wrt_aexpr_rec (S n1) x1 wl1)
    | w_compact A1 B1 => w_compact (close_aexpr_wrt_aexpr_rec n1 x1 A1) (close_aexpr_wrt_aexpr_rec n1 x1 B1)
  end

with close_worklist_wrt_aexpr_rec (n1 : nat) (x1 : aexprvar) (wl1 : worklist) {struct wl1} : worklist :=
  match wl1 with
    | wl_nil => wl_nil
    | wl_cons wl2 w1 => wl_cons (close_worklist_wrt_aexpr_rec n1 x1 wl2) (close_work_wrt_aexpr_rec n1 x1 w1)
    | wl_bind wl2 b1 => wl_bind (close_worklist_wrt_aexpr_rec n1 x1 wl2) (close_binding_wrt_aexpr_rec n1 x1 b1)
  end.

Definition close_work_wrt_aexpr x1 w1 := close_work_wrt_aexpr_rec 0 x1 w1.

Definition close_worklist_wrt_aexpr x1 wl1 := close_worklist_wrt_aexpr_rec 0 x1 wl1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_akind (k1 : akind) {struct k1} : nat :=
  match k1 with
    | ak_star => 1
    | ak_box => 1
    | ak_ex kx1 => 1
  end.

Fixpoint size_aexpr (e1 : aexpr) {struct e1} : nat :=
  match e1 with
    | ae_var_f x1 => 1
    | ae_var_b n1 => 1
    | ae_kind k1 => 1 + (size_akind k1)
    | ae_ex ex1 => 1
    | ae_num n1 => 1
    | ae_int => 1
    | ae_bot A1 => 1 + (size_aexpr A1)
    | ae_app e2 e3 => 1 + (size_aexpr e2) + (size_aexpr e3)
    | ae_abs A1 ab1 => 1 + (size_aexpr A1) + (size_abody ab1)
    | ae_pi A1 B1 => 1 + (size_aexpr A1) + (size_aexpr B1)
    | ae_bind A1 ab1 => 1 + (size_aexpr A1) + (size_abody ab1)
    | ae_all A1 B1 => 1 + (size_aexpr A1) + (size_aexpr B1)
    | ae_castup A1 e2 => 1 + (size_aexpr A1) + (size_aexpr e2)
    | ae_castdn e2 => 1 + (size_aexpr e2)
  end

with size_abody (ab1 : abody) {struct ab1} : nat :=
  match ab1 with
    | ab_anno e1 A1 => 1 + (size_aexpr e1) + (size_aexpr A1)
  end.

Fixpoint size_binding (b1 : binding) {struct b1} : nat :=
  match b1 with
    | b_var x1 A1 => 1 + (size_aexpr A1)
    | b_ex ex1 A1 => 1 + (size_aexpr A1)
    | b_kind kx1 => 1
  end.

Fixpoint size_obind (ob1 : obind) {struct ob1} : nat :=
  match ob1 with
    | ob_none => 1
    | ob_bind x1 A1 => 1 + (size_aexpr A1)
  end.

Fixpoint size_work (w1 : work) {struct w1} : nat :=
  match w1 with
    | w_check ob1 e1 e2 A1 => 1 + (size_obind ob1) + (size_aexpr e1) + (size_aexpr e2) + (size_aexpr A1)
    | w_infer e1 e2 wl1 => 1 + (size_aexpr e1) + (size_aexpr e2) + (size_worklist wl1)
    | w_infer_app A1 e1 e2 wl1 => 1 + (size_aexpr A1) + (size_aexpr e1) + (size_aexpr e2) + (size_worklist wl1)
    | w_reduce e1 wl1 => 1 + (size_aexpr e1) + (size_worklist wl1)
    | w_compact A1 B1 => 1 + (size_aexpr A1) + (size_aexpr B1)
  end

with size_worklist (wl1 : worklist) {struct wl1} : nat :=
  match wl1 with
    | wl_nil => 1
    | wl_cons wl2 w1 => 1 + (size_worklist wl2) + (size_work w1)
    | wl_bind wl2 b1 => 1 + (size_worklist wl2) + (size_binding b1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_aexpr_wrt_aexpr : nat -> aexpr -> Prop :=
  | degree_wrt_aexpr_ae_var_f : forall n1 x1,
    degree_aexpr_wrt_aexpr n1 (ae_var_f x1)
  | degree_wrt_aexpr_ae_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_aexpr_wrt_aexpr n1 (ae_var_b n2)
  | degree_wrt_aexpr_ae_kind : forall n1 k1,
    degree_aexpr_wrt_aexpr n1 (ae_kind k1)
  | degree_wrt_aexpr_ae_ex : forall n1 ex1,
    degree_aexpr_wrt_aexpr n1 (ae_ex ex1)
  | degree_wrt_aexpr_ae_num : forall n1 n2,
    degree_aexpr_wrt_aexpr n1 (ae_num n2)
  | degree_wrt_aexpr_ae_int : forall n1,
    degree_aexpr_wrt_aexpr n1 (ae_int)
  | degree_wrt_aexpr_ae_bot : forall n1 A1,
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_aexpr_wrt_aexpr n1 (ae_bot A1)
  | degree_wrt_aexpr_ae_app : forall n1 e1 e2,
    degree_aexpr_wrt_aexpr n1 e1 ->
    degree_aexpr_wrt_aexpr n1 e2 ->
    degree_aexpr_wrt_aexpr n1 (ae_app e1 e2)
  | degree_wrt_aexpr_ae_abs : forall n1 A1 ab1,
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_abody_wrt_aexpr (S n1) ab1 ->
    degree_aexpr_wrt_aexpr n1 (ae_abs A1 ab1)
  | degree_wrt_aexpr_ae_pi : forall n1 A1 B1,
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_aexpr_wrt_aexpr (S n1) B1 ->
    degree_aexpr_wrt_aexpr n1 (ae_pi A1 B1)
  | degree_wrt_aexpr_ae_bind : forall n1 A1 ab1,
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_abody_wrt_aexpr (S n1) ab1 ->
    degree_aexpr_wrt_aexpr n1 (ae_bind A1 ab1)
  | degree_wrt_aexpr_ae_all : forall n1 A1 B1,
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_aexpr_wrt_aexpr (S n1) B1 ->
    degree_aexpr_wrt_aexpr n1 (ae_all A1 B1)
  | degree_wrt_aexpr_ae_castup : forall n1 A1 e1,
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_aexpr_wrt_aexpr n1 e1 ->
    degree_aexpr_wrt_aexpr n1 (ae_castup A1 e1)
  | degree_wrt_aexpr_ae_castdn : forall n1 e1,
    degree_aexpr_wrt_aexpr n1 e1 ->
    degree_aexpr_wrt_aexpr n1 (ae_castdn e1)

with degree_abody_wrt_aexpr : nat -> abody -> Prop :=
  | degree_wrt_aexpr_ab_anno : forall n1 e1 A1,
    degree_aexpr_wrt_aexpr n1 e1 ->
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_abody_wrt_aexpr n1 (ab_anno e1 A1).

Scheme degree_aexpr_wrt_aexpr_ind' := Induction for degree_aexpr_wrt_aexpr Sort Prop
  with degree_abody_wrt_aexpr_ind' := Induction for degree_abody_wrt_aexpr Sort Prop.

Definition degree_aexpr_wrt_aexpr_degree_abody_wrt_aexpr_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 =>
  (conj (degree_aexpr_wrt_aexpr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)
  (degree_abody_wrt_aexpr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)).

Hint Constructors degree_aexpr_wrt_aexpr : core lngen.

Hint Constructors degree_abody_wrt_aexpr : core lngen.

Inductive degree_binding_wrt_aexpr : nat -> binding -> Prop :=
  | degree_wrt_aexpr_b_var : forall n1 x1 A1,
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_binding_wrt_aexpr n1 (b_var x1 A1)
  | degree_wrt_aexpr_b_ex : forall n1 ex1 A1,
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_binding_wrt_aexpr n1 (b_ex ex1 A1)
  | degree_wrt_aexpr_b_kind : forall n1 kx1,
    degree_binding_wrt_aexpr n1 (b_kind kx1).

Scheme degree_binding_wrt_aexpr_ind' := Induction for degree_binding_wrt_aexpr Sort Prop.

Definition degree_binding_wrt_aexpr_mutind :=
  fun H1 H2 H3 H4 =>
  degree_binding_wrt_aexpr_ind' H1 H2 H3 H4.

Hint Constructors degree_binding_wrt_aexpr : core lngen.

Inductive degree_obind_wrt_aexpr : nat -> obind -> Prop :=
  | degree_wrt_aexpr_ob_none : forall n1,
    degree_obind_wrt_aexpr n1 (ob_none)
  | degree_wrt_aexpr_ob_bind : forall n1 x1 A1,
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_obind_wrt_aexpr n1 (ob_bind x1 A1).

Scheme degree_obind_wrt_aexpr_ind' := Induction for degree_obind_wrt_aexpr Sort Prop.

Definition degree_obind_wrt_aexpr_mutind :=
  fun H1 H2 H3 =>
  degree_obind_wrt_aexpr_ind' H1 H2 H3.

Hint Constructors degree_obind_wrt_aexpr : core lngen.

Inductive degree_work_wrt_aexpr : nat -> work -> Prop :=
  | degree_wrt_aexpr_w_check : forall n1 ob1 e1 e2 A1,
    degree_obind_wrt_aexpr n1 ob1 ->
    degree_aexpr_wrt_aexpr n1 e1 ->
    degree_aexpr_wrt_aexpr n1 e2 ->
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_work_wrt_aexpr n1 (w_check ob1 e1 e2 A1)
  | degree_wrt_aexpr_w_infer : forall n1 e1 e2 wl1,
    degree_aexpr_wrt_aexpr n1 e1 ->
    degree_aexpr_wrt_aexpr n1 e2 ->
    degree_worklist_wrt_aexpr (S n1) wl1 ->
    degree_work_wrt_aexpr n1 (w_infer e1 e2 wl1)
  | degree_wrt_aexpr_w_infer_app : forall n1 A1 e1 e2 wl1,
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_aexpr_wrt_aexpr n1 e1 ->
    degree_aexpr_wrt_aexpr n1 e2 ->
    degree_worklist_wrt_aexpr (S n1) wl1 ->
    degree_work_wrt_aexpr n1 (w_infer_app A1 e1 e2 wl1)
  | degree_wrt_aexpr_w_reduce : forall n1 e1 wl1,
    degree_aexpr_wrt_aexpr n1 e1 ->
    degree_worklist_wrt_aexpr (S n1) wl1 ->
    degree_work_wrt_aexpr n1 (w_reduce e1 wl1)
  | degree_wrt_aexpr_w_compact : forall n1 A1 B1,
    degree_aexpr_wrt_aexpr n1 A1 ->
    degree_aexpr_wrt_aexpr n1 B1 ->
    degree_work_wrt_aexpr n1 (w_compact A1 B1)

with degree_worklist_wrt_aexpr : nat -> worklist -> Prop :=
  | degree_wrt_aexpr_wl_nil : forall n1,
    degree_worklist_wrt_aexpr n1 (wl_nil)
  | degree_wrt_aexpr_wl_cons : forall n1 wl1 w1,
    degree_worklist_wrt_aexpr n1 wl1 ->
    degree_work_wrt_aexpr n1 w1 ->
    degree_worklist_wrt_aexpr n1 (wl_cons wl1 w1)
  | degree_wrt_aexpr_wl_bind : forall n1 wl1 b1,
    degree_worklist_wrt_aexpr n1 wl1 ->
    degree_binding_wrt_aexpr n1 b1 ->
    degree_worklist_wrt_aexpr n1 (wl_bind wl1 b1).

Scheme degree_work_wrt_aexpr_ind' := Induction for degree_work_wrt_aexpr Sort Prop
  with degree_worklist_wrt_aexpr_ind' := Induction for degree_worklist_wrt_aexpr Sort Prop.

Definition degree_work_wrt_aexpr_degree_worklist_wrt_aexpr_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (conj (degree_work_wrt_aexpr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (degree_worklist_wrt_aexpr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Hint Constructors degree_work_wrt_aexpr : core lngen.

Hint Constructors degree_worklist_wrt_aexpr : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_aexpr : aexpr -> Set :=
  | lc_set_ae_var_f : forall x1,
    lc_set_aexpr (ae_var_f x1)
  | lc_set_ae_kind : forall k1,
    lc_set_aexpr (ae_kind k1)
  | lc_set_ae_ex : forall ex1,
    lc_set_aexpr (ae_ex ex1)
  | lc_set_ae_num : forall n1,
    lc_set_aexpr (ae_num n1)
  | lc_set_ae_int :
    lc_set_aexpr (ae_int)
  | lc_set_ae_bot : forall A1,
    lc_set_aexpr A1 ->
    lc_set_aexpr (ae_bot A1)
  | lc_set_ae_app : forall e1 e2,
    lc_set_aexpr e1 ->
    lc_set_aexpr e2 ->
    lc_set_aexpr (ae_app e1 e2)
  | lc_set_ae_abs : forall A1 ab1,
    lc_set_aexpr A1 ->
    (forall x1 : aexprvar, lc_set_abody (open_abody_wrt_aexpr ab1 (ae_var_f x1))) ->
    lc_set_aexpr (ae_abs A1 ab1)
  | lc_set_ae_pi : forall A1 B1,
    lc_set_aexpr A1 ->
    (forall x1 : aexprvar, lc_set_aexpr (open_aexpr_wrt_aexpr B1 (ae_var_f x1))) ->
    lc_set_aexpr (ae_pi A1 B1)
  | lc_set_ae_bind : forall A1 ab1,
    lc_set_aexpr A1 ->
    (forall x1 : aexprvar, lc_set_abody (open_abody_wrt_aexpr ab1 (ae_var_f x1))) ->
    lc_set_aexpr (ae_bind A1 ab1)
  | lc_set_ae_all : forall A1 B1,
    lc_set_aexpr A1 ->
    (forall x1 : aexprvar, lc_set_aexpr (open_aexpr_wrt_aexpr B1 (ae_var_f x1))) ->
    lc_set_aexpr (ae_all A1 B1)
  | lc_set_ae_castup : forall A1 e1,
    lc_set_aexpr A1 ->
    lc_set_aexpr e1 ->
    lc_set_aexpr (ae_castup A1 e1)
  | lc_set_ae_castdn : forall e1,
    lc_set_aexpr e1 ->
    lc_set_aexpr (ae_castdn e1)

with lc_set_abody : abody -> Set :=
  | lc_set_ab_anno : forall e1 A1,
    lc_set_aexpr e1 ->
    lc_set_aexpr A1 ->
    lc_set_abody (ab_anno e1 A1).

Scheme lc_aexpr_ind' := Induction for lc_aexpr Sort Prop
  with lc_abody_ind' := Induction for lc_abody Sort Prop.

Definition lc_aexpr_lc_abody_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  (conj (lc_aexpr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)
  (lc_abody_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)).

Scheme lc_set_aexpr_ind' := Induction for lc_set_aexpr Sort Prop
  with lc_set_abody_ind' := Induction for lc_set_abody Sort Prop.

Definition lc_set_aexpr_lc_set_abody_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  (conj (lc_set_aexpr_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)
  (lc_set_abody_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)).

Scheme lc_set_aexpr_rec' := Induction for lc_set_aexpr Sort Set
  with lc_set_abody_rec' := Induction for lc_set_abody Sort Set.

Definition lc_set_aexpr_lc_set_abody_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  (pair (lc_set_aexpr_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)
  (lc_set_abody_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)).

Hint Constructors lc_aexpr : core lngen.

Hint Constructors lc_abody : core lngen.

Hint Constructors lc_set_aexpr : core lngen.

Hint Constructors lc_set_abody : core lngen.

Inductive lc_set_binding : binding -> Set :=
  | lc_set_b_var : forall x1 A1,
    lc_set_aexpr A1 ->
    lc_set_binding (b_var x1 A1)
  | lc_set_b_ex : forall ex1 A1,
    lc_set_aexpr A1 ->
    lc_set_binding (b_ex ex1 A1)
  | lc_set_b_kind : forall kx1,
    lc_set_binding (b_kind kx1).

Scheme lc_binding_ind' := Induction for lc_binding Sort Prop.

Definition lc_binding_mutind :=
  fun H1 H2 H3 H4 =>
  lc_binding_ind' H1 H2 H3 H4.

Scheme lc_set_binding_ind' := Induction for lc_set_binding Sort Prop.

Definition lc_set_binding_mutind :=
  fun H1 H2 H3 H4 =>
  lc_set_binding_ind' H1 H2 H3 H4.

Scheme lc_set_binding_rec' := Induction for lc_set_binding Sort Set.

Definition lc_set_binding_mutrec :=
  fun H1 H2 H3 H4 =>
  lc_set_binding_rec' H1 H2 H3 H4.

Hint Constructors lc_binding : core lngen.

Hint Constructors lc_set_binding : core lngen.

Inductive lc_set_obind : obind -> Set :=
  | lc_set_ob_none :
    lc_set_obind (ob_none)
  | lc_set_ob_bind : forall x1 A1,
    lc_set_aexpr A1 ->
    lc_set_obind (ob_bind x1 A1).

Scheme lc_obind_ind' := Induction for lc_obind Sort Prop.

Definition lc_obind_mutind :=
  fun H1 H2 H3 =>
  lc_obind_ind' H1 H2 H3.

Scheme lc_set_obind_ind' := Induction for lc_set_obind Sort Prop.

Definition lc_set_obind_mutind :=
  fun H1 H2 H3 =>
  lc_set_obind_ind' H1 H2 H3.

Scheme lc_set_obind_rec' := Induction for lc_set_obind Sort Set.

Definition lc_set_obind_mutrec :=
  fun H1 H2 H3 =>
  lc_set_obind_rec' H1 H2 H3.

Hint Constructors lc_obind : core lngen.

Hint Constructors lc_set_obind : core lngen.

Inductive lc_set_work : work -> Set :=
  | lc_set_w_check : forall ob1 e1 e2 A1,
    lc_set_obind ob1 ->
    lc_set_aexpr e1 ->
    lc_set_aexpr e2 ->
    lc_set_aexpr A1 ->
    lc_set_work (w_check ob1 e1 e2 A1)
  | lc_set_w_infer : forall e1 e2 wl1,
    lc_set_aexpr e1 ->
    lc_set_aexpr e2 ->
    (forall x1 : aexprvar, lc_set_worklist (open_worklist_wrt_aexpr wl1 (ae_var_f x1))) ->
    lc_set_work (w_infer e1 e2 wl1)
  | lc_set_w_infer_app : forall A1 e1 e2 wl1,
    lc_set_aexpr A1 ->
    lc_set_aexpr e1 ->
    lc_set_aexpr e2 ->
    (forall x1 : aexprvar, lc_set_worklist (open_worklist_wrt_aexpr wl1 (ae_var_f x1))) ->
    lc_set_work (w_infer_app A1 e1 e2 wl1)
  | lc_set_w_reduce : forall e1 wl1,
    lc_set_aexpr e1 ->
    (forall x1 : aexprvar, lc_set_worklist (open_worklist_wrt_aexpr wl1 (ae_var_f x1))) ->
    lc_set_work (w_reduce e1 wl1)
  | lc_set_w_compact : forall A1 B1,
    lc_set_aexpr A1 ->
    lc_set_aexpr B1 ->
    lc_set_work (w_compact A1 B1)

with lc_set_worklist : worklist -> Set :=
  | lc_set_wl_nil :
    lc_set_worklist (wl_nil)
  | lc_set_wl_cons : forall wl1 w1,
    lc_set_worklist wl1 ->
    lc_set_work w1 ->
    lc_set_worklist (wl_cons wl1 w1)
  | lc_set_wl_bind : forall wl1 b1,
    lc_set_worklist wl1 ->
    lc_set_binding b1 ->
    lc_set_worklist (wl_bind wl1 b1).

Scheme lc_work_ind' := Induction for lc_work Sort Prop
  with lc_worklist_ind' := Induction for lc_worklist Sort Prop.

Definition lc_work_lc_worklist_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (conj (lc_work_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (lc_worklist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Scheme lc_set_work_ind' := Induction for lc_set_work Sort Prop
  with lc_set_worklist_ind' := Induction for lc_set_worklist Sort Prop.

Definition lc_set_work_lc_set_worklist_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (conj (lc_set_work_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (lc_set_worklist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Scheme lc_set_work_rec' := Induction for lc_set_work Sort Set
  with lc_set_worklist_rec' := Induction for lc_set_worklist Sort Set.

Definition lc_set_work_lc_set_worklist_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (pair (lc_set_work_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (lc_set_worklist_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Hint Constructors lc_work : core lngen.

Hint Constructors lc_worklist : core lngen.

Hint Constructors lc_set_work : core lngen.

Hint Constructors lc_set_worklist : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_aexpr_wrt_aexpr e1 := forall x1, lc_aexpr (open_aexpr_wrt_aexpr e1 (ae_var_f x1)).

Definition body_abody_wrt_aexpr ab1 := forall x1, lc_abody (open_abody_wrt_aexpr ab1 (ae_var_f x1)).

Hint Unfold body_aexpr_wrt_aexpr : core.

Hint Unfold body_abody_wrt_aexpr : core.

Definition body_binding_wrt_aexpr b1 := forall x1, lc_binding (open_binding_wrt_aexpr b1 (ae_var_f x1)).

Hint Unfold body_binding_wrt_aexpr : core.

Definition body_obind_wrt_aexpr ob1 := forall x1, lc_obind (open_obind_wrt_aexpr ob1 (ae_var_f x1)).

Hint Unfold body_obind_wrt_aexpr : core.

Definition body_work_wrt_aexpr w1 := forall x1, lc_work (open_work_wrt_aexpr w1 (ae_var_f x1)).

Definition body_worklist_wrt_aexpr wl1 := forall x1, lc_worklist (open_worklist_wrt_aexpr wl1 (ae_var_f x1)).

Hint Unfold body_work_wrt_aexpr : core.

Hint Unfold body_worklist_wrt_aexpr : core.


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

Lemma size_akind_min_mutual :
(forall k1, 1 <= size_akind k1).
Proof.
apply_mutual_ind akind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_akind_min :
forall k1, 1 <= size_akind k1.
Proof.
pose proof size_akind_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_akind_min : lngen.

(* begin hide *)

Lemma size_aexpr_min_size_abody_min_mutual :
(forall e1, 1 <= size_aexpr e1) /\
(forall ab1, 1 <= size_abody ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_aexpr_min :
forall e1, 1 <= size_aexpr e1.
Proof.
pose proof size_aexpr_min_size_abody_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_aexpr_min : lngen.

Lemma size_abody_min :
forall ab1, 1 <= size_abody ab1.
Proof.
pose proof size_aexpr_min_size_abody_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_abody_min : lngen.

(* begin hide *)

Lemma size_binding_min_mutual :
(forall b1, 1 <= size_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_binding_min :
forall b1, 1 <= size_binding b1.
Proof.
pose proof size_binding_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_binding_min : lngen.

(* begin hide *)

Lemma size_obind_min_mutual :
(forall ob1, 1 <= size_obind ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_obind_min :
forall ob1, 1 <= size_obind ob1.
Proof.
pose proof size_obind_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_obind_min : lngen.

(* begin hide *)

Lemma size_work_min_size_worklist_min_mutual :
(forall w1, 1 <= size_work w1) /\
(forall wl1, 1 <= size_worklist wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_work_min :
forall w1, 1 <= size_work w1.
Proof.
pose proof size_work_min_size_worklist_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_work_min : lngen.

Lemma size_worklist_min :
forall wl1, 1 <= size_worklist wl1.
Proof.
pose proof size_work_min_size_worklist_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_worklist_min : lngen.

(* begin hide *)

Lemma size_aexpr_close_aexpr_wrt_aexpr_rec_size_abody_close_abody_wrt_aexpr_rec_mutual :
(forall e1 x1 n1,
  size_aexpr (close_aexpr_wrt_aexpr_rec n1 x1 e1) = size_aexpr e1) /\
(forall ab1 x1 n1,
  size_abody (close_abody_wrt_aexpr_rec n1 x1 ab1) = size_abody ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_aexpr_close_aexpr_wrt_aexpr_rec :
forall e1 x1 n1,
  size_aexpr (close_aexpr_wrt_aexpr_rec n1 x1 e1) = size_aexpr e1.
Proof.
pose proof size_aexpr_close_aexpr_wrt_aexpr_rec_size_abody_close_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_aexpr_close_aexpr_wrt_aexpr_rec : lngen.
Hint Rewrite size_aexpr_close_aexpr_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abody_close_abody_wrt_aexpr_rec :
forall ab1 x1 n1,
  size_abody (close_abody_wrt_aexpr_rec n1 x1 ab1) = size_abody ab1.
Proof.
pose proof size_aexpr_close_aexpr_wrt_aexpr_rec_size_abody_close_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_abody_close_abody_wrt_aexpr_rec : lngen.
Hint Rewrite size_abody_close_abody_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_binding_close_binding_wrt_aexpr_rec_mutual :
(forall b1 x1 n1,
  size_binding (close_binding_wrt_aexpr_rec n1 x1 b1) = size_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_binding_close_binding_wrt_aexpr_rec :
forall b1 x1 n1,
  size_binding (close_binding_wrt_aexpr_rec n1 x1 b1) = size_binding b1.
Proof.
pose proof size_binding_close_binding_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_binding_close_binding_wrt_aexpr_rec : lngen.
Hint Rewrite size_binding_close_binding_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_obind_close_obind_wrt_aexpr_rec_mutual :
(forall ob1 x1 n1,
  size_obind (close_obind_wrt_aexpr_rec n1 x1 ob1) = size_obind ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_obind_close_obind_wrt_aexpr_rec :
forall ob1 x1 n1,
  size_obind (close_obind_wrt_aexpr_rec n1 x1 ob1) = size_obind ob1.
Proof.
pose proof size_obind_close_obind_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_obind_close_obind_wrt_aexpr_rec : lngen.
Hint Rewrite size_obind_close_obind_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_work_close_work_wrt_aexpr_rec_size_worklist_close_worklist_wrt_aexpr_rec_mutual :
(forall w1 x1 n1,
  size_work (close_work_wrt_aexpr_rec n1 x1 w1) = size_work w1) /\
(forall wl1 x1 n1,
  size_worklist (close_worklist_wrt_aexpr_rec n1 x1 wl1) = size_worklist wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_work_close_work_wrt_aexpr_rec :
forall w1 x1 n1,
  size_work (close_work_wrt_aexpr_rec n1 x1 w1) = size_work w1.
Proof.
pose proof size_work_close_work_wrt_aexpr_rec_size_worklist_close_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_work_close_work_wrt_aexpr_rec : lngen.
Hint Rewrite size_work_close_work_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_worklist_close_worklist_wrt_aexpr_rec :
forall wl1 x1 n1,
  size_worklist (close_worklist_wrt_aexpr_rec n1 x1 wl1) = size_worklist wl1.
Proof.
pose proof size_work_close_work_wrt_aexpr_rec_size_worklist_close_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_worklist_close_worklist_wrt_aexpr_rec : lngen.
Hint Rewrite size_worklist_close_worklist_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_aexpr_close_aexpr_wrt_aexpr :
forall e1 x1,
  size_aexpr (close_aexpr_wrt_aexpr x1 e1) = size_aexpr e1.
Proof.
unfold close_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_aexpr_close_aexpr_wrt_aexpr : lngen.
Hint Rewrite size_aexpr_close_aexpr_wrt_aexpr using solve [auto] : lngen.

Lemma size_abody_close_abody_wrt_aexpr :
forall ab1 x1,
  size_abody (close_abody_wrt_aexpr x1 ab1) = size_abody ab1.
Proof.
unfold close_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_abody_close_abody_wrt_aexpr : lngen.
Hint Rewrite size_abody_close_abody_wrt_aexpr using solve [auto] : lngen.

Lemma size_binding_close_binding_wrt_aexpr :
forall b1 x1,
  size_binding (close_binding_wrt_aexpr x1 b1) = size_binding b1.
Proof.
unfold close_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_binding_close_binding_wrt_aexpr : lngen.
Hint Rewrite size_binding_close_binding_wrt_aexpr using solve [auto] : lngen.

Lemma size_obind_close_obind_wrt_aexpr :
forall ob1 x1,
  size_obind (close_obind_wrt_aexpr x1 ob1) = size_obind ob1.
Proof.
unfold close_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_obind_close_obind_wrt_aexpr : lngen.
Hint Rewrite size_obind_close_obind_wrt_aexpr using solve [auto] : lngen.

Lemma size_work_close_work_wrt_aexpr :
forall w1 x1,
  size_work (close_work_wrt_aexpr x1 w1) = size_work w1.
Proof.
unfold close_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_work_close_work_wrt_aexpr : lngen.
Hint Rewrite size_work_close_work_wrt_aexpr using solve [auto] : lngen.

Lemma size_worklist_close_worklist_wrt_aexpr :
forall wl1 x1,
  size_worklist (close_worklist_wrt_aexpr x1 wl1) = size_worklist wl1.
Proof.
unfold close_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_worklist_close_worklist_wrt_aexpr : lngen.
Hint Rewrite size_worklist_close_worklist_wrt_aexpr using solve [auto] : lngen.

(* begin hide *)

Lemma size_aexpr_open_aexpr_wrt_aexpr_rec_size_abody_open_abody_wrt_aexpr_rec_mutual :
(forall e1 e2 n1,
  size_aexpr e1 <= size_aexpr (open_aexpr_wrt_aexpr_rec n1 e2 e1)) /\
(forall ab1 e1 n1,
  size_abody ab1 <= size_abody (open_abody_wrt_aexpr_rec n1 e1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_aexpr_open_aexpr_wrt_aexpr_rec :
forall e1 e2 n1,
  size_aexpr e1 <= size_aexpr (open_aexpr_wrt_aexpr_rec n1 e2 e1).
Proof.
pose proof size_aexpr_open_aexpr_wrt_aexpr_rec_size_abody_open_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_aexpr_open_aexpr_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abody_open_abody_wrt_aexpr_rec :
forall ab1 e1 n1,
  size_abody ab1 <= size_abody (open_abody_wrt_aexpr_rec n1 e1 ab1).
Proof.
pose proof size_aexpr_open_aexpr_wrt_aexpr_rec_size_abody_open_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_abody_open_abody_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_aexpr_rec_mutual :
(forall b1 e1 n1,
  size_binding b1 <= size_binding (open_binding_wrt_aexpr_rec n1 e1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_aexpr_rec :
forall b1 e1 n1,
  size_binding b1 <= size_binding (open_binding_wrt_aexpr_rec n1 e1 b1).
Proof.
pose proof size_binding_open_binding_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_binding_open_binding_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_obind_open_obind_wrt_aexpr_rec_mutual :
(forall ob1 e1 n1,
  size_obind ob1 <= size_obind (open_obind_wrt_aexpr_rec n1 e1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_obind_open_obind_wrt_aexpr_rec :
forall ob1 e1 n1,
  size_obind ob1 <= size_obind (open_obind_wrt_aexpr_rec n1 e1 ob1).
Proof.
pose proof size_obind_open_obind_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_obind_open_obind_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_aexpr_rec_size_worklist_open_worklist_wrt_aexpr_rec_mutual :
(forall w1 e1 n1,
  size_work w1 <= size_work (open_work_wrt_aexpr_rec n1 e1 w1)) /\
(forall wl1 e1 n1,
  size_worklist wl1 <= size_worklist (open_worklist_wrt_aexpr_rec n1 e1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_aexpr_rec :
forall w1 e1 n1,
  size_work w1 <= size_work (open_work_wrt_aexpr_rec n1 e1 w1).
Proof.
pose proof size_work_open_work_wrt_aexpr_rec_size_worklist_open_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_work_open_work_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_worklist_open_worklist_wrt_aexpr_rec :
forall wl1 e1 n1,
  size_worklist wl1 <= size_worklist (open_worklist_wrt_aexpr_rec n1 e1 wl1).
Proof.
pose proof size_work_open_work_wrt_aexpr_rec_size_worklist_open_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_worklist_open_worklist_wrt_aexpr_rec : lngen.

(* end hide *)

Lemma size_aexpr_open_aexpr_wrt_aexpr :
forall e1 e2,
  size_aexpr e1 <= size_aexpr (open_aexpr_wrt_aexpr e1 e2).
Proof.
unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_aexpr_open_aexpr_wrt_aexpr : lngen.

Lemma size_abody_open_abody_wrt_aexpr :
forall ab1 e1,
  size_abody ab1 <= size_abody (open_abody_wrt_aexpr ab1 e1).
Proof.
unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_abody_open_abody_wrt_aexpr : lngen.

Lemma size_binding_open_binding_wrt_aexpr :
forall b1 e1,
  size_binding b1 <= size_binding (open_binding_wrt_aexpr b1 e1).
Proof.
unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_binding_open_binding_wrt_aexpr : lngen.

Lemma size_obind_open_obind_wrt_aexpr :
forall ob1 e1,
  size_obind ob1 <= size_obind (open_obind_wrt_aexpr ob1 e1).
Proof.
unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_obind_open_obind_wrt_aexpr : lngen.

Lemma size_work_open_work_wrt_aexpr :
forall w1 e1,
  size_work w1 <= size_work (open_work_wrt_aexpr w1 e1).
Proof.
unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_work_open_work_wrt_aexpr : lngen.

Lemma size_worklist_open_worklist_wrt_aexpr :
forall wl1 e1,
  size_worklist wl1 <= size_worklist (open_worklist_wrt_aexpr wl1 e1).
Proof.
unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_worklist_open_worklist_wrt_aexpr : lngen.

(* begin hide *)

Lemma size_aexpr_open_aexpr_wrt_aexpr_rec_var_size_abody_open_abody_wrt_aexpr_rec_var_mutual :
(forall e1 x1 n1,
  size_aexpr (open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) e1) = size_aexpr e1) /\
(forall ab1 x1 n1,
  size_abody (open_abody_wrt_aexpr_rec n1 (ae_var_f x1) ab1) = size_abody ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_aexpr_open_aexpr_wrt_aexpr_rec_var :
forall e1 x1 n1,
  size_aexpr (open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) e1) = size_aexpr e1.
Proof.
pose proof size_aexpr_open_aexpr_wrt_aexpr_rec_var_size_abody_open_abody_wrt_aexpr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_aexpr_open_aexpr_wrt_aexpr_rec_var : lngen.
Hint Rewrite size_aexpr_open_aexpr_wrt_aexpr_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abody_open_abody_wrt_aexpr_rec_var :
forall ab1 x1 n1,
  size_abody (open_abody_wrt_aexpr_rec n1 (ae_var_f x1) ab1) = size_abody ab1.
Proof.
pose proof size_aexpr_open_aexpr_wrt_aexpr_rec_var_size_abody_open_abody_wrt_aexpr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_abody_open_abody_wrt_aexpr_rec_var : lngen.
Hint Rewrite size_abody_open_abody_wrt_aexpr_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_aexpr_rec_var_mutual :
(forall b1 x1 n1,
  size_binding (open_binding_wrt_aexpr_rec n1 (ae_var_f x1) b1) = size_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_aexpr_rec_var :
forall b1 x1 n1,
  size_binding (open_binding_wrt_aexpr_rec n1 (ae_var_f x1) b1) = size_binding b1.
Proof.
pose proof size_binding_open_binding_wrt_aexpr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_binding_open_binding_wrt_aexpr_rec_var : lngen.
Hint Rewrite size_binding_open_binding_wrt_aexpr_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_obind_open_obind_wrt_aexpr_rec_var_mutual :
(forall ob1 x1 n1,
  size_obind (open_obind_wrt_aexpr_rec n1 (ae_var_f x1) ob1) = size_obind ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_obind_open_obind_wrt_aexpr_rec_var :
forall ob1 x1 n1,
  size_obind (open_obind_wrt_aexpr_rec n1 (ae_var_f x1) ob1) = size_obind ob1.
Proof.
pose proof size_obind_open_obind_wrt_aexpr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_obind_open_obind_wrt_aexpr_rec_var : lngen.
Hint Rewrite size_obind_open_obind_wrt_aexpr_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_aexpr_rec_var_size_worklist_open_worklist_wrt_aexpr_rec_var_mutual :
(forall w1 x1 n1,
  size_work (open_work_wrt_aexpr_rec n1 (ae_var_f x1) w1) = size_work w1) /\
(forall wl1 x1 n1,
  size_worklist (open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) wl1) = size_worklist wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_aexpr_rec_var :
forall w1 x1 n1,
  size_work (open_work_wrt_aexpr_rec n1 (ae_var_f x1) w1) = size_work w1.
Proof.
pose proof size_work_open_work_wrt_aexpr_rec_var_size_worklist_open_worklist_wrt_aexpr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_work_open_work_wrt_aexpr_rec_var : lngen.
Hint Rewrite size_work_open_work_wrt_aexpr_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_worklist_open_worklist_wrt_aexpr_rec_var :
forall wl1 x1 n1,
  size_worklist (open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) wl1) = size_worklist wl1.
Proof.
pose proof size_work_open_work_wrt_aexpr_rec_var_size_worklist_open_worklist_wrt_aexpr_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_worklist_open_worklist_wrt_aexpr_rec_var : lngen.
Hint Rewrite size_worklist_open_worklist_wrt_aexpr_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_aexpr_open_aexpr_wrt_aexpr_var :
forall e1 x1,
  size_aexpr (open_aexpr_wrt_aexpr e1 (ae_var_f x1)) = size_aexpr e1.
Proof.
unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_aexpr_open_aexpr_wrt_aexpr_var : lngen.
Hint Rewrite size_aexpr_open_aexpr_wrt_aexpr_var using solve [auto] : lngen.

Lemma size_abody_open_abody_wrt_aexpr_var :
forall ab1 x1,
  size_abody (open_abody_wrt_aexpr ab1 (ae_var_f x1)) = size_abody ab1.
Proof.
unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_abody_open_abody_wrt_aexpr_var : lngen.
Hint Rewrite size_abody_open_abody_wrt_aexpr_var using solve [auto] : lngen.

Lemma size_binding_open_binding_wrt_aexpr_var :
forall b1 x1,
  size_binding (open_binding_wrt_aexpr b1 (ae_var_f x1)) = size_binding b1.
Proof.
unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_binding_open_binding_wrt_aexpr_var : lngen.
Hint Rewrite size_binding_open_binding_wrt_aexpr_var using solve [auto] : lngen.

Lemma size_obind_open_obind_wrt_aexpr_var :
forall ob1 x1,
  size_obind (open_obind_wrt_aexpr ob1 (ae_var_f x1)) = size_obind ob1.
Proof.
unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_obind_open_obind_wrt_aexpr_var : lngen.
Hint Rewrite size_obind_open_obind_wrt_aexpr_var using solve [auto] : lngen.

Lemma size_work_open_work_wrt_aexpr_var :
forall w1 x1,
  size_work (open_work_wrt_aexpr w1 (ae_var_f x1)) = size_work w1.
Proof.
unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_work_open_work_wrt_aexpr_var : lngen.
Hint Rewrite size_work_open_work_wrt_aexpr_var using solve [auto] : lngen.

Lemma size_worklist_open_worklist_wrt_aexpr_var :
forall wl1 x1,
  size_worklist (open_worklist_wrt_aexpr wl1 (ae_var_f x1)) = size_worklist wl1.
Proof.
unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve size_worklist_open_worklist_wrt_aexpr_var : lngen.
Hint Rewrite size_worklist_open_worklist_wrt_aexpr_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_aexpr_wrt_aexpr_S_degree_abody_wrt_aexpr_S_mutual :
(forall n1 e1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_aexpr_wrt_aexpr (S n1) e1) /\
(forall n1 ab1,
  degree_abody_wrt_aexpr n1 ab1 ->
  degree_abody_wrt_aexpr (S n1) ab1).
Proof.
apply_mutual_ind degree_aexpr_wrt_aexpr_degree_abody_wrt_aexpr_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_aexpr_wrt_aexpr_S :
forall n1 e1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_aexpr_wrt_aexpr (S n1) e1.
Proof.
pose proof degree_aexpr_wrt_aexpr_S_degree_abody_wrt_aexpr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_aexpr_wrt_aexpr_S : lngen.

Lemma degree_abody_wrt_aexpr_S :
forall n1 ab1,
  degree_abody_wrt_aexpr n1 ab1 ->
  degree_abody_wrt_aexpr (S n1) ab1.
Proof.
pose proof degree_aexpr_wrt_aexpr_S_degree_abody_wrt_aexpr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_abody_wrt_aexpr_S : lngen.

(* begin hide *)

Lemma degree_binding_wrt_aexpr_S_mutual :
(forall n1 b1,
  degree_binding_wrt_aexpr n1 b1 ->
  degree_binding_wrt_aexpr (S n1) b1).
Proof.
apply_mutual_ind degree_binding_wrt_aexpr_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_binding_wrt_aexpr_S :
forall n1 b1,
  degree_binding_wrt_aexpr n1 b1 ->
  degree_binding_wrt_aexpr (S n1) b1.
Proof.
pose proof degree_binding_wrt_aexpr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_binding_wrt_aexpr_S : lngen.

(* begin hide *)

Lemma degree_obind_wrt_aexpr_S_mutual :
(forall n1 ob1,
  degree_obind_wrt_aexpr n1 ob1 ->
  degree_obind_wrt_aexpr (S n1) ob1).
Proof.
apply_mutual_ind degree_obind_wrt_aexpr_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_obind_wrt_aexpr_S :
forall n1 ob1,
  degree_obind_wrt_aexpr n1 ob1 ->
  degree_obind_wrt_aexpr (S n1) ob1.
Proof.
pose proof degree_obind_wrt_aexpr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_obind_wrt_aexpr_S : lngen.

(* begin hide *)

Lemma degree_work_wrt_aexpr_S_degree_worklist_wrt_aexpr_S_mutual :
(forall n1 w1,
  degree_work_wrt_aexpr n1 w1 ->
  degree_work_wrt_aexpr (S n1) w1) /\
(forall n1 wl1,
  degree_worklist_wrt_aexpr n1 wl1 ->
  degree_worklist_wrt_aexpr (S n1) wl1).
Proof.
apply_mutual_ind degree_work_wrt_aexpr_degree_worklist_wrt_aexpr_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_work_wrt_aexpr_S :
forall n1 w1,
  degree_work_wrt_aexpr n1 w1 ->
  degree_work_wrt_aexpr (S n1) w1.
Proof.
pose proof degree_work_wrt_aexpr_S_degree_worklist_wrt_aexpr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_work_wrt_aexpr_S : lngen.

Lemma degree_worklist_wrt_aexpr_S :
forall n1 wl1,
  degree_worklist_wrt_aexpr n1 wl1 ->
  degree_worklist_wrt_aexpr (S n1) wl1.
Proof.
pose proof degree_work_wrt_aexpr_S_degree_worklist_wrt_aexpr_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_worklist_wrt_aexpr_S : lngen.

Lemma degree_aexpr_wrt_aexpr_O :
forall n1 e1,
  degree_aexpr_wrt_aexpr O e1 ->
  degree_aexpr_wrt_aexpr n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_aexpr_wrt_aexpr_O : lngen.

Lemma degree_abody_wrt_aexpr_O :
forall n1 ab1,
  degree_abody_wrt_aexpr O ab1 ->
  degree_abody_wrt_aexpr n1 ab1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_abody_wrt_aexpr_O : lngen.

Lemma degree_binding_wrt_aexpr_O :
forall n1 b1,
  degree_binding_wrt_aexpr O b1 ->
  degree_binding_wrt_aexpr n1 b1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_binding_wrt_aexpr_O : lngen.

Lemma degree_obind_wrt_aexpr_O :
forall n1 ob1,
  degree_obind_wrt_aexpr O ob1 ->
  degree_obind_wrt_aexpr n1 ob1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_obind_wrt_aexpr_O : lngen.

Lemma degree_work_wrt_aexpr_O :
forall n1 w1,
  degree_work_wrt_aexpr O w1 ->
  degree_work_wrt_aexpr n1 w1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_work_wrt_aexpr_O : lngen.

Lemma degree_worklist_wrt_aexpr_O :
forall n1 wl1,
  degree_worklist_wrt_aexpr O wl1 ->
  degree_worklist_wrt_aexpr n1 wl1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_worklist_wrt_aexpr_O : lngen.

(* begin hide *)

Lemma degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_rec_degree_abody_wrt_aexpr_close_abody_wrt_aexpr_rec_mutual :
(forall e1 x1 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_aexpr_wrt_aexpr (S n1) (close_aexpr_wrt_aexpr_rec n1 x1 e1)) /\
(forall ab1 x1 n1,
  degree_abody_wrt_aexpr n1 ab1 ->
  degree_abody_wrt_aexpr (S n1) (close_abody_wrt_aexpr_rec n1 x1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_rec :
forall e1 x1 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_aexpr_wrt_aexpr (S n1) (close_aexpr_wrt_aexpr_rec n1 x1 e1).
Proof.
pose proof degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_rec_degree_abody_wrt_aexpr_close_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexpr_close_abody_wrt_aexpr_rec :
forall ab1 x1 n1,
  degree_abody_wrt_aexpr n1 ab1 ->
  degree_abody_wrt_aexpr (S n1) (close_abody_wrt_aexpr_rec n1 x1 ab1).
Proof.
pose proof degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_rec_degree_abody_wrt_aexpr_close_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_abody_wrt_aexpr_close_abody_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_aexpr_close_binding_wrt_aexpr_rec_mutual :
(forall b1 x1 n1,
  degree_binding_wrt_aexpr n1 b1 ->
  degree_binding_wrt_aexpr (S n1) (close_binding_wrt_aexpr_rec n1 x1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_aexpr_close_binding_wrt_aexpr_rec :
forall b1 x1 n1,
  degree_binding_wrt_aexpr n1 b1 ->
  degree_binding_wrt_aexpr (S n1) (close_binding_wrt_aexpr_rec n1 x1 b1).
Proof.
pose proof degree_binding_wrt_aexpr_close_binding_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_binding_wrt_aexpr_close_binding_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_obind_wrt_aexpr_close_obind_wrt_aexpr_rec_mutual :
(forall ob1 x1 n1,
  degree_obind_wrt_aexpr n1 ob1 ->
  degree_obind_wrt_aexpr (S n1) (close_obind_wrt_aexpr_rec n1 x1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_obind_wrt_aexpr_close_obind_wrt_aexpr_rec :
forall ob1 x1 n1,
  degree_obind_wrt_aexpr n1 ob1 ->
  degree_obind_wrt_aexpr (S n1) (close_obind_wrt_aexpr_rec n1 x1 ob1).
Proof.
pose proof degree_obind_wrt_aexpr_close_obind_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_obind_wrt_aexpr_close_obind_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_aexpr_close_work_wrt_aexpr_rec_degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_rec_mutual :
(forall w1 x1 n1,
  degree_work_wrt_aexpr n1 w1 ->
  degree_work_wrt_aexpr (S n1) (close_work_wrt_aexpr_rec n1 x1 w1)) /\
(forall wl1 x1 n1,
  degree_worklist_wrt_aexpr n1 wl1 ->
  degree_worklist_wrt_aexpr (S n1) (close_worklist_wrt_aexpr_rec n1 x1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_aexpr_close_work_wrt_aexpr_rec :
forall w1 x1 n1,
  degree_work_wrt_aexpr n1 w1 ->
  degree_work_wrt_aexpr (S n1) (close_work_wrt_aexpr_rec n1 x1 w1).
Proof.
pose proof degree_work_wrt_aexpr_close_work_wrt_aexpr_rec_degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_work_wrt_aexpr_close_work_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_rec :
forall wl1 x1 n1,
  degree_worklist_wrt_aexpr n1 wl1 ->
  degree_worklist_wrt_aexpr (S n1) (close_worklist_wrt_aexpr_rec n1 x1 wl1).
Proof.
pose proof degree_work_wrt_aexpr_close_work_wrt_aexpr_rec_degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_rec : lngen.

(* end hide *)

Lemma degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr :
forall e1 x1,
  degree_aexpr_wrt_aexpr 0 e1 ->
  degree_aexpr_wrt_aexpr 1 (close_aexpr_wrt_aexpr x1 e1).
Proof.
unfold close_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr : lngen.

Lemma degree_abody_wrt_aexpr_close_abody_wrt_aexpr :
forall ab1 x1,
  degree_abody_wrt_aexpr 0 ab1 ->
  degree_abody_wrt_aexpr 1 (close_abody_wrt_aexpr x1 ab1).
Proof.
unfold close_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_abody_wrt_aexpr_close_abody_wrt_aexpr : lngen.

Lemma degree_binding_wrt_aexpr_close_binding_wrt_aexpr :
forall b1 x1,
  degree_binding_wrt_aexpr 0 b1 ->
  degree_binding_wrt_aexpr 1 (close_binding_wrt_aexpr x1 b1).
Proof.
unfold close_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_binding_wrt_aexpr_close_binding_wrt_aexpr : lngen.

Lemma degree_obind_wrt_aexpr_close_obind_wrt_aexpr :
forall ob1 x1,
  degree_obind_wrt_aexpr 0 ob1 ->
  degree_obind_wrt_aexpr 1 (close_obind_wrt_aexpr x1 ob1).
Proof.
unfold close_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_obind_wrt_aexpr_close_obind_wrt_aexpr : lngen.

Lemma degree_work_wrt_aexpr_close_work_wrt_aexpr :
forall w1 x1,
  degree_work_wrt_aexpr 0 w1 ->
  degree_work_wrt_aexpr 1 (close_work_wrt_aexpr x1 w1).
Proof.
unfold close_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_work_wrt_aexpr_close_work_wrt_aexpr : lngen.

Lemma degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr :
forall wl1 x1,
  degree_worklist_wrt_aexpr 0 wl1 ->
  degree_worklist_wrt_aexpr 1 (close_worklist_wrt_aexpr x1 wl1).
Proof.
unfold close_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr : lngen.

(* begin hide *)

Lemma degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_rec_inv_degree_abody_wrt_aexpr_close_abody_wrt_aexpr_rec_inv_mutual :
(forall e1 x1 n1,
  degree_aexpr_wrt_aexpr (S n1) (close_aexpr_wrt_aexpr_rec n1 x1 e1) ->
  degree_aexpr_wrt_aexpr n1 e1) /\
(forall ab1 x1 n1,
  degree_abody_wrt_aexpr (S n1) (close_abody_wrt_aexpr_rec n1 x1 ab1) ->
  degree_abody_wrt_aexpr n1 ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_rec_inv :
forall e1 x1 n1,
  degree_aexpr_wrt_aexpr (S n1) (close_aexpr_wrt_aexpr_rec n1 x1 e1) ->
  degree_aexpr_wrt_aexpr n1 e1.
Proof.
pose proof degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_rec_inv_degree_abody_wrt_aexpr_close_abody_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexpr_close_abody_wrt_aexpr_rec_inv :
forall ab1 x1 n1,
  degree_abody_wrt_aexpr (S n1) (close_abody_wrt_aexpr_rec n1 x1 ab1) ->
  degree_abody_wrt_aexpr n1 ab1.
Proof.
pose proof degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_rec_inv_degree_abody_wrt_aexpr_close_abody_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_abody_wrt_aexpr_close_abody_wrt_aexpr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_aexpr_close_binding_wrt_aexpr_rec_inv_mutual :
(forall b1 x1 n1,
  degree_binding_wrt_aexpr (S n1) (close_binding_wrt_aexpr_rec n1 x1 b1) ->
  degree_binding_wrt_aexpr n1 b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_aexpr_close_binding_wrt_aexpr_rec_inv :
forall b1 x1 n1,
  degree_binding_wrt_aexpr (S n1) (close_binding_wrt_aexpr_rec n1 x1 b1) ->
  degree_binding_wrt_aexpr n1 b1.
Proof.
pose proof degree_binding_wrt_aexpr_close_binding_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_binding_wrt_aexpr_close_binding_wrt_aexpr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_obind_wrt_aexpr_close_obind_wrt_aexpr_rec_inv_mutual :
(forall ob1 x1 n1,
  degree_obind_wrt_aexpr (S n1) (close_obind_wrt_aexpr_rec n1 x1 ob1) ->
  degree_obind_wrt_aexpr n1 ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_obind_wrt_aexpr_close_obind_wrt_aexpr_rec_inv :
forall ob1 x1 n1,
  degree_obind_wrt_aexpr (S n1) (close_obind_wrt_aexpr_rec n1 x1 ob1) ->
  degree_obind_wrt_aexpr n1 ob1.
Proof.
pose proof degree_obind_wrt_aexpr_close_obind_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_obind_wrt_aexpr_close_obind_wrt_aexpr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_aexpr_close_work_wrt_aexpr_rec_inv_degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_rec_inv_mutual :
(forall w1 x1 n1,
  degree_work_wrt_aexpr (S n1) (close_work_wrt_aexpr_rec n1 x1 w1) ->
  degree_work_wrt_aexpr n1 w1) /\
(forall wl1 x1 n1,
  degree_worklist_wrt_aexpr (S n1) (close_worklist_wrt_aexpr_rec n1 x1 wl1) ->
  degree_worklist_wrt_aexpr n1 wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_aexpr_close_work_wrt_aexpr_rec_inv :
forall w1 x1 n1,
  degree_work_wrt_aexpr (S n1) (close_work_wrt_aexpr_rec n1 x1 w1) ->
  degree_work_wrt_aexpr n1 w1.
Proof.
pose proof degree_work_wrt_aexpr_close_work_wrt_aexpr_rec_inv_degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_work_wrt_aexpr_close_work_wrt_aexpr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_rec_inv :
forall wl1 x1 n1,
  degree_worklist_wrt_aexpr (S n1) (close_worklist_wrt_aexpr_rec n1 x1 wl1) ->
  degree_worklist_wrt_aexpr n1 wl1.
Proof.
pose proof degree_work_wrt_aexpr_close_work_wrt_aexpr_rec_inv_degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_rec_inv : lngen.

(* end hide *)

Lemma degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_inv :
forall e1 x1,
  degree_aexpr_wrt_aexpr 1 (close_aexpr_wrt_aexpr x1 e1) ->
  degree_aexpr_wrt_aexpr 0 e1.
Proof.
unfold close_aexpr_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr_inv : lngen.

Lemma degree_abody_wrt_aexpr_close_abody_wrt_aexpr_inv :
forall ab1 x1,
  degree_abody_wrt_aexpr 1 (close_abody_wrt_aexpr x1 ab1) ->
  degree_abody_wrt_aexpr 0 ab1.
Proof.
unfold close_abody_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_abody_wrt_aexpr_close_abody_wrt_aexpr_inv : lngen.

Lemma degree_binding_wrt_aexpr_close_binding_wrt_aexpr_inv :
forall b1 x1,
  degree_binding_wrt_aexpr 1 (close_binding_wrt_aexpr x1 b1) ->
  degree_binding_wrt_aexpr 0 b1.
Proof.
unfold close_binding_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_binding_wrt_aexpr_close_binding_wrt_aexpr_inv : lngen.

Lemma degree_obind_wrt_aexpr_close_obind_wrt_aexpr_inv :
forall ob1 x1,
  degree_obind_wrt_aexpr 1 (close_obind_wrt_aexpr x1 ob1) ->
  degree_obind_wrt_aexpr 0 ob1.
Proof.
unfold close_obind_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_obind_wrt_aexpr_close_obind_wrt_aexpr_inv : lngen.

Lemma degree_work_wrt_aexpr_close_work_wrt_aexpr_inv :
forall w1 x1,
  degree_work_wrt_aexpr 1 (close_work_wrt_aexpr x1 w1) ->
  degree_work_wrt_aexpr 0 w1.
Proof.
unfold close_work_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_work_wrt_aexpr_close_work_wrt_aexpr_inv : lngen.

Lemma degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_inv :
forall wl1 x1,
  degree_worklist_wrt_aexpr 1 (close_worklist_wrt_aexpr x1 wl1) ->
  degree_worklist_wrt_aexpr 0 wl1.
Proof.
unfold close_worklist_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_worklist_wrt_aexpr_close_worklist_wrt_aexpr_inv : lngen.

(* begin hide *)

Lemma degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_rec_degree_abody_wrt_aexpr_open_abody_wrt_aexpr_rec_mutual :
(forall e1 e2 n1,
  degree_aexpr_wrt_aexpr (S n1) e1 ->
  degree_aexpr_wrt_aexpr n1 e2 ->
  degree_aexpr_wrt_aexpr n1 (open_aexpr_wrt_aexpr_rec n1 e2 e1)) /\
(forall ab1 e1 n1,
  degree_abody_wrt_aexpr (S n1) ab1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_abody_wrt_aexpr n1 (open_abody_wrt_aexpr_rec n1 e1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_rec :
forall e1 e2 n1,
  degree_aexpr_wrt_aexpr (S n1) e1 ->
  degree_aexpr_wrt_aexpr n1 e2 ->
  degree_aexpr_wrt_aexpr n1 (open_aexpr_wrt_aexpr_rec n1 e2 e1).
Proof.
pose proof degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_rec_degree_abody_wrt_aexpr_open_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexpr_open_abody_wrt_aexpr_rec :
forall ab1 e1 n1,
  degree_abody_wrt_aexpr (S n1) ab1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_abody_wrt_aexpr n1 (open_abody_wrt_aexpr_rec n1 e1 ab1).
Proof.
pose proof degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_rec_degree_abody_wrt_aexpr_open_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_abody_wrt_aexpr_open_abody_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_aexpr_open_binding_wrt_aexpr_rec_mutual :
(forall b1 e1 n1,
  degree_binding_wrt_aexpr (S n1) b1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_binding_wrt_aexpr n1 (open_binding_wrt_aexpr_rec n1 e1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_aexpr_open_binding_wrt_aexpr_rec :
forall b1 e1 n1,
  degree_binding_wrt_aexpr (S n1) b1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_binding_wrt_aexpr n1 (open_binding_wrt_aexpr_rec n1 e1 b1).
Proof.
pose proof degree_binding_wrt_aexpr_open_binding_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_binding_wrt_aexpr_open_binding_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_obind_wrt_aexpr_open_obind_wrt_aexpr_rec_mutual :
(forall ob1 e1 n1,
  degree_obind_wrt_aexpr (S n1) ob1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_obind_wrt_aexpr n1 (open_obind_wrt_aexpr_rec n1 e1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_obind_wrt_aexpr_open_obind_wrt_aexpr_rec :
forall ob1 e1 n1,
  degree_obind_wrt_aexpr (S n1) ob1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_obind_wrt_aexpr n1 (open_obind_wrt_aexpr_rec n1 e1 ob1).
Proof.
pose proof degree_obind_wrt_aexpr_open_obind_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_obind_wrt_aexpr_open_obind_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_aexpr_open_work_wrt_aexpr_rec_degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_rec_mutual :
(forall w1 e1 n1,
  degree_work_wrt_aexpr (S n1) w1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_work_wrt_aexpr n1 (open_work_wrt_aexpr_rec n1 e1 w1)) /\
(forall wl1 e1 n1,
  degree_worklist_wrt_aexpr (S n1) wl1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_worklist_wrt_aexpr n1 (open_worklist_wrt_aexpr_rec n1 e1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_aexpr_open_work_wrt_aexpr_rec :
forall w1 e1 n1,
  degree_work_wrt_aexpr (S n1) w1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_work_wrt_aexpr n1 (open_work_wrt_aexpr_rec n1 e1 w1).
Proof.
pose proof degree_work_wrt_aexpr_open_work_wrt_aexpr_rec_degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_work_wrt_aexpr_open_work_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_rec :
forall wl1 e1 n1,
  degree_worklist_wrt_aexpr (S n1) wl1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_worklist_wrt_aexpr n1 (open_worklist_wrt_aexpr_rec n1 e1 wl1).
Proof.
pose proof degree_work_wrt_aexpr_open_work_wrt_aexpr_rec_degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_rec : lngen.

(* end hide *)

Lemma degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr :
forall e1 e2,
  degree_aexpr_wrt_aexpr 1 e1 ->
  degree_aexpr_wrt_aexpr 0 e2 ->
  degree_aexpr_wrt_aexpr 0 (open_aexpr_wrt_aexpr e1 e2).
Proof.
unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr : lngen.

Lemma degree_abody_wrt_aexpr_open_abody_wrt_aexpr :
forall ab1 e1,
  degree_abody_wrt_aexpr 1 ab1 ->
  degree_aexpr_wrt_aexpr 0 e1 ->
  degree_abody_wrt_aexpr 0 (open_abody_wrt_aexpr ab1 e1).
Proof.
unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_abody_wrt_aexpr_open_abody_wrt_aexpr : lngen.

Lemma degree_binding_wrt_aexpr_open_binding_wrt_aexpr :
forall b1 e1,
  degree_binding_wrt_aexpr 1 b1 ->
  degree_aexpr_wrt_aexpr 0 e1 ->
  degree_binding_wrt_aexpr 0 (open_binding_wrt_aexpr b1 e1).
Proof.
unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_binding_wrt_aexpr_open_binding_wrt_aexpr : lngen.

Lemma degree_obind_wrt_aexpr_open_obind_wrt_aexpr :
forall ob1 e1,
  degree_obind_wrt_aexpr 1 ob1 ->
  degree_aexpr_wrt_aexpr 0 e1 ->
  degree_obind_wrt_aexpr 0 (open_obind_wrt_aexpr ob1 e1).
Proof.
unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_obind_wrt_aexpr_open_obind_wrt_aexpr : lngen.

Lemma degree_work_wrt_aexpr_open_work_wrt_aexpr :
forall w1 e1,
  degree_work_wrt_aexpr 1 w1 ->
  degree_aexpr_wrt_aexpr 0 e1 ->
  degree_work_wrt_aexpr 0 (open_work_wrt_aexpr w1 e1).
Proof.
unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_work_wrt_aexpr_open_work_wrt_aexpr : lngen.

Lemma degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr :
forall wl1 e1,
  degree_worklist_wrt_aexpr 1 wl1 ->
  degree_aexpr_wrt_aexpr 0 e1 ->
  degree_worklist_wrt_aexpr 0 (open_worklist_wrt_aexpr wl1 e1).
Proof.
unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr : lngen.

(* begin hide *)

Lemma degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_rec_inv_degree_abody_wrt_aexpr_open_abody_wrt_aexpr_rec_inv_mutual :
(forall e1 e2 n1,
  degree_aexpr_wrt_aexpr n1 (open_aexpr_wrt_aexpr_rec n1 e2 e1) ->
  degree_aexpr_wrt_aexpr (S n1) e1) /\
(forall ab1 e1 n1,
  degree_abody_wrt_aexpr n1 (open_abody_wrt_aexpr_rec n1 e1 ab1) ->
  degree_abody_wrt_aexpr (S n1) ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_rec_inv :
forall e1 e2 n1,
  degree_aexpr_wrt_aexpr n1 (open_aexpr_wrt_aexpr_rec n1 e2 e1) ->
  degree_aexpr_wrt_aexpr (S n1) e1.
Proof.
pose proof degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_rec_inv_degree_abody_wrt_aexpr_open_abody_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexpr_open_abody_wrt_aexpr_rec_inv :
forall ab1 e1 n1,
  degree_abody_wrt_aexpr n1 (open_abody_wrt_aexpr_rec n1 e1 ab1) ->
  degree_abody_wrt_aexpr (S n1) ab1.
Proof.
pose proof degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_rec_inv_degree_abody_wrt_aexpr_open_abody_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_abody_wrt_aexpr_open_abody_wrt_aexpr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_aexpr_open_binding_wrt_aexpr_rec_inv_mutual :
(forall b1 e1 n1,
  degree_binding_wrt_aexpr n1 (open_binding_wrt_aexpr_rec n1 e1 b1) ->
  degree_binding_wrt_aexpr (S n1) b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_aexpr_open_binding_wrt_aexpr_rec_inv :
forall b1 e1 n1,
  degree_binding_wrt_aexpr n1 (open_binding_wrt_aexpr_rec n1 e1 b1) ->
  degree_binding_wrt_aexpr (S n1) b1.
Proof.
pose proof degree_binding_wrt_aexpr_open_binding_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_binding_wrt_aexpr_open_binding_wrt_aexpr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_obind_wrt_aexpr_open_obind_wrt_aexpr_rec_inv_mutual :
(forall ob1 e1 n1,
  degree_obind_wrt_aexpr n1 (open_obind_wrt_aexpr_rec n1 e1 ob1) ->
  degree_obind_wrt_aexpr (S n1) ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_obind_wrt_aexpr_open_obind_wrt_aexpr_rec_inv :
forall ob1 e1 n1,
  degree_obind_wrt_aexpr n1 (open_obind_wrt_aexpr_rec n1 e1 ob1) ->
  degree_obind_wrt_aexpr (S n1) ob1.
Proof.
pose proof degree_obind_wrt_aexpr_open_obind_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_obind_wrt_aexpr_open_obind_wrt_aexpr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_aexpr_open_work_wrt_aexpr_rec_inv_degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_rec_inv_mutual :
(forall w1 e1 n1,
  degree_work_wrt_aexpr n1 (open_work_wrt_aexpr_rec n1 e1 w1) ->
  degree_work_wrt_aexpr (S n1) w1) /\
(forall wl1 e1 n1,
  degree_worklist_wrt_aexpr n1 (open_worklist_wrt_aexpr_rec n1 e1 wl1) ->
  degree_worklist_wrt_aexpr (S n1) wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_aexpr_open_work_wrt_aexpr_rec_inv :
forall w1 e1 n1,
  degree_work_wrt_aexpr n1 (open_work_wrt_aexpr_rec n1 e1 w1) ->
  degree_work_wrt_aexpr (S n1) w1.
Proof.
pose proof degree_work_wrt_aexpr_open_work_wrt_aexpr_rec_inv_degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_work_wrt_aexpr_open_work_wrt_aexpr_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_rec_inv :
forall wl1 e1 n1,
  degree_worklist_wrt_aexpr n1 (open_worklist_wrt_aexpr_rec n1 e1 wl1) ->
  degree_worklist_wrt_aexpr (S n1) wl1.
Proof.
pose proof degree_work_wrt_aexpr_open_work_wrt_aexpr_rec_inv_degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_rec_inv : lngen.

(* end hide *)

Lemma degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_inv :
forall e1 e2,
  degree_aexpr_wrt_aexpr 0 (open_aexpr_wrt_aexpr e1 e2) ->
  degree_aexpr_wrt_aexpr 1 e1.
Proof.
unfold open_aexpr_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr_inv : lngen.

Lemma degree_abody_wrt_aexpr_open_abody_wrt_aexpr_inv :
forall ab1 e1,
  degree_abody_wrt_aexpr 0 (open_abody_wrt_aexpr ab1 e1) ->
  degree_abody_wrt_aexpr 1 ab1.
Proof.
unfold open_abody_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_abody_wrt_aexpr_open_abody_wrt_aexpr_inv : lngen.

Lemma degree_binding_wrt_aexpr_open_binding_wrt_aexpr_inv :
forall b1 e1,
  degree_binding_wrt_aexpr 0 (open_binding_wrt_aexpr b1 e1) ->
  degree_binding_wrt_aexpr 1 b1.
Proof.
unfold open_binding_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_binding_wrt_aexpr_open_binding_wrt_aexpr_inv : lngen.

Lemma degree_obind_wrt_aexpr_open_obind_wrt_aexpr_inv :
forall ob1 e1,
  degree_obind_wrt_aexpr 0 (open_obind_wrt_aexpr ob1 e1) ->
  degree_obind_wrt_aexpr 1 ob1.
Proof.
unfold open_obind_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_obind_wrt_aexpr_open_obind_wrt_aexpr_inv : lngen.

Lemma degree_work_wrt_aexpr_open_work_wrt_aexpr_inv :
forall w1 e1,
  degree_work_wrt_aexpr 0 (open_work_wrt_aexpr w1 e1) ->
  degree_work_wrt_aexpr 1 w1.
Proof.
unfold open_work_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_work_wrt_aexpr_open_work_wrt_aexpr_inv : lngen.

Lemma degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_inv :
forall wl1 e1,
  degree_worklist_wrt_aexpr 0 (open_worklist_wrt_aexpr wl1 e1) ->
  degree_worklist_wrt_aexpr 1 wl1.
Proof.
unfold open_worklist_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate degree_worklist_wrt_aexpr_open_worklist_wrt_aexpr_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_aexpr_wrt_aexpr_rec_inj_close_abody_wrt_aexpr_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_aexpr_wrt_aexpr_rec n1 x1 e1 = close_aexpr_wrt_aexpr_rec n1 x1 e2 ->
  e1 = e2) /\
(forall ab1 ab2 x1 n1,
  close_abody_wrt_aexpr_rec n1 x1 ab1 = close_abody_wrt_aexpr_rec n1 x1 ab2 ->
  ab1 = ab2).
Proof.
apply_mutual_ind aexpr_abody_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_aexpr_wrt_aexpr_rec_inj :
forall e1 e2 x1 n1,
  close_aexpr_wrt_aexpr_rec n1 x1 e1 = close_aexpr_wrt_aexpr_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_aexpr_wrt_aexpr_rec_inj_close_abody_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_aexpr_wrt_aexpr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_aexpr_rec_inj :
forall ab1 ab2 x1 n1,
  close_abody_wrt_aexpr_rec n1 x1 ab1 = close_abody_wrt_aexpr_rec n1 x1 ab2 ->
  ab1 = ab2.
Proof.
pose proof close_aexpr_wrt_aexpr_rec_inj_close_abody_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_abody_wrt_aexpr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_aexpr_rec_inj_mutual :
(forall b1 b2 x1 n1,
  close_binding_wrt_aexpr_rec n1 x1 b1 = close_binding_wrt_aexpr_rec n1 x1 b2 ->
  b1 = b2).
Proof.
apply_mutual_ind binding_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_aexpr_rec_inj :
forall b1 b2 x1 n1,
  close_binding_wrt_aexpr_rec n1 x1 b1 = close_binding_wrt_aexpr_rec n1 x1 b2 ->
  b1 = b2.
Proof.
pose proof close_binding_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_binding_wrt_aexpr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_obind_wrt_aexpr_rec_inj_mutual :
(forall ob1 ob2 x1 n1,
  close_obind_wrt_aexpr_rec n1 x1 ob1 = close_obind_wrt_aexpr_rec n1 x1 ob2 ->
  ob1 = ob2).
Proof.
apply_mutual_ind obind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_obind_wrt_aexpr_rec_inj :
forall ob1 ob2 x1 n1,
  close_obind_wrt_aexpr_rec n1 x1 ob1 = close_obind_wrt_aexpr_rec n1 x1 ob2 ->
  ob1 = ob2.
Proof.
pose proof close_obind_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_obind_wrt_aexpr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_aexpr_rec_inj_close_worklist_wrt_aexpr_rec_inj_mutual :
(forall w1 w2 x1 n1,
  close_work_wrt_aexpr_rec n1 x1 w1 = close_work_wrt_aexpr_rec n1 x1 w2 ->
  w1 = w2) /\
(forall wl1 wl2 x1 n1,
  close_worklist_wrt_aexpr_rec n1 x1 wl1 = close_worklist_wrt_aexpr_rec n1 x1 wl2 ->
  wl1 = wl2).
Proof.
apply_mutual_ind work_worklist_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_aexpr_rec_inj :
forall w1 w2 x1 n1,
  close_work_wrt_aexpr_rec n1 x1 w1 = close_work_wrt_aexpr_rec n1 x1 w2 ->
  w1 = w2.
Proof.
pose proof close_work_wrt_aexpr_rec_inj_close_worklist_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_work_wrt_aexpr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_worklist_wrt_aexpr_rec_inj :
forall wl1 wl2 x1 n1,
  close_worklist_wrt_aexpr_rec n1 x1 wl1 = close_worklist_wrt_aexpr_rec n1 x1 wl2 ->
  wl1 = wl2.
Proof.
pose proof close_work_wrt_aexpr_rec_inj_close_worklist_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_worklist_wrt_aexpr_rec_inj : lngen.

(* end hide *)

Lemma close_aexpr_wrt_aexpr_inj :
forall e1 e2 x1,
  close_aexpr_wrt_aexpr x1 e1 = close_aexpr_wrt_aexpr x1 e2 ->
  e1 = e2.
Proof.
unfold close_aexpr_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate close_aexpr_wrt_aexpr_inj : lngen.

Lemma close_abody_wrt_aexpr_inj :
forall ab1 ab2 x1,
  close_abody_wrt_aexpr x1 ab1 = close_abody_wrt_aexpr x1 ab2 ->
  ab1 = ab2.
Proof.
unfold close_abody_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate close_abody_wrt_aexpr_inj : lngen.

Lemma close_binding_wrt_aexpr_inj :
forall b1 b2 x1,
  close_binding_wrt_aexpr x1 b1 = close_binding_wrt_aexpr x1 b2 ->
  b1 = b2.
Proof.
unfold close_binding_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate close_binding_wrt_aexpr_inj : lngen.

Lemma close_obind_wrt_aexpr_inj :
forall ob1 ob2 x1,
  close_obind_wrt_aexpr x1 ob1 = close_obind_wrt_aexpr x1 ob2 ->
  ob1 = ob2.
Proof.
unfold close_obind_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate close_obind_wrt_aexpr_inj : lngen.

Lemma close_work_wrt_aexpr_inj :
forall w1 w2 x1,
  close_work_wrt_aexpr x1 w1 = close_work_wrt_aexpr x1 w2 ->
  w1 = w2.
Proof.
unfold close_work_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate close_work_wrt_aexpr_inj : lngen.

Lemma close_worklist_wrt_aexpr_inj :
forall wl1 wl2 x1,
  close_worklist_wrt_aexpr x1 wl1 = close_worklist_wrt_aexpr x1 wl2 ->
  wl1 = wl2.
Proof.
unfold close_worklist_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate close_worklist_wrt_aexpr_inj : lngen.

(* begin hide *)

Lemma close_aexpr_wrt_aexpr_rec_open_aexpr_wrt_aexpr_rec_close_abody_wrt_aexpr_rec_open_abody_wrt_aexpr_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_aexpr e1 ->
  close_aexpr_wrt_aexpr_rec n1 x1 (open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) e1) = e1) /\
(forall ab1 x1 n1,
  x1 `notin` fv_abody ab1 ->
  close_abody_wrt_aexpr_rec n1 x1 (open_abody_wrt_aexpr_rec n1 (ae_var_f x1) ab1) = ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_aexpr_wrt_aexpr_rec_open_aexpr_wrt_aexpr_rec :
forall e1 x1 n1,
  x1 `notin` fv_aexpr e1 ->
  close_aexpr_wrt_aexpr_rec n1 x1 (open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) e1) = e1.
Proof.
pose proof close_aexpr_wrt_aexpr_rec_open_aexpr_wrt_aexpr_rec_close_abody_wrt_aexpr_rec_open_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_aexpr_wrt_aexpr_rec_open_aexpr_wrt_aexpr_rec : lngen.
Hint Rewrite close_aexpr_wrt_aexpr_rec_open_aexpr_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_aexpr_rec_open_abody_wrt_aexpr_rec :
forall ab1 x1 n1,
  x1 `notin` fv_abody ab1 ->
  close_abody_wrt_aexpr_rec n1 x1 (open_abody_wrt_aexpr_rec n1 (ae_var_f x1) ab1) = ab1.
Proof.
pose proof close_aexpr_wrt_aexpr_rec_open_aexpr_wrt_aexpr_rec_close_abody_wrt_aexpr_rec_open_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_abody_wrt_aexpr_rec_open_abody_wrt_aexpr_rec : lngen.
Hint Rewrite close_abody_wrt_aexpr_rec_open_abody_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_aexpr_rec_open_binding_wrt_aexpr_rec_mutual :
(forall b1 x1 n1,
  x1 `notin` fv_binding b1 ->
  close_binding_wrt_aexpr_rec n1 x1 (open_binding_wrt_aexpr_rec n1 (ae_var_f x1) b1) = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_aexpr_rec_open_binding_wrt_aexpr_rec :
forall b1 x1 n1,
  x1 `notin` fv_binding b1 ->
  close_binding_wrt_aexpr_rec n1 x1 (open_binding_wrt_aexpr_rec n1 (ae_var_f x1) b1) = b1.
Proof.
pose proof close_binding_wrt_aexpr_rec_open_binding_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_binding_wrt_aexpr_rec_open_binding_wrt_aexpr_rec : lngen.
Hint Rewrite close_binding_wrt_aexpr_rec_open_binding_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_obind_wrt_aexpr_rec_open_obind_wrt_aexpr_rec_mutual :
(forall ob1 x1 n1,
  x1 `notin` fv_obind ob1 ->
  close_obind_wrt_aexpr_rec n1 x1 (open_obind_wrt_aexpr_rec n1 (ae_var_f x1) ob1) = ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_obind_wrt_aexpr_rec_open_obind_wrt_aexpr_rec :
forall ob1 x1 n1,
  x1 `notin` fv_obind ob1 ->
  close_obind_wrt_aexpr_rec n1 x1 (open_obind_wrt_aexpr_rec n1 (ae_var_f x1) ob1) = ob1.
Proof.
pose proof close_obind_wrt_aexpr_rec_open_obind_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_obind_wrt_aexpr_rec_open_obind_wrt_aexpr_rec : lngen.
Hint Rewrite close_obind_wrt_aexpr_rec_open_obind_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_aexpr_rec_open_work_wrt_aexpr_rec_close_worklist_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec_mutual :
(forall w1 x1 n1,
  x1 `notin` fv_work w1 ->
  close_work_wrt_aexpr_rec n1 x1 (open_work_wrt_aexpr_rec n1 (ae_var_f x1) w1) = w1) /\
(forall wl1 x1 n1,
  x1 `notin` fv_worklist wl1 ->
  close_worklist_wrt_aexpr_rec n1 x1 (open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) wl1) = wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_aexpr_rec_open_work_wrt_aexpr_rec :
forall w1 x1 n1,
  x1 `notin` fv_work w1 ->
  close_work_wrt_aexpr_rec n1 x1 (open_work_wrt_aexpr_rec n1 (ae_var_f x1) w1) = w1.
Proof.
pose proof close_work_wrt_aexpr_rec_open_work_wrt_aexpr_rec_close_worklist_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_work_wrt_aexpr_rec_open_work_wrt_aexpr_rec : lngen.
Hint Rewrite close_work_wrt_aexpr_rec_open_work_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_worklist_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec :
forall wl1 x1 n1,
  x1 `notin` fv_worklist wl1 ->
  close_worklist_wrt_aexpr_rec n1 x1 (open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) wl1) = wl1.
Proof.
pose proof close_work_wrt_aexpr_rec_open_work_wrt_aexpr_rec_close_worklist_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_worklist_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec : lngen.
Hint Rewrite close_worklist_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr :
forall e1 x1,
  x1 `notin` fv_aexpr e1 ->
  close_aexpr_wrt_aexpr x1 (open_aexpr_wrt_aexpr e1 (ae_var_f x1)) = e1.
Proof.
unfold close_aexpr_wrt_aexpr; unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr : lngen.
Hint Rewrite close_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr using solve [auto] : lngen.

Lemma close_abody_wrt_aexpr_open_abody_wrt_aexpr :
forall ab1 x1,
  x1 `notin` fv_abody ab1 ->
  close_abody_wrt_aexpr x1 (open_abody_wrt_aexpr ab1 (ae_var_f x1)) = ab1.
Proof.
unfold close_abody_wrt_aexpr; unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_abody_wrt_aexpr_open_abody_wrt_aexpr : lngen.
Hint Rewrite close_abody_wrt_aexpr_open_abody_wrt_aexpr using solve [auto] : lngen.

Lemma close_binding_wrt_aexpr_open_binding_wrt_aexpr :
forall b1 x1,
  x1 `notin` fv_binding b1 ->
  close_binding_wrt_aexpr x1 (open_binding_wrt_aexpr b1 (ae_var_f x1)) = b1.
Proof.
unfold close_binding_wrt_aexpr; unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_binding_wrt_aexpr_open_binding_wrt_aexpr : lngen.
Hint Rewrite close_binding_wrt_aexpr_open_binding_wrt_aexpr using solve [auto] : lngen.

Lemma close_obind_wrt_aexpr_open_obind_wrt_aexpr :
forall ob1 x1,
  x1 `notin` fv_obind ob1 ->
  close_obind_wrt_aexpr x1 (open_obind_wrt_aexpr ob1 (ae_var_f x1)) = ob1.
Proof.
unfold close_obind_wrt_aexpr; unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_obind_wrt_aexpr_open_obind_wrt_aexpr : lngen.
Hint Rewrite close_obind_wrt_aexpr_open_obind_wrt_aexpr using solve [auto] : lngen.

Lemma close_work_wrt_aexpr_open_work_wrt_aexpr :
forall w1 x1,
  x1 `notin` fv_work w1 ->
  close_work_wrt_aexpr x1 (open_work_wrt_aexpr w1 (ae_var_f x1)) = w1.
Proof.
unfold close_work_wrt_aexpr; unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_work_wrt_aexpr_open_work_wrt_aexpr : lngen.
Hint Rewrite close_work_wrt_aexpr_open_work_wrt_aexpr using solve [auto] : lngen.

Lemma close_worklist_wrt_aexpr_open_worklist_wrt_aexpr :
forall wl1 x1,
  x1 `notin` fv_worklist wl1 ->
  close_worklist_wrt_aexpr x1 (open_worklist_wrt_aexpr wl1 (ae_var_f x1)) = wl1.
Proof.
unfold close_worklist_wrt_aexpr; unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_worklist_wrt_aexpr_open_worklist_wrt_aexpr : lngen.
Hint Rewrite close_worklist_wrt_aexpr_open_worklist_wrt_aexpr using solve [auto] : lngen.

(* begin hide *)

Lemma open_aexpr_wrt_aexpr_rec_close_aexpr_wrt_aexpr_rec_open_abody_wrt_aexpr_rec_close_abody_wrt_aexpr_rec_mutual :
(forall e1 x1 n1,
  open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) (close_aexpr_wrt_aexpr_rec n1 x1 e1) = e1) /\
(forall ab1 x1 n1,
  open_abody_wrt_aexpr_rec n1 (ae_var_f x1) (close_abody_wrt_aexpr_rec n1 x1 ab1) = ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_aexpr_wrt_aexpr_rec_close_aexpr_wrt_aexpr_rec :
forall e1 x1 n1,
  open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) (close_aexpr_wrt_aexpr_rec n1 x1 e1) = e1.
Proof.
pose proof open_aexpr_wrt_aexpr_rec_close_aexpr_wrt_aexpr_rec_open_abody_wrt_aexpr_rec_close_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_aexpr_wrt_aexpr_rec_close_aexpr_wrt_aexpr_rec : lngen.
Hint Rewrite open_aexpr_wrt_aexpr_rec_close_aexpr_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_aexpr_rec_close_abody_wrt_aexpr_rec :
forall ab1 x1 n1,
  open_abody_wrt_aexpr_rec n1 (ae_var_f x1) (close_abody_wrt_aexpr_rec n1 x1 ab1) = ab1.
Proof.
pose proof open_aexpr_wrt_aexpr_rec_close_aexpr_wrt_aexpr_rec_open_abody_wrt_aexpr_rec_close_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_abody_wrt_aexpr_rec_close_abody_wrt_aexpr_rec : lngen.
Hint Rewrite open_abody_wrt_aexpr_rec_close_abody_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_aexpr_rec_close_binding_wrt_aexpr_rec_mutual :
(forall b1 x1 n1,
  open_binding_wrt_aexpr_rec n1 (ae_var_f x1) (close_binding_wrt_aexpr_rec n1 x1 b1) = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_aexpr_rec_close_binding_wrt_aexpr_rec :
forall b1 x1 n1,
  open_binding_wrt_aexpr_rec n1 (ae_var_f x1) (close_binding_wrt_aexpr_rec n1 x1 b1) = b1.
Proof.
pose proof open_binding_wrt_aexpr_rec_close_binding_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_binding_wrt_aexpr_rec_close_binding_wrt_aexpr_rec : lngen.
Hint Rewrite open_binding_wrt_aexpr_rec_close_binding_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_obind_wrt_aexpr_rec_close_obind_wrt_aexpr_rec_mutual :
(forall ob1 x1 n1,
  open_obind_wrt_aexpr_rec n1 (ae_var_f x1) (close_obind_wrt_aexpr_rec n1 x1 ob1) = ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_obind_wrt_aexpr_rec_close_obind_wrt_aexpr_rec :
forall ob1 x1 n1,
  open_obind_wrt_aexpr_rec n1 (ae_var_f x1) (close_obind_wrt_aexpr_rec n1 x1 ob1) = ob1.
Proof.
pose proof open_obind_wrt_aexpr_rec_close_obind_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_obind_wrt_aexpr_rec_close_obind_wrt_aexpr_rec : lngen.
Hint Rewrite open_obind_wrt_aexpr_rec_close_obind_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_aexpr_rec_close_work_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec_close_worklist_wrt_aexpr_rec_mutual :
(forall w1 x1 n1,
  open_work_wrt_aexpr_rec n1 (ae_var_f x1) (close_work_wrt_aexpr_rec n1 x1 w1) = w1) /\
(forall wl1 x1 n1,
  open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) (close_worklist_wrt_aexpr_rec n1 x1 wl1) = wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_aexpr_rec_close_work_wrt_aexpr_rec :
forall w1 x1 n1,
  open_work_wrt_aexpr_rec n1 (ae_var_f x1) (close_work_wrt_aexpr_rec n1 x1 w1) = w1.
Proof.
pose proof open_work_wrt_aexpr_rec_close_work_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec_close_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_work_wrt_aexpr_rec_close_work_wrt_aexpr_rec : lngen.
Hint Rewrite open_work_wrt_aexpr_rec_close_work_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_worklist_wrt_aexpr_rec_close_worklist_wrt_aexpr_rec :
forall wl1 x1 n1,
  open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) (close_worklist_wrt_aexpr_rec n1 x1 wl1) = wl1.
Proof.
pose proof open_work_wrt_aexpr_rec_close_work_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec_close_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_worklist_wrt_aexpr_rec_close_worklist_wrt_aexpr_rec : lngen.
Hint Rewrite open_worklist_wrt_aexpr_rec_close_worklist_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr :
forall e1 x1,
  open_aexpr_wrt_aexpr (close_aexpr_wrt_aexpr x1 e1) (ae_var_f x1) = e1.
Proof.
unfold close_aexpr_wrt_aexpr; unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr : lngen.
Hint Rewrite open_aexpr_wrt_aexpr_close_aexpr_wrt_aexpr using solve [auto] : lngen.

Lemma open_abody_wrt_aexpr_close_abody_wrt_aexpr :
forall ab1 x1,
  open_abody_wrt_aexpr (close_abody_wrt_aexpr x1 ab1) (ae_var_f x1) = ab1.
Proof.
unfold close_abody_wrt_aexpr; unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_abody_wrt_aexpr_close_abody_wrt_aexpr : lngen.
Hint Rewrite open_abody_wrt_aexpr_close_abody_wrt_aexpr using solve [auto] : lngen.

Lemma open_binding_wrt_aexpr_close_binding_wrt_aexpr :
forall b1 x1,
  open_binding_wrt_aexpr (close_binding_wrt_aexpr x1 b1) (ae_var_f x1) = b1.
Proof.
unfold close_binding_wrt_aexpr; unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_binding_wrt_aexpr_close_binding_wrt_aexpr : lngen.
Hint Rewrite open_binding_wrt_aexpr_close_binding_wrt_aexpr using solve [auto] : lngen.

Lemma open_obind_wrt_aexpr_close_obind_wrt_aexpr :
forall ob1 x1,
  open_obind_wrt_aexpr (close_obind_wrt_aexpr x1 ob1) (ae_var_f x1) = ob1.
Proof.
unfold close_obind_wrt_aexpr; unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_obind_wrt_aexpr_close_obind_wrt_aexpr : lngen.
Hint Rewrite open_obind_wrt_aexpr_close_obind_wrt_aexpr using solve [auto] : lngen.

Lemma open_work_wrt_aexpr_close_work_wrt_aexpr :
forall w1 x1,
  open_work_wrt_aexpr (close_work_wrt_aexpr x1 w1) (ae_var_f x1) = w1.
Proof.
unfold close_work_wrt_aexpr; unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_work_wrt_aexpr_close_work_wrt_aexpr : lngen.
Hint Rewrite open_work_wrt_aexpr_close_work_wrt_aexpr using solve [auto] : lngen.

Lemma open_worklist_wrt_aexpr_close_worklist_wrt_aexpr :
forall wl1 x1,
  open_worklist_wrt_aexpr (close_worklist_wrt_aexpr x1 wl1) (ae_var_f x1) = wl1.
Proof.
unfold close_worklist_wrt_aexpr; unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_worklist_wrt_aexpr_close_worklist_wrt_aexpr : lngen.
Hint Rewrite open_worklist_wrt_aexpr_close_worklist_wrt_aexpr using solve [auto] : lngen.

(* begin hide *)

Lemma open_aexpr_wrt_aexpr_rec_inj_open_abody_wrt_aexpr_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_aexpr e2 ->
  x1 `notin` fv_aexpr e1 ->
  open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) e2 = open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) e1 ->
  e2 = e1) /\
(forall ab2 ab1 x1 n1,
  x1 `notin` fv_abody ab2 ->
  x1 `notin` fv_abody ab1 ->
  open_abody_wrt_aexpr_rec n1 (ae_var_f x1) ab2 = open_abody_wrt_aexpr_rec n1 (ae_var_f x1) ab1 ->
  ab2 = ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_aexpr_wrt_aexpr_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_aexpr e2 ->
  x1 `notin` fv_aexpr e1 ->
  open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) e2 = open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_aexpr_wrt_aexpr_rec_inj_open_abody_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_aexpr_wrt_aexpr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_aexpr_rec_inj :
forall ab2 ab1 x1 n1,
  x1 `notin` fv_abody ab2 ->
  x1 `notin` fv_abody ab1 ->
  open_abody_wrt_aexpr_rec n1 (ae_var_f x1) ab2 = open_abody_wrt_aexpr_rec n1 (ae_var_f x1) ab1 ->
  ab2 = ab1.
Proof.
pose proof open_aexpr_wrt_aexpr_rec_inj_open_abody_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_abody_wrt_aexpr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_aexpr_rec_inj_mutual :
(forall b2 b1 x1 n1,
  x1 `notin` fv_binding b2 ->
  x1 `notin` fv_binding b1 ->
  open_binding_wrt_aexpr_rec n1 (ae_var_f x1) b2 = open_binding_wrt_aexpr_rec n1 (ae_var_f x1) b1 ->
  b2 = b1).
Proof.
apply_mutual_ind binding_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_aexpr_rec_inj :
forall b2 b1 x1 n1,
  x1 `notin` fv_binding b2 ->
  x1 `notin` fv_binding b1 ->
  open_binding_wrt_aexpr_rec n1 (ae_var_f x1) b2 = open_binding_wrt_aexpr_rec n1 (ae_var_f x1) b1 ->
  b2 = b1.
Proof.
pose proof open_binding_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_binding_wrt_aexpr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_obind_wrt_aexpr_rec_inj_mutual :
(forall ob2 ob1 x1 n1,
  x1 `notin` fv_obind ob2 ->
  x1 `notin` fv_obind ob1 ->
  open_obind_wrt_aexpr_rec n1 (ae_var_f x1) ob2 = open_obind_wrt_aexpr_rec n1 (ae_var_f x1) ob1 ->
  ob2 = ob1).
Proof.
apply_mutual_ind obind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_obind_wrt_aexpr_rec_inj :
forall ob2 ob1 x1 n1,
  x1 `notin` fv_obind ob2 ->
  x1 `notin` fv_obind ob1 ->
  open_obind_wrt_aexpr_rec n1 (ae_var_f x1) ob2 = open_obind_wrt_aexpr_rec n1 (ae_var_f x1) ob1 ->
  ob2 = ob1.
Proof.
pose proof open_obind_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_obind_wrt_aexpr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_aexpr_rec_inj_open_worklist_wrt_aexpr_rec_inj_mutual :
(forall w2 w1 x1 n1,
  x1 `notin` fv_work w2 ->
  x1 `notin` fv_work w1 ->
  open_work_wrt_aexpr_rec n1 (ae_var_f x1) w2 = open_work_wrt_aexpr_rec n1 (ae_var_f x1) w1 ->
  w2 = w1) /\
(forall wl2 wl1 x1 n1,
  x1 `notin` fv_worklist wl2 ->
  x1 `notin` fv_worklist wl1 ->
  open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) wl2 = open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) wl1 ->
  wl2 = wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_aexpr_rec_inj :
forall w2 w1 x1 n1,
  x1 `notin` fv_work w2 ->
  x1 `notin` fv_work w1 ->
  open_work_wrt_aexpr_rec n1 (ae_var_f x1) w2 = open_work_wrt_aexpr_rec n1 (ae_var_f x1) w1 ->
  w2 = w1.
Proof.
pose proof open_work_wrt_aexpr_rec_inj_open_worklist_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_work_wrt_aexpr_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_worklist_wrt_aexpr_rec_inj :
forall wl2 wl1 x1 n1,
  x1 `notin` fv_worklist wl2 ->
  x1 `notin` fv_worklist wl1 ->
  open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) wl2 = open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) wl1 ->
  wl2 = wl1.
Proof.
pose proof open_work_wrt_aexpr_rec_inj_open_worklist_wrt_aexpr_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_worklist_wrt_aexpr_rec_inj : lngen.

(* end hide *)

Lemma open_aexpr_wrt_aexpr_inj :
forall e2 e1 x1,
  x1 `notin` fv_aexpr e2 ->
  x1 `notin` fv_aexpr e1 ->
  open_aexpr_wrt_aexpr e2 (ae_var_f x1) = open_aexpr_wrt_aexpr e1 (ae_var_f x1) ->
  e2 = e1.
Proof.
unfold open_aexpr_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate open_aexpr_wrt_aexpr_inj : lngen.

Lemma open_abody_wrt_aexpr_inj :
forall ab2 ab1 x1,
  x1 `notin` fv_abody ab2 ->
  x1 `notin` fv_abody ab1 ->
  open_abody_wrt_aexpr ab2 (ae_var_f x1) = open_abody_wrt_aexpr ab1 (ae_var_f x1) ->
  ab2 = ab1.
Proof.
unfold open_abody_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate open_abody_wrt_aexpr_inj : lngen.

Lemma open_binding_wrt_aexpr_inj :
forall b2 b1 x1,
  x1 `notin` fv_binding b2 ->
  x1 `notin` fv_binding b1 ->
  open_binding_wrt_aexpr b2 (ae_var_f x1) = open_binding_wrt_aexpr b1 (ae_var_f x1) ->
  b2 = b1.
Proof.
unfold open_binding_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate open_binding_wrt_aexpr_inj : lngen.

Lemma open_obind_wrt_aexpr_inj :
forall ob2 ob1 x1,
  x1 `notin` fv_obind ob2 ->
  x1 `notin` fv_obind ob1 ->
  open_obind_wrt_aexpr ob2 (ae_var_f x1) = open_obind_wrt_aexpr ob1 (ae_var_f x1) ->
  ob2 = ob1.
Proof.
unfold open_obind_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate open_obind_wrt_aexpr_inj : lngen.

Lemma open_work_wrt_aexpr_inj :
forall w2 w1 x1,
  x1 `notin` fv_work w2 ->
  x1 `notin` fv_work w1 ->
  open_work_wrt_aexpr w2 (ae_var_f x1) = open_work_wrt_aexpr w1 (ae_var_f x1) ->
  w2 = w1.
Proof.
unfold open_work_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate open_work_wrt_aexpr_inj : lngen.

Lemma open_worklist_wrt_aexpr_inj :
forall wl2 wl1 x1,
  x1 `notin` fv_worklist wl2 ->
  x1 `notin` fv_worklist wl1 ->
  open_worklist_wrt_aexpr wl2 (ae_var_f x1) = open_worklist_wrt_aexpr wl1 (ae_var_f x1) ->
  wl2 = wl1.
Proof.
unfold open_worklist_wrt_aexpr; eauto with lngen.
Qed.

Hint Immediate open_worklist_wrt_aexpr_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_aexpr_wrt_aexpr_of_lc_aexpr_degree_abody_wrt_aexpr_of_lc_abody_mutual :
(forall e1,
  lc_aexpr e1 ->
  degree_aexpr_wrt_aexpr 0 e1) /\
(forall ab1,
  lc_abody ab1 ->
  degree_abody_wrt_aexpr 0 ab1).
Proof.
apply_mutual_ind lc_aexpr_lc_abody_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_aexpr_wrt_aexpr_of_lc_aexpr :
forall e1,
  lc_aexpr e1 ->
  degree_aexpr_wrt_aexpr 0 e1.
Proof.
pose proof degree_aexpr_wrt_aexpr_of_lc_aexpr_degree_abody_wrt_aexpr_of_lc_abody_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_aexpr_wrt_aexpr_of_lc_aexpr : lngen.

Lemma degree_abody_wrt_aexpr_of_lc_abody :
forall ab1,
  lc_abody ab1 ->
  degree_abody_wrt_aexpr 0 ab1.
Proof.
pose proof degree_aexpr_wrt_aexpr_of_lc_aexpr_degree_abody_wrt_aexpr_of_lc_abody_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_abody_wrt_aexpr_of_lc_abody : lngen.

(* begin hide *)

Lemma degree_binding_wrt_aexpr_of_lc_binding_mutual :
(forall b1,
  lc_binding b1 ->
  degree_binding_wrt_aexpr 0 b1).
Proof.
apply_mutual_ind lc_binding_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_binding_wrt_aexpr_of_lc_binding :
forall b1,
  lc_binding b1 ->
  degree_binding_wrt_aexpr 0 b1.
Proof.
pose proof degree_binding_wrt_aexpr_of_lc_binding_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_binding_wrt_aexpr_of_lc_binding : lngen.

(* begin hide *)

Lemma degree_obind_wrt_aexpr_of_lc_obind_mutual :
(forall ob1,
  lc_obind ob1 ->
  degree_obind_wrt_aexpr 0 ob1).
Proof.
apply_mutual_ind lc_obind_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_obind_wrt_aexpr_of_lc_obind :
forall ob1,
  lc_obind ob1 ->
  degree_obind_wrt_aexpr 0 ob1.
Proof.
pose proof degree_obind_wrt_aexpr_of_lc_obind_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_obind_wrt_aexpr_of_lc_obind : lngen.

(* begin hide *)

Lemma degree_work_wrt_aexpr_of_lc_work_degree_worklist_wrt_aexpr_of_lc_worklist_mutual :
(forall w1,
  lc_work w1 ->
  degree_work_wrt_aexpr 0 w1) /\
(forall wl1,
  lc_worklist wl1 ->
  degree_worklist_wrt_aexpr 0 wl1).
Proof.
apply_mutual_ind lc_work_lc_worklist_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_work_wrt_aexpr_of_lc_work :
forall w1,
  lc_work w1 ->
  degree_work_wrt_aexpr 0 w1.
Proof.
pose proof degree_work_wrt_aexpr_of_lc_work_degree_worklist_wrt_aexpr_of_lc_worklist_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_work_wrt_aexpr_of_lc_work : lngen.

Lemma degree_worklist_wrt_aexpr_of_lc_worklist :
forall wl1,
  lc_worklist wl1 ->
  degree_worklist_wrt_aexpr 0 wl1.
Proof.
pose proof degree_work_wrt_aexpr_of_lc_work_degree_worklist_wrt_aexpr_of_lc_worklist_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_worklist_wrt_aexpr_of_lc_worklist : lngen.

(* begin hide *)

Lemma lc_aexpr_of_degree_lc_abody_of_degree_size_mutual :
forall i1,
(forall e1,
  size_aexpr e1 = i1 ->
  degree_aexpr_wrt_aexpr 0 e1 ->
  lc_aexpr e1) /\
(forall ab1,
  size_abody ab1 = i1 ->
  degree_abody_wrt_aexpr 0 ab1 ->
  lc_abody ab1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind aexpr_abody_mutind;
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

Lemma lc_aexpr_of_degree :
forall e1,
  degree_aexpr_wrt_aexpr 0 e1 ->
  lc_aexpr e1.
Proof.
intros e1; intros;
pose proof (lc_aexpr_of_degree_lc_abody_of_degree_size_mutual (size_aexpr e1));
intuition eauto.
Qed.

Hint Resolve lc_aexpr_of_degree : lngen.

Lemma lc_abody_of_degree :
forall ab1,
  degree_abody_wrt_aexpr 0 ab1 ->
  lc_abody ab1.
Proof.
intros ab1; intros;
pose proof (lc_aexpr_of_degree_lc_abody_of_degree_size_mutual (size_abody ab1));
intuition eauto.
Qed.

Hint Resolve lc_abody_of_degree : lngen.

(* begin hide *)

Lemma lc_binding_of_degree_size_mutual :
forall i1,
(forall b1,
  size_binding b1 = i1 ->
  degree_binding_wrt_aexpr 0 b1 ->
  lc_binding b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind binding_mutind;
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

Lemma lc_binding_of_degree :
forall b1,
  degree_binding_wrt_aexpr 0 b1 ->
  lc_binding b1.
Proof.
intros b1; intros;
pose proof (lc_binding_of_degree_size_mutual (size_binding b1));
intuition eauto.
Qed.

Hint Resolve lc_binding_of_degree : lngen.

(* begin hide *)

Lemma lc_obind_of_degree_size_mutual :
forall i1,
(forall ob1,
  size_obind ob1 = i1 ->
  degree_obind_wrt_aexpr 0 ob1 ->
  lc_obind ob1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind obind_mutind;
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

Lemma lc_obind_of_degree :
forall ob1,
  degree_obind_wrt_aexpr 0 ob1 ->
  lc_obind ob1.
Proof.
intros ob1; intros;
pose proof (lc_obind_of_degree_size_mutual (size_obind ob1));
intuition eauto.
Qed.

Hint Resolve lc_obind_of_degree : lngen.

(* begin hide *)

Lemma lc_work_of_degree_lc_worklist_of_degree_size_mutual :
forall i1,
(forall w1,
  size_work w1 = i1 ->
  degree_work_wrt_aexpr 0 w1 ->
  lc_work w1) /\
(forall wl1,
  size_worklist wl1 = i1 ->
  degree_worklist_wrt_aexpr 0 wl1 ->
  lc_worklist wl1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind work_worklist_mutind;
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

Lemma lc_work_of_degree :
forall w1,
  degree_work_wrt_aexpr 0 w1 ->
  lc_work w1.
Proof.
intros w1; intros;
pose proof (lc_work_of_degree_lc_worklist_of_degree_size_mutual (size_work w1));
intuition eauto.
Qed.

Hint Resolve lc_work_of_degree : lngen.

Lemma lc_worklist_of_degree :
forall wl1,
  degree_worklist_wrt_aexpr 0 wl1 ->
  lc_worklist wl1.
Proof.
intros wl1; intros;
pose proof (lc_work_of_degree_lc_worklist_of_degree_size_mutual (size_worklist wl1));
intuition eauto.
Qed.

Hint Resolve lc_worklist_of_degree : lngen.

Ltac akind_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac aexpr_abody_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_aexpr_wrt_aexpr_of_lc_aexpr in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_abody_wrt_aexpr_of_lc_abody in J1; clear H
          end).

Ltac binding_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_binding_wrt_aexpr_of_lc_binding in J1; clear H
          end).

Ltac obind_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_obind_wrt_aexpr_of_lc_obind in J1; clear H
          end).

Ltac work_worklist_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_work_wrt_aexpr_of_lc_work in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_worklist_wrt_aexpr_of_lc_worklist in J1; clear H
          end).

Lemma lc_ae_abs_exists :
forall x1 A1 ab1,
  lc_aexpr A1 ->
  lc_abody (open_abody_wrt_aexpr ab1 (ae_var_f x1)) ->
  lc_aexpr (ae_abs A1 ab1).
Proof.
intros; aexpr_abody_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_ae_pi_exists :
forall x1 A1 B1,
  lc_aexpr A1 ->
  lc_aexpr (open_aexpr_wrt_aexpr B1 (ae_var_f x1)) ->
  lc_aexpr (ae_pi A1 B1).
Proof.
intros; aexpr_abody_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_ae_bind_exists :
forall x1 A1 ab1,
  lc_aexpr A1 ->
  lc_abody (open_abody_wrt_aexpr ab1 (ae_var_f x1)) ->
  lc_aexpr (ae_bind A1 ab1).
Proof.
intros; aexpr_abody_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_ae_all_exists :
forall x1 A1 B1,
  lc_aexpr A1 ->
  lc_aexpr (open_aexpr_wrt_aexpr B1 (ae_var_f x1)) ->
  lc_aexpr (ae_all A1 B1).
Proof.
intros; aexpr_abody_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_w_infer_exists :
forall x1 e1 e2 wl1,
  lc_aexpr e1 ->
  lc_aexpr e2 ->
  lc_worklist (open_worklist_wrt_aexpr wl1 (ae_var_f x1)) ->
  lc_work (w_infer e1 e2 wl1).
Proof.
intros; work_worklist_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_w_infer_app_exists :
forall x1 A1 e1 e2 wl1,
  lc_aexpr A1 ->
  lc_aexpr e1 ->
  lc_aexpr e2 ->
  lc_worklist (open_worklist_wrt_aexpr wl1 (ae_var_f x1)) ->
  lc_work (w_infer_app A1 e1 e2 wl1).
Proof.
intros; work_worklist_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_w_reduce_exists :
forall x1 e1 wl1,
  lc_aexpr e1 ->
  lc_worklist (open_worklist_wrt_aexpr wl1 (ae_var_f x1)) ->
  lc_work (w_reduce e1 wl1).
Proof.
intros; work_worklist_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_aexpr (ae_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_ae_abs_exists x1) : core.

Hint Extern 1 (lc_aexpr (ae_pi _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_ae_pi_exists x1) : core.

Hint Extern 1 (lc_aexpr (ae_bind _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_ae_bind_exists x1) : core.

Hint Extern 1 (lc_aexpr (ae_all _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_ae_all_exists x1) : core.

Hint Extern 1 (lc_work (w_infer _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_w_infer_exists x1) : core.

Hint Extern 1 (lc_work (w_infer_app _ _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_w_infer_app_exists x1) : core.

Hint Extern 1 (lc_work (w_reduce _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_w_reduce_exists x1) : core.

Lemma lc_body_aexpr_wrt_aexpr :
forall e1 e2,
  body_aexpr_wrt_aexpr e1 ->
  lc_aexpr e2 ->
  lc_aexpr (open_aexpr_wrt_aexpr e1 e2).
Proof.
unfold body_aexpr_wrt_aexpr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
aexpr_abody_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_aexpr_wrt_aexpr : lngen.

Lemma lc_body_abody_wrt_aexpr :
forall ab1 e1,
  body_abody_wrt_aexpr ab1 ->
  lc_aexpr e1 ->
  lc_abody (open_abody_wrt_aexpr ab1 e1).
Proof.
unfold body_abody_wrt_aexpr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
aexpr_abody_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_abody_wrt_aexpr : lngen.

Lemma lc_body_binding_wrt_aexpr :
forall b1 e1,
  body_binding_wrt_aexpr b1 ->
  lc_aexpr e1 ->
  lc_binding (open_binding_wrt_aexpr b1 e1).
Proof.
unfold body_binding_wrt_aexpr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
binding_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_binding_wrt_aexpr : lngen.

Lemma lc_body_obind_wrt_aexpr :
forall ob1 e1,
  body_obind_wrt_aexpr ob1 ->
  lc_aexpr e1 ->
  lc_obind (open_obind_wrt_aexpr ob1 e1).
Proof.
unfold body_obind_wrt_aexpr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
obind_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_obind_wrt_aexpr : lngen.

Lemma lc_body_work_wrt_aexpr :
forall w1 e1,
  body_work_wrt_aexpr w1 ->
  lc_aexpr e1 ->
  lc_work (open_work_wrt_aexpr w1 e1).
Proof.
unfold body_work_wrt_aexpr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
work_worklist_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_work_wrt_aexpr : lngen.

Lemma lc_body_worklist_wrt_aexpr :
forall wl1 e1,
  body_worklist_wrt_aexpr wl1 ->
  lc_aexpr e1 ->
  lc_worklist (open_worklist_wrt_aexpr wl1 e1).
Proof.
unfold body_worklist_wrt_aexpr;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
work_worklist_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_worklist_wrt_aexpr : lngen.

Lemma lc_body_ae_abs_2 :
forall A1 ab1,
  lc_aexpr (ae_abs A1 ab1) ->
  body_abody_wrt_aexpr ab1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_ae_abs_2 : lngen.

Lemma lc_body_ae_pi_2 :
forall A1 B1,
  lc_aexpr (ae_pi A1 B1) ->
  body_aexpr_wrt_aexpr B1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_ae_pi_2 : lngen.

Lemma lc_body_ae_bind_2 :
forall A1 ab1,
  lc_aexpr (ae_bind A1 ab1) ->
  body_abody_wrt_aexpr ab1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_ae_bind_2 : lngen.

Lemma lc_body_ae_all_2 :
forall A1 B1,
  lc_aexpr (ae_all A1 B1) ->
  body_aexpr_wrt_aexpr B1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_ae_all_2 : lngen.

Lemma lc_body_w_infer_3 :
forall e1 e2 wl1,
  lc_work (w_infer e1 e2 wl1) ->
  body_worklist_wrt_aexpr wl1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_w_infer_3 : lngen.

Lemma lc_body_w_infer_app_4 :
forall A1 e1 e2 wl1,
  lc_work (w_infer_app A1 e1 e2 wl1) ->
  body_worklist_wrt_aexpr wl1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_w_infer_app_4 : lngen.

Lemma lc_body_w_reduce_2 :
forall e1 wl1,
  lc_work (w_reduce e1 wl1) ->
  body_worklist_wrt_aexpr wl1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_w_reduce_2 : lngen.

(* begin hide *)

Lemma lc_aexpr_unique_lc_abody_unique_mutual :
(forall e1 (proof2 proof3 : lc_aexpr e1), proof2 = proof3) /\
(forall ab1 (proof2 proof3 : lc_abody ab1), proof2 = proof3).
Proof.
apply_mutual_ind lc_aexpr_lc_abody_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_aexpr_unique :
forall e1 (proof2 proof3 : lc_aexpr e1), proof2 = proof3.
Proof.
pose proof lc_aexpr_unique_lc_abody_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_aexpr_unique : lngen.

Lemma lc_abody_unique :
forall ab1 (proof2 proof3 : lc_abody ab1), proof2 = proof3.
Proof.
pose proof lc_aexpr_unique_lc_abody_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_abody_unique : lngen.

(* begin hide *)

Lemma lc_binding_unique_mutual :
(forall b1 (proof2 proof3 : lc_binding b1), proof2 = proof3).
Proof.
apply_mutual_ind lc_binding_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_binding_unique :
forall b1 (proof2 proof3 : lc_binding b1), proof2 = proof3.
Proof.
pose proof lc_binding_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_binding_unique : lngen.

(* begin hide *)

Lemma lc_obind_unique_mutual :
(forall ob1 (proof2 proof3 : lc_obind ob1), proof2 = proof3).
Proof.
apply_mutual_ind lc_obind_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_obind_unique :
forall ob1 (proof2 proof3 : lc_obind ob1), proof2 = proof3.
Proof.
pose proof lc_obind_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_obind_unique : lngen.

(* begin hide *)

Lemma lc_work_unique_lc_worklist_unique_mutual :
(forall w1 (proof2 proof3 : lc_work w1), proof2 = proof3) /\
(forall wl1 (proof2 proof3 : lc_worklist wl1), proof2 = proof3).
Proof.
apply_mutual_ind lc_work_lc_worklist_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_work_unique :
forall w1 (proof2 proof3 : lc_work w1), proof2 = proof3.
Proof.
pose proof lc_work_unique_lc_worklist_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_work_unique : lngen.

Lemma lc_worklist_unique :
forall wl1 (proof2 proof3 : lc_worklist wl1), proof2 = proof3.
Proof.
pose proof lc_work_unique_lc_worklist_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_worklist_unique : lngen.

(* begin hide *)

Lemma lc_aexpr_of_lc_set_aexpr_lc_abody_of_lc_set_abody_mutual :
(forall e1, lc_set_aexpr e1 -> lc_aexpr e1) /\
(forall ab1, lc_set_abody ab1 -> lc_abody ab1).
Proof.
apply_mutual_ind lc_set_aexpr_lc_set_abody_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_aexpr_of_lc_set_aexpr :
forall e1, lc_set_aexpr e1 -> lc_aexpr e1.
Proof.
pose proof lc_aexpr_of_lc_set_aexpr_lc_abody_of_lc_set_abody_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_aexpr_of_lc_set_aexpr : lngen.

Lemma lc_abody_of_lc_set_abody :
forall ab1, lc_set_abody ab1 -> lc_abody ab1.
Proof.
pose proof lc_aexpr_of_lc_set_aexpr_lc_abody_of_lc_set_abody_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_abody_of_lc_set_abody : lngen.

(* begin hide *)

Lemma lc_binding_of_lc_set_binding_mutual :
(forall b1, lc_set_binding b1 -> lc_binding b1).
Proof.
apply_mutual_ind lc_set_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_binding_of_lc_set_binding :
forall b1, lc_set_binding b1 -> lc_binding b1.
Proof.
pose proof lc_binding_of_lc_set_binding_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_binding_of_lc_set_binding : lngen.

(* begin hide *)

Lemma lc_obind_of_lc_set_obind_mutual :
(forall ob1, lc_set_obind ob1 -> lc_obind ob1).
Proof.
apply_mutual_ind lc_set_obind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_obind_of_lc_set_obind :
forall ob1, lc_set_obind ob1 -> lc_obind ob1.
Proof.
pose proof lc_obind_of_lc_set_obind_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_obind_of_lc_set_obind : lngen.

(* begin hide *)

Lemma lc_work_of_lc_set_work_lc_worklist_of_lc_set_worklist_mutual :
(forall w1, lc_set_work w1 -> lc_work w1) /\
(forall wl1, lc_set_worklist wl1 -> lc_worklist wl1).
Proof.
apply_mutual_ind lc_set_work_lc_set_worklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_work_of_lc_set_work :
forall w1, lc_set_work w1 -> lc_work w1.
Proof.
pose proof lc_work_of_lc_set_work_lc_worklist_of_lc_set_worklist_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_work_of_lc_set_work : lngen.

Lemma lc_worklist_of_lc_set_worklist :
forall wl1, lc_set_worklist wl1 -> lc_worklist wl1.
Proof.
pose proof lc_work_of_lc_set_work_lc_worklist_of_lc_set_worklist_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_worklist_of_lc_set_worklist : lngen.

(* begin hide *)

Lemma lc_set_aexpr_of_lc_aexpr_lc_set_abody_of_lc_abody_size_mutual :
forall i1,
(forall e1,
  size_aexpr e1 = i1 ->
  lc_aexpr e1 ->
  lc_set_aexpr e1) *
(forall ab1,
  size_abody ab1 = i1 ->
  lc_abody ab1 ->
  lc_set_abody ab1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind aexpr_abody_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_aexpr_of_lc_aexpr
 | apply lc_set_abody_of_lc_abody
 | apply lc_set_akind_of_lc_akind
 | apply lc_set_aexpr_of_lc_aexpr
 | apply lc_set_abody_of_lc_abody
 | apply lc_set_akind_of_lc_akind];
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

Lemma lc_set_aexpr_of_lc_aexpr :
forall e1,
  lc_aexpr e1 ->
  lc_set_aexpr e1.
Proof.
intros e1; intros;
pose proof (lc_set_aexpr_of_lc_aexpr_lc_set_abody_of_lc_abody_size_mutual (size_aexpr e1));
intuition eauto.
Qed.

Hint Resolve lc_set_aexpr_of_lc_aexpr : lngen.

Lemma lc_set_abody_of_lc_abody :
forall ab1,
  lc_abody ab1 ->
  lc_set_abody ab1.
Proof.
intros ab1; intros;
pose proof (lc_set_aexpr_of_lc_aexpr_lc_set_abody_of_lc_abody_size_mutual (size_abody ab1));
intuition eauto.
Qed.

Hint Resolve lc_set_abody_of_lc_abody : lngen.

(* begin hide *)

Lemma lc_set_binding_of_lc_binding_size_mutual :
forall i1,
(forall b1,
  size_binding b1 = i1 ->
  lc_binding b1 ->
  lc_set_binding b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind binding_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_aexpr_of_lc_aexpr
 | apply lc_set_abody_of_lc_abody
 | apply lc_set_akind_of_lc_akind
 | apply lc_set_binding_of_lc_binding];
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

Lemma lc_set_binding_of_lc_binding :
forall b1,
  lc_binding b1 ->
  lc_set_binding b1.
Proof.
intros b1; intros;
pose proof (lc_set_binding_of_lc_binding_size_mutual (size_binding b1));
intuition eauto.
Qed.

Hint Resolve lc_set_binding_of_lc_binding : lngen.

(* begin hide *)

Lemma lc_set_obind_of_lc_obind_size_mutual :
forall i1,
(forall ob1,
  size_obind ob1 = i1 ->
  lc_obind ob1 ->
  lc_set_obind ob1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind obind_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_aexpr_of_lc_aexpr
 | apply lc_set_abody_of_lc_abody
 | apply lc_set_akind_of_lc_akind
 | apply lc_set_obind_of_lc_obind];
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

Lemma lc_set_obind_of_lc_obind :
forall ob1,
  lc_obind ob1 ->
  lc_set_obind ob1.
Proof.
intros ob1; intros;
pose proof (lc_set_obind_of_lc_obind_size_mutual (size_obind ob1));
intuition eauto.
Qed.

Hint Resolve lc_set_obind_of_lc_obind : lngen.

(* begin hide *)

Lemma lc_set_work_of_lc_work_lc_set_worklist_of_lc_worklist_size_mutual :
forall i1,
(forall w1,
  size_work w1 = i1 ->
  lc_work w1 ->
  lc_set_work w1) *
(forall wl1,
  size_worklist wl1 = i1 ->
  lc_worklist wl1 ->
  lc_set_worklist wl1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind work_worklist_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_aexpr_of_lc_aexpr
 | apply lc_set_abody_of_lc_abody
 | apply lc_set_akind_of_lc_akind
 | apply lc_set_binding_of_lc_binding
 | apply lc_set_obind_of_lc_obind
 | apply lc_set_work_of_lc_work
 | apply lc_set_worklist_of_lc_worklist
 | apply lc_set_aexpr_of_lc_aexpr
 | apply lc_set_abody_of_lc_abody
 | apply lc_set_akind_of_lc_akind
 | apply lc_set_binding_of_lc_binding
 | apply lc_set_obind_of_lc_obind
 | apply lc_set_work_of_lc_work
 | apply lc_set_worklist_of_lc_worklist];
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

Lemma lc_set_work_of_lc_work :
forall w1,
  lc_work w1 ->
  lc_set_work w1.
Proof.
intros w1; intros;
pose proof (lc_set_work_of_lc_work_lc_set_worklist_of_lc_worklist_size_mutual (size_work w1));
intuition eauto.
Qed.

Hint Resolve lc_set_work_of_lc_work : lngen.

Lemma lc_set_worklist_of_lc_worklist :
forall wl1,
  lc_worklist wl1 ->
  lc_set_worklist wl1.
Proof.
intros wl1; intros;
pose proof (lc_set_work_of_lc_work_lc_set_worklist_of_lc_worklist_size_mutual (size_worklist wl1));
intuition eauto.
Qed.

Hint Resolve lc_set_worklist_of_lc_worklist : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr_close_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr_mutual :
(forall e1 x1 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 `notin` fv_aexpr e1 ->
  close_aexpr_wrt_aexpr_rec n1 x1 e1 = e1) /\
(forall ab1 x1 n1,
  degree_abody_wrt_aexpr n1 ab1 ->
  x1 `notin` fv_abody ab1 ->
  close_abody_wrt_aexpr_rec n1 x1 ab1 = ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr :
forall e1 x1 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 `notin` fv_aexpr e1 ->
  close_aexpr_wrt_aexpr_rec n1 x1 e1 = e1.
Proof.
pose proof close_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr_close_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr : lngen.
Hint Rewrite close_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr :
forall ab1 x1 n1,
  degree_abody_wrt_aexpr n1 ab1 ->
  x1 `notin` fv_abody ab1 ->
  close_abody_wrt_aexpr_rec n1 x1 ab1 = ab1.
Proof.
pose proof close_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr_close_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr : lngen.
Hint Rewrite close_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_aexpr_rec_degree_binding_wrt_aexpr_mutual :
(forall b1 x1 n1,
  degree_binding_wrt_aexpr n1 b1 ->
  x1 `notin` fv_binding b1 ->
  close_binding_wrt_aexpr_rec n1 x1 b1 = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_aexpr_rec_degree_binding_wrt_aexpr :
forall b1 x1 n1,
  degree_binding_wrt_aexpr n1 b1 ->
  x1 `notin` fv_binding b1 ->
  close_binding_wrt_aexpr_rec n1 x1 b1 = b1.
Proof.
pose proof close_binding_wrt_aexpr_rec_degree_binding_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_binding_wrt_aexpr_rec_degree_binding_wrt_aexpr : lngen.
Hint Rewrite close_binding_wrt_aexpr_rec_degree_binding_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_obind_wrt_aexpr_rec_degree_obind_wrt_aexpr_mutual :
(forall ob1 x1 n1,
  degree_obind_wrt_aexpr n1 ob1 ->
  x1 `notin` fv_obind ob1 ->
  close_obind_wrt_aexpr_rec n1 x1 ob1 = ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_obind_wrt_aexpr_rec_degree_obind_wrt_aexpr :
forall ob1 x1 n1,
  degree_obind_wrt_aexpr n1 ob1 ->
  x1 `notin` fv_obind ob1 ->
  close_obind_wrt_aexpr_rec n1 x1 ob1 = ob1.
Proof.
pose proof close_obind_wrt_aexpr_rec_degree_obind_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_obind_wrt_aexpr_rec_degree_obind_wrt_aexpr : lngen.
Hint Rewrite close_obind_wrt_aexpr_rec_degree_obind_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_aexpr_rec_degree_work_wrt_aexpr_close_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr_mutual :
(forall w1 x1 n1,
  degree_work_wrt_aexpr n1 w1 ->
  x1 `notin` fv_work w1 ->
  close_work_wrt_aexpr_rec n1 x1 w1 = w1) /\
(forall wl1 x1 n1,
  degree_worklist_wrt_aexpr n1 wl1 ->
  x1 `notin` fv_worklist wl1 ->
  close_worklist_wrt_aexpr_rec n1 x1 wl1 = wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_aexpr_rec_degree_work_wrt_aexpr :
forall w1 x1 n1,
  degree_work_wrt_aexpr n1 w1 ->
  x1 `notin` fv_work w1 ->
  close_work_wrt_aexpr_rec n1 x1 w1 = w1.
Proof.
pose proof close_work_wrt_aexpr_rec_degree_work_wrt_aexpr_close_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_work_wrt_aexpr_rec_degree_work_wrt_aexpr : lngen.
Hint Rewrite close_work_wrt_aexpr_rec_degree_work_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr :
forall wl1 x1 n1,
  degree_worklist_wrt_aexpr n1 wl1 ->
  x1 `notin` fv_worklist wl1 ->
  close_worklist_wrt_aexpr_rec n1 x1 wl1 = wl1.
Proof.
pose proof close_work_wrt_aexpr_rec_degree_work_wrt_aexpr_close_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve close_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr : lngen.
Hint Rewrite close_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

Lemma close_aexpr_wrt_aexpr_lc_aexpr :
forall e1 x1,
  lc_aexpr e1 ->
  x1 `notin` fv_aexpr e1 ->
  close_aexpr_wrt_aexpr x1 e1 = e1.
Proof.
unfold close_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_aexpr_wrt_aexpr_lc_aexpr : lngen.
Hint Rewrite close_aexpr_wrt_aexpr_lc_aexpr using solve [auto] : lngen.

Lemma close_abody_wrt_aexpr_lc_abody :
forall ab1 x1,
  lc_abody ab1 ->
  x1 `notin` fv_abody ab1 ->
  close_abody_wrt_aexpr x1 ab1 = ab1.
Proof.
unfold close_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_abody_wrt_aexpr_lc_abody : lngen.
Hint Rewrite close_abody_wrt_aexpr_lc_abody using solve [auto] : lngen.

Lemma close_binding_wrt_aexpr_lc_binding :
forall b1 x1,
  lc_binding b1 ->
  x1 `notin` fv_binding b1 ->
  close_binding_wrt_aexpr x1 b1 = b1.
Proof.
unfold close_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_binding_wrt_aexpr_lc_binding : lngen.
Hint Rewrite close_binding_wrt_aexpr_lc_binding using solve [auto] : lngen.

Lemma close_obind_wrt_aexpr_lc_obind :
forall ob1 x1,
  lc_obind ob1 ->
  x1 `notin` fv_obind ob1 ->
  close_obind_wrt_aexpr x1 ob1 = ob1.
Proof.
unfold close_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_obind_wrt_aexpr_lc_obind : lngen.
Hint Rewrite close_obind_wrt_aexpr_lc_obind using solve [auto] : lngen.

Lemma close_work_wrt_aexpr_lc_work :
forall w1 x1,
  lc_work w1 ->
  x1 `notin` fv_work w1 ->
  close_work_wrt_aexpr x1 w1 = w1.
Proof.
unfold close_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_work_wrt_aexpr_lc_work : lngen.
Hint Rewrite close_work_wrt_aexpr_lc_work using solve [auto] : lngen.

Lemma close_worklist_wrt_aexpr_lc_worklist :
forall wl1 x1,
  lc_worklist wl1 ->
  x1 `notin` fv_worklist wl1 ->
  close_worklist_wrt_aexpr x1 wl1 = wl1.
Proof.
unfold close_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve close_worklist_wrt_aexpr_lc_worklist : lngen.
Hint Rewrite close_worklist_wrt_aexpr_lc_worklist using solve [auto] : lngen.

(* begin hide *)

Lemma open_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr_open_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr_mutual :
(forall e2 e1 n1,
  degree_aexpr_wrt_aexpr n1 e2 ->
  open_aexpr_wrt_aexpr_rec n1 e1 e2 = e2) /\
(forall ab1 e1 n1,
  degree_abody_wrt_aexpr n1 ab1 ->
  open_abody_wrt_aexpr_rec n1 e1 ab1 = ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr :
forall e2 e1 n1,
  degree_aexpr_wrt_aexpr n1 e2 ->
  open_aexpr_wrt_aexpr_rec n1 e1 e2 = e2.
Proof.
pose proof open_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr_open_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr : lngen.
Hint Rewrite open_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr :
forall ab1 e1 n1,
  degree_abody_wrt_aexpr n1 ab1 ->
  open_abody_wrt_aexpr_rec n1 e1 ab1 = ab1.
Proof.
pose proof open_aexpr_wrt_aexpr_rec_degree_aexpr_wrt_aexpr_open_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr : lngen.
Hint Rewrite open_abody_wrt_aexpr_rec_degree_abody_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_aexpr_rec_degree_binding_wrt_aexpr_mutual :
(forall b1 e1 n1,
  degree_binding_wrt_aexpr n1 b1 ->
  open_binding_wrt_aexpr_rec n1 e1 b1 = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_aexpr_rec_degree_binding_wrt_aexpr :
forall b1 e1 n1,
  degree_binding_wrt_aexpr n1 b1 ->
  open_binding_wrt_aexpr_rec n1 e1 b1 = b1.
Proof.
pose proof open_binding_wrt_aexpr_rec_degree_binding_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_binding_wrt_aexpr_rec_degree_binding_wrt_aexpr : lngen.
Hint Rewrite open_binding_wrt_aexpr_rec_degree_binding_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_obind_wrt_aexpr_rec_degree_obind_wrt_aexpr_mutual :
(forall ob1 e1 n1,
  degree_obind_wrt_aexpr n1 ob1 ->
  open_obind_wrt_aexpr_rec n1 e1 ob1 = ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_obind_wrt_aexpr_rec_degree_obind_wrt_aexpr :
forall ob1 e1 n1,
  degree_obind_wrt_aexpr n1 ob1 ->
  open_obind_wrt_aexpr_rec n1 e1 ob1 = ob1.
Proof.
pose proof open_obind_wrt_aexpr_rec_degree_obind_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_obind_wrt_aexpr_rec_degree_obind_wrt_aexpr : lngen.
Hint Rewrite open_obind_wrt_aexpr_rec_degree_obind_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_aexpr_rec_degree_work_wrt_aexpr_open_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr_mutual :
(forall w1 e1 n1,
  degree_work_wrt_aexpr n1 w1 ->
  open_work_wrt_aexpr_rec n1 e1 w1 = w1) /\
(forall wl1 e1 n1,
  degree_worklist_wrt_aexpr n1 wl1 ->
  open_worklist_wrt_aexpr_rec n1 e1 wl1 = wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_aexpr_rec_degree_work_wrt_aexpr :
forall w1 e1 n1,
  degree_work_wrt_aexpr n1 w1 ->
  open_work_wrt_aexpr_rec n1 e1 w1 = w1.
Proof.
pose proof open_work_wrt_aexpr_rec_degree_work_wrt_aexpr_open_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_work_wrt_aexpr_rec_degree_work_wrt_aexpr : lngen.
Hint Rewrite open_work_wrt_aexpr_rec_degree_work_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr :
forall wl1 e1 n1,
  degree_worklist_wrt_aexpr n1 wl1 ->
  open_worklist_wrt_aexpr_rec n1 e1 wl1 = wl1.
Proof.
pose proof open_work_wrt_aexpr_rec_degree_work_wrt_aexpr_open_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve open_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr : lngen.
Hint Rewrite open_worklist_wrt_aexpr_rec_degree_worklist_wrt_aexpr using solve [auto] : lngen.

(* end hide *)

Lemma open_aexpr_wrt_aexpr_lc_aexpr :
forall e2 e1,
  lc_aexpr e2 ->
  open_aexpr_wrt_aexpr e2 e1 = e2.
Proof.
unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_aexpr_wrt_aexpr_lc_aexpr : lngen.
Hint Rewrite open_aexpr_wrt_aexpr_lc_aexpr using solve [auto] : lngen.

Lemma open_abody_wrt_aexpr_lc_abody :
forall ab1 e1,
  lc_abody ab1 ->
  open_abody_wrt_aexpr ab1 e1 = ab1.
Proof.
unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_abody_wrt_aexpr_lc_abody : lngen.
Hint Rewrite open_abody_wrt_aexpr_lc_abody using solve [auto] : lngen.

Lemma open_binding_wrt_aexpr_lc_binding :
forall b1 e1,
  lc_binding b1 ->
  open_binding_wrt_aexpr b1 e1 = b1.
Proof.
unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_binding_wrt_aexpr_lc_binding : lngen.
Hint Rewrite open_binding_wrt_aexpr_lc_binding using solve [auto] : lngen.

Lemma open_obind_wrt_aexpr_lc_obind :
forall ob1 e1,
  lc_obind ob1 ->
  open_obind_wrt_aexpr ob1 e1 = ob1.
Proof.
unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_obind_wrt_aexpr_lc_obind : lngen.
Hint Rewrite open_obind_wrt_aexpr_lc_obind using solve [auto] : lngen.

Lemma open_work_wrt_aexpr_lc_work :
forall w1 e1,
  lc_work w1 ->
  open_work_wrt_aexpr w1 e1 = w1.
Proof.
unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_work_wrt_aexpr_lc_work : lngen.
Hint Rewrite open_work_wrt_aexpr_lc_work using solve [auto] : lngen.

Lemma open_worklist_wrt_aexpr_lc_worklist :
forall wl1 e1,
  lc_worklist wl1 ->
  open_worklist_wrt_aexpr wl1 e1 = wl1.
Proof.
unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve open_worklist_wrt_aexpr_lc_worklist : lngen.
Hint Rewrite open_worklist_wrt_aexpr_lc_worklist using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_aexpr_close_aexpr_wrt_aexpr_rec_fv_abody_close_abody_wrt_aexpr_rec_mutual :
(forall e1 x1 n1,
  fv_aexpr (close_aexpr_wrt_aexpr_rec n1 x1 e1) [=] remove x1 (fv_aexpr e1)) /\
(forall ab1 x1 n1,
  fv_abody (close_abody_wrt_aexpr_rec n1 x1 ab1) [=] remove x1 (fv_abody ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_aexpr_close_aexpr_wrt_aexpr_rec :
forall e1 x1 n1,
  fv_aexpr (close_aexpr_wrt_aexpr_rec n1 x1 e1) [=] remove x1 (fv_aexpr e1).
Proof.
pose proof fv_aexpr_close_aexpr_wrt_aexpr_rec_fv_abody_close_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_aexpr_close_aexpr_wrt_aexpr_rec : lngen.
Hint Rewrite fv_aexpr_close_aexpr_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_abody_close_abody_wrt_aexpr_rec :
forall ab1 x1 n1,
  fv_abody (close_abody_wrt_aexpr_rec n1 x1 ab1) [=] remove x1 (fv_abody ab1).
Proof.
pose proof fv_aexpr_close_aexpr_wrt_aexpr_rec_fv_abody_close_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_abody_close_abody_wrt_aexpr_rec : lngen.
Hint Rewrite fv_abody_close_abody_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_binding_close_binding_wrt_aexpr_rec_mutual :
(forall b1 x1 n1,
  fv_binding (close_binding_wrt_aexpr_rec n1 x1 b1) [=] remove x1 (fv_binding b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_binding_close_binding_wrt_aexpr_rec :
forall b1 x1 n1,
  fv_binding (close_binding_wrt_aexpr_rec n1 x1 b1) [=] remove x1 (fv_binding b1).
Proof.
pose proof fv_binding_close_binding_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_binding_close_binding_wrt_aexpr_rec : lngen.
Hint Rewrite fv_binding_close_binding_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_obind_close_obind_wrt_aexpr_rec_mutual :
(forall ob1 x1 n1,
  fv_obind (close_obind_wrt_aexpr_rec n1 x1 ob1) [=] remove x1 (fv_obind ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_obind_close_obind_wrt_aexpr_rec :
forall ob1 x1 n1,
  fv_obind (close_obind_wrt_aexpr_rec n1 x1 ob1) [=] remove x1 (fv_obind ob1).
Proof.
pose proof fv_obind_close_obind_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obind_close_obind_wrt_aexpr_rec : lngen.
Hint Rewrite fv_obind_close_obind_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_work_close_work_wrt_aexpr_rec_fv_worklist_close_worklist_wrt_aexpr_rec_mutual :
(forall w1 x1 n1,
  fv_work (close_work_wrt_aexpr_rec n1 x1 w1) [=] remove x1 (fv_work w1)) /\
(forall wl1 x1 n1,
  fv_worklist (close_worklist_wrt_aexpr_rec n1 x1 wl1) [=] remove x1 (fv_worklist wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_work_close_work_wrt_aexpr_rec :
forall w1 x1 n1,
  fv_work (close_work_wrt_aexpr_rec n1 x1 w1) [=] remove x1 (fv_work w1).
Proof.
pose proof fv_work_close_work_wrt_aexpr_rec_fv_worklist_close_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_work_close_work_wrt_aexpr_rec : lngen.
Hint Rewrite fv_work_close_work_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_worklist_close_worklist_wrt_aexpr_rec :
forall wl1 x1 n1,
  fv_worklist (close_worklist_wrt_aexpr_rec n1 x1 wl1) [=] remove x1 (fv_worklist wl1).
Proof.
pose proof fv_work_close_work_wrt_aexpr_rec_fv_worklist_close_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_worklist_close_worklist_wrt_aexpr_rec : lngen.
Hint Rewrite fv_worklist_close_worklist_wrt_aexpr_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_aexpr_close_aexpr_wrt_aexpr :
forall e1 x1,
  fv_aexpr (close_aexpr_wrt_aexpr x1 e1) [=] remove x1 (fv_aexpr e1).
Proof.
unfold close_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_aexpr_close_aexpr_wrt_aexpr : lngen.
Hint Rewrite fv_aexpr_close_aexpr_wrt_aexpr using solve [auto] : lngen.

Lemma fv_abody_close_abody_wrt_aexpr :
forall ab1 x1,
  fv_abody (close_abody_wrt_aexpr x1 ab1) [=] remove x1 (fv_abody ab1).
Proof.
unfold close_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_abody_close_abody_wrt_aexpr : lngen.
Hint Rewrite fv_abody_close_abody_wrt_aexpr using solve [auto] : lngen.

Lemma fv_binding_close_binding_wrt_aexpr :
forall b1 x1,
  fv_binding (close_binding_wrt_aexpr x1 b1) [=] remove x1 (fv_binding b1).
Proof.
unfold close_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_binding_close_binding_wrt_aexpr : lngen.
Hint Rewrite fv_binding_close_binding_wrt_aexpr using solve [auto] : lngen.

Lemma fv_obind_close_obind_wrt_aexpr :
forall ob1 x1,
  fv_obind (close_obind_wrt_aexpr x1 ob1) [=] remove x1 (fv_obind ob1).
Proof.
unfold close_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_obind_close_obind_wrt_aexpr : lngen.
Hint Rewrite fv_obind_close_obind_wrt_aexpr using solve [auto] : lngen.

Lemma fv_work_close_work_wrt_aexpr :
forall w1 x1,
  fv_work (close_work_wrt_aexpr x1 w1) [=] remove x1 (fv_work w1).
Proof.
unfold close_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_work_close_work_wrt_aexpr : lngen.
Hint Rewrite fv_work_close_work_wrt_aexpr using solve [auto] : lngen.

Lemma fv_worklist_close_worklist_wrt_aexpr :
forall wl1 x1,
  fv_worklist (close_worklist_wrt_aexpr x1 wl1) [=] remove x1 (fv_worklist wl1).
Proof.
unfold close_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_worklist_close_worklist_wrt_aexpr : lngen.
Hint Rewrite fv_worklist_close_worklist_wrt_aexpr using solve [auto] : lngen.

(* begin hide *)

Lemma fv_aexpr_open_aexpr_wrt_aexpr_rec_lower_fv_abody_open_abody_wrt_aexpr_rec_lower_mutual :
(forall e1 e2 n1,
  fv_aexpr e1 [<=] fv_aexpr (open_aexpr_wrt_aexpr_rec n1 e2 e1)) /\
(forall ab1 e1 n1,
  fv_abody ab1 [<=] fv_abody (open_abody_wrt_aexpr_rec n1 e1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_aexpr_open_aexpr_wrt_aexpr_rec_lower :
forall e1 e2 n1,
  fv_aexpr e1 [<=] fv_aexpr (open_aexpr_wrt_aexpr_rec n1 e2 e1).
Proof.
pose proof fv_aexpr_open_aexpr_wrt_aexpr_rec_lower_fv_abody_open_abody_wrt_aexpr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_aexpr_open_aexpr_wrt_aexpr_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_abody_open_abody_wrt_aexpr_rec_lower :
forall ab1 e1 n1,
  fv_abody ab1 [<=] fv_abody (open_abody_wrt_aexpr_rec n1 e1 ab1).
Proof.
pose proof fv_aexpr_open_aexpr_wrt_aexpr_rec_lower_fv_abody_open_abody_wrt_aexpr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_abody_open_abody_wrt_aexpr_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_binding_open_binding_wrt_aexpr_rec_lower_mutual :
(forall b1 e1 n1,
  fv_binding b1 [<=] fv_binding (open_binding_wrt_aexpr_rec n1 e1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_binding_open_binding_wrt_aexpr_rec_lower :
forall b1 e1 n1,
  fv_binding b1 [<=] fv_binding (open_binding_wrt_aexpr_rec n1 e1 b1).
Proof.
pose proof fv_binding_open_binding_wrt_aexpr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_binding_open_binding_wrt_aexpr_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_obind_open_obind_wrt_aexpr_rec_lower_mutual :
(forall ob1 e1 n1,
  fv_obind ob1 [<=] fv_obind (open_obind_wrt_aexpr_rec n1 e1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_obind_open_obind_wrt_aexpr_rec_lower :
forall ob1 e1 n1,
  fv_obind ob1 [<=] fv_obind (open_obind_wrt_aexpr_rec n1 e1 ob1).
Proof.
pose proof fv_obind_open_obind_wrt_aexpr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obind_open_obind_wrt_aexpr_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_work_open_work_wrt_aexpr_rec_lower_fv_worklist_open_worklist_wrt_aexpr_rec_lower_mutual :
(forall w1 e1 n1,
  fv_work w1 [<=] fv_work (open_work_wrt_aexpr_rec n1 e1 w1)) /\
(forall wl1 e1 n1,
  fv_worklist wl1 [<=] fv_worklist (open_worklist_wrt_aexpr_rec n1 e1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_work_open_work_wrt_aexpr_rec_lower :
forall w1 e1 n1,
  fv_work w1 [<=] fv_work (open_work_wrt_aexpr_rec n1 e1 w1).
Proof.
pose proof fv_work_open_work_wrt_aexpr_rec_lower_fv_worklist_open_worklist_wrt_aexpr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_work_open_work_wrt_aexpr_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_worklist_open_worklist_wrt_aexpr_rec_lower :
forall wl1 e1 n1,
  fv_worklist wl1 [<=] fv_worklist (open_worklist_wrt_aexpr_rec n1 e1 wl1).
Proof.
pose proof fv_work_open_work_wrt_aexpr_rec_lower_fv_worklist_open_worklist_wrt_aexpr_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_worklist_open_worklist_wrt_aexpr_rec_lower : lngen.

(* end hide *)

Lemma fv_aexpr_open_aexpr_wrt_aexpr_lower :
forall e1 e2,
  fv_aexpr e1 [<=] fv_aexpr (open_aexpr_wrt_aexpr e1 e2).
Proof.
unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_aexpr_open_aexpr_wrt_aexpr_lower : lngen.

Lemma fv_abody_open_abody_wrt_aexpr_lower :
forall ab1 e1,
  fv_abody ab1 [<=] fv_abody (open_abody_wrt_aexpr ab1 e1).
Proof.
unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_abody_open_abody_wrt_aexpr_lower : lngen.

Lemma fv_binding_open_binding_wrt_aexpr_lower :
forall b1 e1,
  fv_binding b1 [<=] fv_binding (open_binding_wrt_aexpr b1 e1).
Proof.
unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_binding_open_binding_wrt_aexpr_lower : lngen.

Lemma fv_obind_open_obind_wrt_aexpr_lower :
forall ob1 e1,
  fv_obind ob1 [<=] fv_obind (open_obind_wrt_aexpr ob1 e1).
Proof.
unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_obind_open_obind_wrt_aexpr_lower : lngen.

Lemma fv_work_open_work_wrt_aexpr_lower :
forall w1 e1,
  fv_work w1 [<=] fv_work (open_work_wrt_aexpr w1 e1).
Proof.
unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_work_open_work_wrt_aexpr_lower : lngen.

Lemma fv_worklist_open_worklist_wrt_aexpr_lower :
forall wl1 e1,
  fv_worklist wl1 [<=] fv_worklist (open_worklist_wrt_aexpr wl1 e1).
Proof.
unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_worklist_open_worklist_wrt_aexpr_lower : lngen.

(* begin hide *)

Lemma fv_aexpr_open_aexpr_wrt_aexpr_rec_upper_fv_abody_open_abody_wrt_aexpr_rec_upper_mutual :
(forall e1 e2 n1,
  fv_aexpr (open_aexpr_wrt_aexpr_rec n1 e2 e1) [<=] fv_aexpr e2 `union` fv_aexpr e1) /\
(forall ab1 e1 n1,
  fv_abody (open_abody_wrt_aexpr_rec n1 e1 ab1) [<=] fv_aexpr e1 `union` fv_abody ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_aexpr_open_aexpr_wrt_aexpr_rec_upper :
forall e1 e2 n1,
  fv_aexpr (open_aexpr_wrt_aexpr_rec n1 e2 e1) [<=] fv_aexpr e2 `union` fv_aexpr e1.
Proof.
pose proof fv_aexpr_open_aexpr_wrt_aexpr_rec_upper_fv_abody_open_abody_wrt_aexpr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_aexpr_open_aexpr_wrt_aexpr_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_abody_open_abody_wrt_aexpr_rec_upper :
forall ab1 e1 n1,
  fv_abody (open_abody_wrt_aexpr_rec n1 e1 ab1) [<=] fv_aexpr e1 `union` fv_abody ab1.
Proof.
pose proof fv_aexpr_open_aexpr_wrt_aexpr_rec_upper_fv_abody_open_abody_wrt_aexpr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_abody_open_abody_wrt_aexpr_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_binding_open_binding_wrt_aexpr_rec_upper_mutual :
(forall b1 e1 n1,
  fv_binding (open_binding_wrt_aexpr_rec n1 e1 b1) [<=] fv_aexpr e1 `union` fv_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_binding_open_binding_wrt_aexpr_rec_upper :
forall b1 e1 n1,
  fv_binding (open_binding_wrt_aexpr_rec n1 e1 b1) [<=] fv_aexpr e1 `union` fv_binding b1.
Proof.
pose proof fv_binding_open_binding_wrt_aexpr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_binding_open_binding_wrt_aexpr_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_obind_open_obind_wrt_aexpr_rec_upper_mutual :
(forall ob1 e1 n1,
  fv_obind (open_obind_wrt_aexpr_rec n1 e1 ob1) [<=] fv_aexpr e1 `union` fv_obind ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_obind_open_obind_wrt_aexpr_rec_upper :
forall ob1 e1 n1,
  fv_obind (open_obind_wrt_aexpr_rec n1 e1 ob1) [<=] fv_aexpr e1 `union` fv_obind ob1.
Proof.
pose proof fv_obind_open_obind_wrt_aexpr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obind_open_obind_wrt_aexpr_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_work_open_work_wrt_aexpr_rec_upper_fv_worklist_open_worklist_wrt_aexpr_rec_upper_mutual :
(forall w1 e1 n1,
  fv_work (open_work_wrt_aexpr_rec n1 e1 w1) [<=] fv_aexpr e1 `union` fv_work w1) /\
(forall wl1 e1 n1,
  fv_worklist (open_worklist_wrt_aexpr_rec n1 e1 wl1) [<=] fv_aexpr e1 `union` fv_worklist wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_work_open_work_wrt_aexpr_rec_upper :
forall w1 e1 n1,
  fv_work (open_work_wrt_aexpr_rec n1 e1 w1) [<=] fv_aexpr e1 `union` fv_work w1.
Proof.
pose proof fv_work_open_work_wrt_aexpr_rec_upper_fv_worklist_open_worklist_wrt_aexpr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_work_open_work_wrt_aexpr_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_worklist_open_worklist_wrt_aexpr_rec_upper :
forall wl1 e1 n1,
  fv_worklist (open_worklist_wrt_aexpr_rec n1 e1 wl1) [<=] fv_aexpr e1 `union` fv_worklist wl1.
Proof.
pose proof fv_work_open_work_wrt_aexpr_rec_upper_fv_worklist_open_worklist_wrt_aexpr_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_worklist_open_worklist_wrt_aexpr_rec_upper : lngen.

(* end hide *)

Lemma fv_aexpr_open_aexpr_wrt_aexpr_upper :
forall e1 e2,
  fv_aexpr (open_aexpr_wrt_aexpr e1 e2) [<=] fv_aexpr e2 `union` fv_aexpr e1.
Proof.
unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_aexpr_open_aexpr_wrt_aexpr_upper : lngen.

Lemma fv_abody_open_abody_wrt_aexpr_upper :
forall ab1 e1,
  fv_abody (open_abody_wrt_aexpr ab1 e1) [<=] fv_aexpr e1 `union` fv_abody ab1.
Proof.
unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_abody_open_abody_wrt_aexpr_upper : lngen.

Lemma fv_binding_open_binding_wrt_aexpr_upper :
forall b1 e1,
  fv_binding (open_binding_wrt_aexpr b1 e1) [<=] fv_aexpr e1 `union` fv_binding b1.
Proof.
unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_binding_open_binding_wrt_aexpr_upper : lngen.

Lemma fv_obind_open_obind_wrt_aexpr_upper :
forall ob1 e1,
  fv_obind (open_obind_wrt_aexpr ob1 e1) [<=] fv_aexpr e1 `union` fv_obind ob1.
Proof.
unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_obind_open_obind_wrt_aexpr_upper : lngen.

Lemma fv_work_open_work_wrt_aexpr_upper :
forall w1 e1,
  fv_work (open_work_wrt_aexpr w1 e1) [<=] fv_aexpr e1 `union` fv_work w1.
Proof.
unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_work_open_work_wrt_aexpr_upper : lngen.

Lemma fv_worklist_open_worklist_wrt_aexpr_upper :
forall wl1 e1,
  fv_worklist (open_worklist_wrt_aexpr wl1 e1) [<=] fv_aexpr e1 `union` fv_worklist wl1.
Proof.
unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve fv_worklist_open_worklist_wrt_aexpr_upper : lngen.

(* begin hide *)

Lemma fv_aexpr_subst_aexpr_fresh_fv_abody_subst_abody_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_aexpr e1 ->
  fv_aexpr (subst_aexpr e2 x1 e1) [=] fv_aexpr e1) /\
(forall ab1 e1 x1,
  x1 `notin` fv_abody ab1 ->
  fv_abody (subst_abody e1 x1 ab1) [=] fv_abody ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_aexpr_subst_aexpr_fresh :
forall e1 e2 x1,
  x1 `notin` fv_aexpr e1 ->
  fv_aexpr (subst_aexpr e2 x1 e1) [=] fv_aexpr e1.
Proof.
pose proof fv_aexpr_subst_aexpr_fresh_fv_abody_subst_abody_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_aexpr_subst_aexpr_fresh : lngen.
Hint Rewrite fv_aexpr_subst_aexpr_fresh using solve [auto] : lngen.

Lemma fv_abody_subst_abody_fresh :
forall ab1 e1 x1,
  x1 `notin` fv_abody ab1 ->
  fv_abody (subst_abody e1 x1 ab1) [=] fv_abody ab1.
Proof.
pose proof fv_aexpr_subst_aexpr_fresh_fv_abody_subst_abody_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_abody_subst_abody_fresh : lngen.
Hint Rewrite fv_abody_subst_abody_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_binding_subst_binding_fresh_mutual :
(forall b1 e1 x1,
  x1 `notin` fv_binding b1 ->
  fv_binding (subst_binding e1 x1 b1) [=] fv_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_binding_subst_binding_fresh :
forall b1 e1 x1,
  x1 `notin` fv_binding b1 ->
  fv_binding (subst_binding e1 x1 b1) [=] fv_binding b1.
Proof.
pose proof fv_binding_subst_binding_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_binding_subst_binding_fresh : lngen.
Hint Rewrite fv_binding_subst_binding_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_obind_subst_obind_fresh_mutual :
(forall ob1 e1 x1,
  x1 `notin` fv_obind ob1 ->
  fv_obind (subst_obind e1 x1 ob1) [=] fv_obind ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_obind_subst_obind_fresh :
forall ob1 e1 x1,
  x1 `notin` fv_obind ob1 ->
  fv_obind (subst_obind e1 x1 ob1) [=] fv_obind ob1.
Proof.
pose proof fv_obind_subst_obind_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obind_subst_obind_fresh : lngen.
Hint Rewrite fv_obind_subst_obind_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_work_subst_work_fresh_fv_worklist_subst_worklist_fresh_mutual :
(forall w1 e1 x1,
  x1 `notin` fv_work w1 ->
  fv_work (subst_work e1 x1 w1) [=] fv_work w1) /\
(forall wl1 e1 x1,
  x1 `notin` fv_worklist wl1 ->
  fv_worklist (subst_worklist e1 x1 wl1) [=] fv_worklist wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_work_subst_work_fresh :
forall w1 e1 x1,
  x1 `notin` fv_work w1 ->
  fv_work (subst_work e1 x1 w1) [=] fv_work w1.
Proof.
pose proof fv_work_subst_work_fresh_fv_worklist_subst_worklist_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_work_subst_work_fresh : lngen.
Hint Rewrite fv_work_subst_work_fresh using solve [auto] : lngen.

Lemma fv_worklist_subst_worklist_fresh :
forall wl1 e1 x1,
  x1 `notin` fv_worklist wl1 ->
  fv_worklist (subst_worklist e1 x1 wl1) [=] fv_worklist wl1.
Proof.
pose proof fv_work_subst_work_fresh_fv_worklist_subst_worklist_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_worklist_subst_worklist_fresh : lngen.
Hint Rewrite fv_worklist_subst_worklist_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_aexpr_subst_aexpr_lower_fv_abody_subst_abody_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_aexpr e1) [<=] fv_aexpr (subst_aexpr e2 x1 e1)) /\
(forall ab1 e1 x1,
  remove x1 (fv_abody ab1) [<=] fv_abody (subst_abody e1 x1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_aexpr_subst_aexpr_lower :
forall e1 e2 x1,
  remove x1 (fv_aexpr e1) [<=] fv_aexpr (subst_aexpr e2 x1 e1).
Proof.
pose proof fv_aexpr_subst_aexpr_lower_fv_abody_subst_abody_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_aexpr_subst_aexpr_lower : lngen.

Lemma fv_abody_subst_abody_lower :
forall ab1 e1 x1,
  remove x1 (fv_abody ab1) [<=] fv_abody (subst_abody e1 x1 ab1).
Proof.
pose proof fv_aexpr_subst_aexpr_lower_fv_abody_subst_abody_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_abody_subst_abody_lower : lngen.

(* begin hide *)

Lemma fv_binding_subst_binding_lower_mutual :
(forall b1 e1 x1,
  remove x1 (fv_binding b1) [<=] fv_binding (subst_binding e1 x1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_binding_subst_binding_lower :
forall b1 e1 x1,
  remove x1 (fv_binding b1) [<=] fv_binding (subst_binding e1 x1 b1).
Proof.
pose proof fv_binding_subst_binding_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_binding_subst_binding_lower : lngen.

(* begin hide *)

Lemma fv_obind_subst_obind_lower_mutual :
(forall ob1 e1 x1,
  remove x1 (fv_obind ob1) [<=] fv_obind (subst_obind e1 x1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_obind_subst_obind_lower :
forall ob1 e1 x1,
  remove x1 (fv_obind ob1) [<=] fv_obind (subst_obind e1 x1 ob1).
Proof.
pose proof fv_obind_subst_obind_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obind_subst_obind_lower : lngen.

(* begin hide *)

Lemma fv_work_subst_work_lower_fv_worklist_subst_worklist_lower_mutual :
(forall w1 e1 x1,
  remove x1 (fv_work w1) [<=] fv_work (subst_work e1 x1 w1)) /\
(forall wl1 e1 x1,
  remove x1 (fv_worklist wl1) [<=] fv_worklist (subst_worklist e1 x1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_work_subst_work_lower :
forall w1 e1 x1,
  remove x1 (fv_work w1) [<=] fv_work (subst_work e1 x1 w1).
Proof.
pose proof fv_work_subst_work_lower_fv_worklist_subst_worklist_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_work_subst_work_lower : lngen.

Lemma fv_worklist_subst_worklist_lower :
forall wl1 e1 x1,
  remove x1 (fv_worklist wl1) [<=] fv_worklist (subst_worklist e1 x1 wl1).
Proof.
pose proof fv_work_subst_work_lower_fv_worklist_subst_worklist_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_worklist_subst_worklist_lower : lngen.

(* begin hide *)

Lemma fv_aexpr_subst_aexpr_notin_fv_abody_subst_abody_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_aexpr e2 ->
  x2 `notin` fv_aexpr (subst_aexpr e2 x1 e1)) /\
(forall ab1 e1 x1 x2,
  x2 `notin` fv_abody ab1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_abody (subst_abody e1 x1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_aexpr_subst_aexpr_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_aexpr e2 ->
  x2 `notin` fv_aexpr (subst_aexpr e2 x1 e1).
Proof.
pose proof fv_aexpr_subst_aexpr_notin_fv_abody_subst_abody_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_aexpr_subst_aexpr_notin : lngen.

Lemma fv_abody_subst_abody_notin :
forall ab1 e1 x1 x2,
  x2 `notin` fv_abody ab1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_abody (subst_abody e1 x1 ab1).
Proof.
pose proof fv_aexpr_subst_aexpr_notin_fv_abody_subst_abody_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_abody_subst_abody_notin : lngen.

(* begin hide *)

Lemma fv_binding_subst_binding_notin_mutual :
(forall b1 e1 x1 x2,
  x2 `notin` fv_binding b1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_binding (subst_binding e1 x1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_binding_subst_binding_notin :
forall b1 e1 x1 x2,
  x2 `notin` fv_binding b1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_binding (subst_binding e1 x1 b1).
Proof.
pose proof fv_binding_subst_binding_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_binding_subst_binding_notin : lngen.

(* begin hide *)

Lemma fv_obind_subst_obind_notin_mutual :
(forall ob1 e1 x1 x2,
  x2 `notin` fv_obind ob1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_obind (subst_obind e1 x1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_obind_subst_obind_notin :
forall ob1 e1 x1 x2,
  x2 `notin` fv_obind ob1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_obind (subst_obind e1 x1 ob1).
Proof.
pose proof fv_obind_subst_obind_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obind_subst_obind_notin : lngen.

(* begin hide *)

Lemma fv_work_subst_work_notin_fv_worklist_subst_worklist_notin_mutual :
(forall w1 e1 x1 x2,
  x2 `notin` fv_work w1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_work (subst_work e1 x1 w1)) /\
(forall wl1 e1 x1 x2,
  x2 `notin` fv_worklist wl1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_worklist (subst_worklist e1 x1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_work_subst_work_notin :
forall w1 e1 x1 x2,
  x2 `notin` fv_work w1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_work (subst_work e1 x1 w1).
Proof.
pose proof fv_work_subst_work_notin_fv_worklist_subst_worklist_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_work_subst_work_notin : lngen.

Lemma fv_worklist_subst_worklist_notin :
forall wl1 e1 x1 x2,
  x2 `notin` fv_worklist wl1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 `notin` fv_worklist (subst_worklist e1 x1 wl1).
Proof.
pose proof fv_work_subst_work_notin_fv_worklist_subst_worklist_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_worklist_subst_worklist_notin : lngen.

(* begin hide *)

Lemma fv_aexpr_subst_aexpr_upper_fv_abody_subst_abody_upper_mutual :
(forall e1 e2 x1,
  fv_aexpr (subst_aexpr e2 x1 e1) [<=] fv_aexpr e2 `union` remove x1 (fv_aexpr e1)) /\
(forall ab1 e1 x1,
  fv_abody (subst_abody e1 x1 ab1) [<=] fv_aexpr e1 `union` remove x1 (fv_abody ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_aexpr_subst_aexpr_upper :
forall e1 e2 x1,
  fv_aexpr (subst_aexpr e2 x1 e1) [<=] fv_aexpr e2 `union` remove x1 (fv_aexpr e1).
Proof.
pose proof fv_aexpr_subst_aexpr_upper_fv_abody_subst_abody_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_aexpr_subst_aexpr_upper : lngen.

Lemma fv_abody_subst_abody_upper :
forall ab1 e1 x1,
  fv_abody (subst_abody e1 x1 ab1) [<=] fv_aexpr e1 `union` remove x1 (fv_abody ab1).
Proof.
pose proof fv_aexpr_subst_aexpr_upper_fv_abody_subst_abody_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_abody_subst_abody_upper : lngen.

(* begin hide *)

Lemma fv_binding_subst_binding_upper_mutual :
(forall b1 e1 x1,
  fv_binding (subst_binding e1 x1 b1) [<=] fv_aexpr e1 `union` remove x1 (fv_binding b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_binding_subst_binding_upper :
forall b1 e1 x1,
  fv_binding (subst_binding e1 x1 b1) [<=] fv_aexpr e1 `union` remove x1 (fv_binding b1).
Proof.
pose proof fv_binding_subst_binding_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_binding_subst_binding_upper : lngen.

(* begin hide *)

Lemma fv_obind_subst_obind_upper_mutual :
(forall ob1 e1 x1,
  fv_obind (subst_obind e1 x1 ob1) [<=] fv_aexpr e1 `union` remove x1 (fv_obind ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_obind_subst_obind_upper :
forall ob1 e1 x1,
  fv_obind (subst_obind e1 x1 ob1) [<=] fv_aexpr e1 `union` remove x1 (fv_obind ob1).
Proof.
pose proof fv_obind_subst_obind_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_obind_subst_obind_upper : lngen.

(* begin hide *)

Lemma fv_work_subst_work_upper_fv_worklist_subst_worklist_upper_mutual :
(forall w1 e1 x1,
  fv_work (subst_work e1 x1 w1) [<=] fv_aexpr e1 `union` remove x1 (fv_work w1)) /\
(forall wl1 e1 x1,
  fv_worklist (subst_worklist e1 x1 wl1) [<=] fv_aexpr e1 `union` remove x1 (fv_worklist wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_work_subst_work_upper :
forall w1 e1 x1,
  fv_work (subst_work e1 x1 w1) [<=] fv_aexpr e1 `union` remove x1 (fv_work w1).
Proof.
pose proof fv_work_subst_work_upper_fv_worklist_subst_worklist_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_work_subst_work_upper : lngen.

Lemma fv_worklist_subst_worklist_upper :
forall wl1 e1 x1,
  fv_worklist (subst_worklist e1 x1 wl1) [<=] fv_aexpr e1 `union` remove x1 (fv_worklist wl1).
Proof.
pose proof fv_work_subst_work_upper_fv_worklist_subst_worklist_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_worklist_subst_worklist_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_aexpr_close_aexpr_wrt_aexpr_rec_subst_abody_close_abody_wrt_aexpr_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_aexpr e1 x1 (close_aexpr_wrt_aexpr_rec n1 x2 e2) = close_aexpr_wrt_aexpr_rec n1 x2 (subst_aexpr e1 x1 e2)) /\
(forall ab1 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_abody e1 x1 (close_abody_wrt_aexpr_rec n1 x2 ab1) = close_abody_wrt_aexpr_rec n1 x2 (subst_abody e1 x1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_aexpr_close_aexpr_wrt_aexpr_rec :
forall e2 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_aexpr e1 x1 (close_aexpr_wrt_aexpr_rec n1 x2 e2) = close_aexpr_wrt_aexpr_rec n1 x2 (subst_aexpr e1 x1 e2).
Proof.
pose proof subst_aexpr_close_aexpr_wrt_aexpr_rec_subst_abody_close_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_aexpr_close_aexpr_wrt_aexpr_rec : lngen.

Lemma subst_abody_close_abody_wrt_aexpr_rec :
forall ab1 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_abody e1 x1 (close_abody_wrt_aexpr_rec n1 x2 ab1) = close_abody_wrt_aexpr_rec n1 x2 (subst_abody e1 x1 ab1).
Proof.
pose proof subst_aexpr_close_aexpr_wrt_aexpr_rec_subst_abody_close_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_abody_close_abody_wrt_aexpr_rec : lngen.

(* begin hide *)

Lemma subst_binding_close_binding_wrt_aexpr_rec_mutual :
(forall b1 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_binding e1 x1 (close_binding_wrt_aexpr_rec n1 x2 b1) = close_binding_wrt_aexpr_rec n1 x2 (subst_binding e1 x1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_binding_close_binding_wrt_aexpr_rec :
forall b1 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_binding e1 x1 (close_binding_wrt_aexpr_rec n1 x2 b1) = close_binding_wrt_aexpr_rec n1 x2 (subst_binding e1 x1 b1).
Proof.
pose proof subst_binding_close_binding_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_binding_close_binding_wrt_aexpr_rec : lngen.

(* begin hide *)

Lemma subst_obind_close_obind_wrt_aexpr_rec_mutual :
(forall ob1 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_obind e1 x1 (close_obind_wrt_aexpr_rec n1 x2 ob1) = close_obind_wrt_aexpr_rec n1 x2 (subst_obind e1 x1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obind_close_obind_wrt_aexpr_rec :
forall ob1 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_obind e1 x1 (close_obind_wrt_aexpr_rec n1 x2 ob1) = close_obind_wrt_aexpr_rec n1 x2 (subst_obind e1 x1 ob1).
Proof.
pose proof subst_obind_close_obind_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obind_close_obind_wrt_aexpr_rec : lngen.

(* begin hide *)

Lemma subst_work_close_work_wrt_aexpr_rec_subst_worklist_close_worklist_wrt_aexpr_rec_mutual :
(forall w1 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_work e1 x1 (close_work_wrt_aexpr_rec n1 x2 w1) = close_work_wrt_aexpr_rec n1 x2 (subst_work e1 x1 w1)) /\
(forall wl1 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_worklist e1 x1 (close_worklist_wrt_aexpr_rec n1 x2 wl1) = close_worklist_wrt_aexpr_rec n1 x2 (subst_worklist e1 x1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_work_close_work_wrt_aexpr_rec :
forall w1 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_work e1 x1 (close_work_wrt_aexpr_rec n1 x2 w1) = close_work_wrt_aexpr_rec n1 x2 (subst_work e1 x1 w1).
Proof.
pose proof subst_work_close_work_wrt_aexpr_rec_subst_worklist_close_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_work_close_work_wrt_aexpr_rec : lngen.

Lemma subst_worklist_close_worklist_wrt_aexpr_rec :
forall wl1 e1 x1 x2 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_worklist e1 x1 (close_worklist_wrt_aexpr_rec n1 x2 wl1) = close_worklist_wrt_aexpr_rec n1 x2 (subst_worklist e1 x1 wl1).
Proof.
pose proof subst_work_close_work_wrt_aexpr_rec_subst_worklist_close_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_worklist_close_worklist_wrt_aexpr_rec : lngen.

Lemma subst_aexpr_close_aexpr_wrt_aexpr :
forall e2 e1 x1 x2,
  lc_aexpr e1 ->  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_aexpr e1 x1 (close_aexpr_wrt_aexpr x2 e2) = close_aexpr_wrt_aexpr x2 (subst_aexpr e1 x1 e2).
Proof.
unfold close_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_aexpr_close_aexpr_wrt_aexpr : lngen.

Lemma subst_abody_close_abody_wrt_aexpr :
forall ab1 e1 x1 x2,
  lc_aexpr e1 ->  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_abody e1 x1 (close_abody_wrt_aexpr x2 ab1) = close_abody_wrt_aexpr x2 (subst_abody e1 x1 ab1).
Proof.
unfold close_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_abody_close_abody_wrt_aexpr : lngen.

Lemma subst_binding_close_binding_wrt_aexpr :
forall b1 e1 x1 x2,
  lc_aexpr e1 ->  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_binding e1 x1 (close_binding_wrt_aexpr x2 b1) = close_binding_wrt_aexpr x2 (subst_binding e1 x1 b1).
Proof.
unfold close_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_binding_close_binding_wrt_aexpr : lngen.

Lemma subst_obind_close_obind_wrt_aexpr :
forall ob1 e1 x1 x2,
  lc_aexpr e1 ->  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_obind e1 x1 (close_obind_wrt_aexpr x2 ob1) = close_obind_wrt_aexpr x2 (subst_obind e1 x1 ob1).
Proof.
unfold close_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_obind_close_obind_wrt_aexpr : lngen.

Lemma subst_work_close_work_wrt_aexpr :
forall w1 e1 x1 x2,
  lc_aexpr e1 ->  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_work e1 x1 (close_work_wrt_aexpr x2 w1) = close_work_wrt_aexpr x2 (subst_work e1 x1 w1).
Proof.
unfold close_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_work_close_work_wrt_aexpr : lngen.

Lemma subst_worklist_close_worklist_wrt_aexpr :
forall wl1 e1 x1 x2,
  lc_aexpr e1 ->  x1 <> x2 ->
  x2 `notin` fv_aexpr e1 ->
  subst_worklist e1 x1 (close_worklist_wrt_aexpr x2 wl1) = close_worklist_wrt_aexpr x2 (subst_worklist e1 x1 wl1).
Proof.
unfold close_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_worklist_close_worklist_wrt_aexpr : lngen.

(* begin hide *)

Lemma subst_aexpr_degree_aexpr_wrt_aexpr_subst_abody_degree_abody_wrt_aexpr_mutual :
(forall e1 e2 x1 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_aexpr_wrt_aexpr n1 e2 ->
  degree_aexpr_wrt_aexpr n1 (subst_aexpr e2 x1 e1)) /\
(forall ab1 e1 x1 n1,
  degree_abody_wrt_aexpr n1 ab1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_abody_wrt_aexpr n1 (subst_abody e1 x1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_aexpr_degree_aexpr_wrt_aexpr :
forall e1 e2 x1 n1,
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_aexpr_wrt_aexpr n1 e2 ->
  degree_aexpr_wrt_aexpr n1 (subst_aexpr e2 x1 e1).
Proof.
pose proof subst_aexpr_degree_aexpr_wrt_aexpr_subst_abody_degree_abody_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_aexpr_degree_aexpr_wrt_aexpr : lngen.

Lemma subst_abody_degree_abody_wrt_aexpr :
forall ab1 e1 x1 n1,
  degree_abody_wrt_aexpr n1 ab1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_abody_wrt_aexpr n1 (subst_abody e1 x1 ab1).
Proof.
pose proof subst_aexpr_degree_aexpr_wrt_aexpr_subst_abody_degree_abody_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_abody_degree_abody_wrt_aexpr : lngen.

(* begin hide *)

Lemma subst_binding_degree_binding_wrt_aexpr_mutual :
(forall b1 e1 x1 n1,
  degree_binding_wrt_aexpr n1 b1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_binding_wrt_aexpr n1 (subst_binding e1 x1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_binding_degree_binding_wrt_aexpr :
forall b1 e1 x1 n1,
  degree_binding_wrt_aexpr n1 b1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_binding_wrt_aexpr n1 (subst_binding e1 x1 b1).
Proof.
pose proof subst_binding_degree_binding_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_binding_degree_binding_wrt_aexpr : lngen.

(* begin hide *)

Lemma subst_obind_degree_obind_wrt_aexpr_mutual :
(forall ob1 e1 x1 n1,
  degree_obind_wrt_aexpr n1 ob1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_obind_wrt_aexpr n1 (subst_obind e1 x1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obind_degree_obind_wrt_aexpr :
forall ob1 e1 x1 n1,
  degree_obind_wrt_aexpr n1 ob1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_obind_wrt_aexpr n1 (subst_obind e1 x1 ob1).
Proof.
pose proof subst_obind_degree_obind_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obind_degree_obind_wrt_aexpr : lngen.

(* begin hide *)

Lemma subst_work_degree_work_wrt_aexpr_subst_worklist_degree_worklist_wrt_aexpr_mutual :
(forall w1 e1 x1 n1,
  degree_work_wrt_aexpr n1 w1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_work_wrt_aexpr n1 (subst_work e1 x1 w1)) /\
(forall wl1 e1 x1 n1,
  degree_worklist_wrt_aexpr n1 wl1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_worklist_wrt_aexpr n1 (subst_worklist e1 x1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_work_degree_work_wrt_aexpr :
forall w1 e1 x1 n1,
  degree_work_wrt_aexpr n1 w1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_work_wrt_aexpr n1 (subst_work e1 x1 w1).
Proof.
pose proof subst_work_degree_work_wrt_aexpr_subst_worklist_degree_worklist_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_work_degree_work_wrt_aexpr : lngen.

Lemma subst_worklist_degree_worklist_wrt_aexpr :
forall wl1 e1 x1 n1,
  degree_worklist_wrt_aexpr n1 wl1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  degree_worklist_wrt_aexpr n1 (subst_worklist e1 x1 wl1).
Proof.
pose proof subst_work_degree_work_wrt_aexpr_subst_worklist_degree_worklist_wrt_aexpr_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_worklist_degree_worklist_wrt_aexpr : lngen.

(* begin hide *)

Lemma subst_aexpr_fresh_eq_subst_abody_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_aexpr e2 ->
  subst_aexpr e1 x1 e2 = e2) /\
(forall ab1 e1 x1,
  x1 `notin` fv_abody ab1 ->
  subst_abody e1 x1 ab1 = ab1).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_aexpr_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_aexpr e2 ->
  subst_aexpr e1 x1 e2 = e2.
Proof.
pose proof subst_aexpr_fresh_eq_subst_abody_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_aexpr_fresh_eq : lngen.
Hint Rewrite subst_aexpr_fresh_eq using solve [auto] : lngen.

Lemma subst_abody_fresh_eq :
forall ab1 e1 x1,
  x1 `notin` fv_abody ab1 ->
  subst_abody e1 x1 ab1 = ab1.
Proof.
pose proof subst_aexpr_fresh_eq_subst_abody_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_abody_fresh_eq : lngen.
Hint Rewrite subst_abody_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_binding_fresh_eq_mutual :
(forall b1 e1 x1,
  x1 `notin` fv_binding b1 ->
  subst_binding e1 x1 b1 = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_binding_fresh_eq :
forall b1 e1 x1,
  x1 `notin` fv_binding b1 ->
  subst_binding e1 x1 b1 = b1.
Proof.
pose proof subst_binding_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_binding_fresh_eq : lngen.
Hint Rewrite subst_binding_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_obind_fresh_eq_mutual :
(forall ob1 e1 x1,
  x1 `notin` fv_obind ob1 ->
  subst_obind e1 x1 ob1 = ob1).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obind_fresh_eq :
forall ob1 e1 x1,
  x1 `notin` fv_obind ob1 ->
  subst_obind e1 x1 ob1 = ob1.
Proof.
pose proof subst_obind_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obind_fresh_eq : lngen.
Hint Rewrite subst_obind_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_work_fresh_eq_subst_worklist_fresh_eq_mutual :
(forall w1 e1 x1,
  x1 `notin` fv_work w1 ->
  subst_work e1 x1 w1 = w1) /\
(forall wl1 e1 x1,
  x1 `notin` fv_worklist wl1 ->
  subst_worklist e1 x1 wl1 = wl1).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_work_fresh_eq :
forall w1 e1 x1,
  x1 `notin` fv_work w1 ->
  subst_work e1 x1 w1 = w1.
Proof.
pose proof subst_work_fresh_eq_subst_worklist_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_work_fresh_eq : lngen.
Hint Rewrite subst_work_fresh_eq using solve [auto] : lngen.

Lemma subst_worklist_fresh_eq :
forall wl1 e1 x1,
  x1 `notin` fv_worklist wl1 ->
  subst_worklist e1 x1 wl1 = wl1.
Proof.
pose proof subst_work_fresh_eq_subst_worklist_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_worklist_fresh_eq : lngen.
Hint Rewrite subst_worklist_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_aexpr_fresh_same_subst_abody_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_aexpr (subst_aexpr e1 x1 e2)) /\
(forall ab1 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_abody (subst_abody e1 x1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_aexpr_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_aexpr (subst_aexpr e1 x1 e2).
Proof.
pose proof subst_aexpr_fresh_same_subst_abody_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_aexpr_fresh_same : lngen.

Lemma subst_abody_fresh_same :
forall ab1 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_abody (subst_abody e1 x1 ab1).
Proof.
pose proof subst_aexpr_fresh_same_subst_abody_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_abody_fresh_same : lngen.

(* begin hide *)

Lemma subst_binding_fresh_same_mutual :
(forall b1 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_binding (subst_binding e1 x1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_binding_fresh_same :
forall b1 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_binding (subst_binding e1 x1 b1).
Proof.
pose proof subst_binding_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_binding_fresh_same : lngen.

(* begin hide *)

Lemma subst_obind_fresh_same_mutual :
(forall ob1 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_obind (subst_obind e1 x1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obind_fresh_same :
forall ob1 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_obind (subst_obind e1 x1 ob1).
Proof.
pose proof subst_obind_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obind_fresh_same : lngen.

(* begin hide *)

Lemma subst_work_fresh_same_subst_worklist_fresh_same_mutual :
(forall w1 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_work (subst_work e1 x1 w1)) /\
(forall wl1 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_worklist (subst_worklist e1 x1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_work_fresh_same :
forall w1 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_work (subst_work e1 x1 w1).
Proof.
pose proof subst_work_fresh_same_subst_worklist_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_work_fresh_same : lngen.

Lemma subst_worklist_fresh_same :
forall wl1 e1 x1,
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_worklist (subst_worklist e1 x1 wl1).
Proof.
pose proof subst_work_fresh_same_subst_worklist_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_worklist_fresh_same : lngen.

(* begin hide *)

Lemma subst_aexpr_fresh_subst_abody_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_aexpr e2 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_aexpr (subst_aexpr e1 x2 e2)) /\
(forall ab1 e1 x1 x2,
  x1 `notin` fv_abody ab1 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_abody (subst_abody e1 x2 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_aexpr_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_aexpr e2 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_aexpr (subst_aexpr e1 x2 e2).
Proof.
pose proof subst_aexpr_fresh_subst_abody_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_aexpr_fresh : lngen.

Lemma subst_abody_fresh :
forall ab1 e1 x1 x2,
  x1 `notin` fv_abody ab1 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_abody (subst_abody e1 x2 ab1).
Proof.
pose proof subst_aexpr_fresh_subst_abody_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_abody_fresh : lngen.

(* begin hide *)

Lemma subst_binding_fresh_mutual :
(forall b1 e1 x1 x2,
  x1 `notin` fv_binding b1 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_binding (subst_binding e1 x2 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_binding_fresh :
forall b1 e1 x1 x2,
  x1 `notin` fv_binding b1 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_binding (subst_binding e1 x2 b1).
Proof.
pose proof subst_binding_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_binding_fresh : lngen.

(* begin hide *)

Lemma subst_obind_fresh_mutual :
(forall ob1 e1 x1 x2,
  x1 `notin` fv_obind ob1 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_obind (subst_obind e1 x2 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obind_fresh :
forall ob1 e1 x1 x2,
  x1 `notin` fv_obind ob1 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_obind (subst_obind e1 x2 ob1).
Proof.
pose proof subst_obind_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obind_fresh : lngen.

(* begin hide *)

Lemma subst_work_fresh_subst_worklist_fresh_mutual :
(forall w1 e1 x1 x2,
  x1 `notin` fv_work w1 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_work (subst_work e1 x2 w1)) /\
(forall wl1 e1 x1 x2,
  x1 `notin` fv_worklist wl1 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_worklist (subst_worklist e1 x2 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_work_fresh :
forall w1 e1 x1 x2,
  x1 `notin` fv_work w1 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_work (subst_work e1 x2 w1).
Proof.
pose proof subst_work_fresh_subst_worklist_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_work_fresh : lngen.

Lemma subst_worklist_fresh :
forall wl1 e1 x1 x2,
  x1 `notin` fv_worklist wl1 ->
  x1 `notin` fv_aexpr e1 ->
  x1 `notin` fv_worklist (subst_worklist e1 x2 wl1).
Proof.
pose proof subst_work_fresh_subst_worklist_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_worklist_fresh : lngen.

Lemma subst_aexpr_lc_aexpr :
forall e1 e2 x1,
  lc_aexpr e1 ->
  lc_aexpr e2 ->
  lc_aexpr (subst_aexpr e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_aexpr_lc_aexpr : lngen.

Lemma subst_abody_lc_abody :
forall ab1 e1 x1,
  lc_abody ab1 ->
  lc_aexpr e1 ->
  lc_abody (subst_abody e1 x1 ab1).
Proof.
default_simp.
Qed.

Hint Resolve subst_abody_lc_abody : lngen.

Lemma subst_binding_lc_binding :
forall b1 e1 x1,
  lc_binding b1 ->
  lc_aexpr e1 ->
  lc_binding (subst_binding e1 x1 b1).
Proof.
default_simp.
Qed.

Hint Resolve subst_binding_lc_binding : lngen.

Lemma subst_obind_lc_obind :
forall ob1 e1 x1,
  lc_obind ob1 ->
  lc_aexpr e1 ->
  lc_obind (subst_obind e1 x1 ob1).
Proof.
default_simp.
Qed.

Hint Resolve subst_obind_lc_obind : lngen.

Lemma subst_work_lc_work :
forall w1 e1 x1,
  lc_work w1 ->
  lc_aexpr e1 ->
  lc_work (subst_work e1 x1 w1).
Proof.
default_simp.
Qed.

Hint Resolve subst_work_lc_work : lngen.

Lemma subst_worklist_lc_worklist :
forall wl1 e1 x1,
  lc_worklist wl1 ->
  lc_aexpr e1 ->
  lc_worklist (subst_worklist e1 x1 wl1).
Proof.
default_simp.
Qed.

Hint Resolve subst_worklist_lc_worklist : lngen.

(* begin hide *)

Lemma subst_aexpr_open_aexpr_wrt_aexpr_rec_subst_abody_open_abody_wrt_aexpr_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_aexpr e1 x1 (open_aexpr_wrt_aexpr_rec n1 e2 e3) = open_aexpr_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_aexpr e1 x1 e3)) /\
(forall ab1 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_abody e1 x1 (open_abody_wrt_aexpr_rec n1 e2 ab1) = open_abody_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_abody e1 x1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_aexpr_open_aexpr_wrt_aexpr_rec :
forall e3 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_aexpr e1 x1 (open_aexpr_wrt_aexpr_rec n1 e2 e3) = open_aexpr_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_aexpr e1 x1 e3).
Proof.
pose proof subst_aexpr_open_aexpr_wrt_aexpr_rec_subst_abody_open_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_aexpr_open_aexpr_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_abody_open_abody_wrt_aexpr_rec :
forall ab1 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_abody e1 x1 (open_abody_wrt_aexpr_rec n1 e2 ab1) = open_abody_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_abody e1 x1 ab1).
Proof.
pose proof subst_aexpr_open_aexpr_wrt_aexpr_rec_subst_abody_open_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_abody_open_abody_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_binding_open_binding_wrt_aexpr_rec_mutual :
(forall b1 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_binding e1 x1 (open_binding_wrt_aexpr_rec n1 e2 b1) = open_binding_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_binding e1 x1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_binding_open_binding_wrt_aexpr_rec :
forall b1 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_binding e1 x1 (open_binding_wrt_aexpr_rec n1 e2 b1) = open_binding_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_binding e1 x1 b1).
Proof.
pose proof subst_binding_open_binding_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_binding_open_binding_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_obind_open_obind_wrt_aexpr_rec_mutual :
(forall ob1 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_obind e1 x1 (open_obind_wrt_aexpr_rec n1 e2 ob1) = open_obind_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_obind e1 x1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_obind_open_obind_wrt_aexpr_rec :
forall ob1 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_obind e1 x1 (open_obind_wrt_aexpr_rec n1 e2 ob1) = open_obind_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_obind e1 x1 ob1).
Proof.
pose proof subst_obind_open_obind_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obind_open_obind_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_work_open_work_wrt_aexpr_rec_subst_worklist_open_worklist_wrt_aexpr_rec_mutual :
(forall w1 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_work e1 x1 (open_work_wrt_aexpr_rec n1 e2 w1) = open_work_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_work e1 x1 w1)) /\
(forall wl1 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_worklist e1 x1 (open_worklist_wrt_aexpr_rec n1 e2 wl1) = open_worklist_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_worklist e1 x1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_work_open_work_wrt_aexpr_rec :
forall w1 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_work e1 x1 (open_work_wrt_aexpr_rec n1 e2 w1) = open_work_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_work e1 x1 w1).
Proof.
pose proof subst_work_open_work_wrt_aexpr_rec_subst_worklist_open_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_work_open_work_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_worklist_open_worklist_wrt_aexpr_rec :
forall wl1 e1 e2 x1 n1,
  lc_aexpr e1 ->
  subst_worklist e1 x1 (open_worklist_wrt_aexpr_rec n1 e2 wl1) = open_worklist_wrt_aexpr_rec n1 (subst_aexpr e1 x1 e2) (subst_worklist e1 x1 wl1).
Proof.
pose proof subst_work_open_work_wrt_aexpr_rec_subst_worklist_open_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_worklist_open_worklist_wrt_aexpr_rec : lngen.

(* end hide *)

Lemma subst_aexpr_open_aexpr_wrt_aexpr :
forall e3 e1 e2 x1,
  lc_aexpr e1 ->
  subst_aexpr e1 x1 (open_aexpr_wrt_aexpr e3 e2) = open_aexpr_wrt_aexpr (subst_aexpr e1 x1 e3) (subst_aexpr e1 x1 e2).
Proof.
unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_aexpr_open_aexpr_wrt_aexpr : lngen.

Lemma subst_abody_open_abody_wrt_aexpr :
forall ab1 e1 e2 x1,
  lc_aexpr e1 ->
  subst_abody e1 x1 (open_abody_wrt_aexpr ab1 e2) = open_abody_wrt_aexpr (subst_abody e1 x1 ab1) (subst_aexpr e1 x1 e2).
Proof.
unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_abody_open_abody_wrt_aexpr : lngen.

Lemma subst_binding_open_binding_wrt_aexpr :
forall b1 e1 e2 x1,
  lc_aexpr e1 ->
  subst_binding e1 x1 (open_binding_wrt_aexpr b1 e2) = open_binding_wrt_aexpr (subst_binding e1 x1 b1) (subst_aexpr e1 x1 e2).
Proof.
unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_binding_open_binding_wrt_aexpr : lngen.

Lemma subst_obind_open_obind_wrt_aexpr :
forall ob1 e1 e2 x1,
  lc_aexpr e1 ->
  subst_obind e1 x1 (open_obind_wrt_aexpr ob1 e2) = open_obind_wrt_aexpr (subst_obind e1 x1 ob1) (subst_aexpr e1 x1 e2).
Proof.
unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_obind_open_obind_wrt_aexpr : lngen.

Lemma subst_work_open_work_wrt_aexpr :
forall w1 e1 e2 x1,
  lc_aexpr e1 ->
  subst_work e1 x1 (open_work_wrt_aexpr w1 e2) = open_work_wrt_aexpr (subst_work e1 x1 w1) (subst_aexpr e1 x1 e2).
Proof.
unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_work_open_work_wrt_aexpr : lngen.

Lemma subst_worklist_open_worklist_wrt_aexpr :
forall wl1 e1 e2 x1,
  lc_aexpr e1 ->
  subst_worklist e1 x1 (open_worklist_wrt_aexpr wl1 e2) = open_worklist_wrt_aexpr (subst_worklist e1 x1 wl1) (subst_aexpr e1 x1 e2).
Proof.
unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_worklist_open_worklist_wrt_aexpr : lngen.

Lemma subst_aexpr_open_aexpr_wrt_aexpr_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_aexpr e1 ->
  open_aexpr_wrt_aexpr (subst_aexpr e1 x1 e2) (ae_var_f x2) = subst_aexpr e1 x1 (open_aexpr_wrt_aexpr e2 (ae_var_f x2)).
Proof.
intros; rewrite subst_aexpr_open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_aexpr_open_aexpr_wrt_aexpr_var : lngen.

Lemma subst_abody_open_abody_wrt_aexpr_var :
forall ab1 e1 x1 x2,
  x1 <> x2 ->
  lc_aexpr e1 ->
  open_abody_wrt_aexpr (subst_abody e1 x1 ab1) (ae_var_f x2) = subst_abody e1 x1 (open_abody_wrt_aexpr ab1 (ae_var_f x2)).
Proof.
intros; rewrite subst_abody_open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_abody_open_abody_wrt_aexpr_var : lngen.

Lemma subst_binding_open_binding_wrt_aexpr_var :
forall b1 e1 x1 x2,
  x1 <> x2 ->
  lc_aexpr e1 ->
  open_binding_wrt_aexpr (subst_binding e1 x1 b1) (ae_var_f x2) = subst_binding e1 x1 (open_binding_wrt_aexpr b1 (ae_var_f x2)).
Proof.
intros; rewrite subst_binding_open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_binding_open_binding_wrt_aexpr_var : lngen.

Lemma subst_obind_open_obind_wrt_aexpr_var :
forall ob1 e1 x1 x2,
  x1 <> x2 ->
  lc_aexpr e1 ->
  open_obind_wrt_aexpr (subst_obind e1 x1 ob1) (ae_var_f x2) = subst_obind e1 x1 (open_obind_wrt_aexpr ob1 (ae_var_f x2)).
Proof.
intros; rewrite subst_obind_open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_obind_open_obind_wrt_aexpr_var : lngen.

Lemma subst_work_open_work_wrt_aexpr_var :
forall w1 e1 x1 x2,
  x1 <> x2 ->
  lc_aexpr e1 ->
  open_work_wrt_aexpr (subst_work e1 x1 w1) (ae_var_f x2) = subst_work e1 x1 (open_work_wrt_aexpr w1 (ae_var_f x2)).
Proof.
intros; rewrite subst_work_open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_work_open_work_wrt_aexpr_var : lngen.

Lemma subst_worklist_open_worklist_wrt_aexpr_var :
forall wl1 e1 x1 x2,
  x1 <> x2 ->
  lc_aexpr e1 ->
  open_worklist_wrt_aexpr (subst_worklist e1 x1 wl1) (ae_var_f x2) = subst_worklist e1 x1 (open_worklist_wrt_aexpr wl1 (ae_var_f x2)).
Proof.
intros; rewrite subst_worklist_open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_worklist_open_worklist_wrt_aexpr_var : lngen.

(* begin hide *)

Lemma subst_aexpr_spec_rec_subst_abody_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_aexpr e2 x1 e1 = open_aexpr_wrt_aexpr_rec n1 e2 (close_aexpr_wrt_aexpr_rec n1 x1 e1)) /\
(forall ab1 e1 x1 n1,
  subst_abody e1 x1 ab1 = open_abody_wrt_aexpr_rec n1 e1 (close_abody_wrt_aexpr_rec n1 x1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_aexpr_spec_rec :
forall e1 e2 x1 n1,
  subst_aexpr e2 x1 e1 = open_aexpr_wrt_aexpr_rec n1 e2 (close_aexpr_wrt_aexpr_rec n1 x1 e1).
Proof.
pose proof subst_aexpr_spec_rec_subst_abody_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_aexpr_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_abody_spec_rec :
forall ab1 e1 x1 n1,
  subst_abody e1 x1 ab1 = open_abody_wrt_aexpr_rec n1 e1 (close_abody_wrt_aexpr_rec n1 x1 ab1).
Proof.
pose proof subst_aexpr_spec_rec_subst_abody_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_abody_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_binding_spec_rec_mutual :
(forall b1 e1 x1 n1,
  subst_binding e1 x1 b1 = open_binding_wrt_aexpr_rec n1 e1 (close_binding_wrt_aexpr_rec n1 x1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_binding_spec_rec :
forall b1 e1 x1 n1,
  subst_binding e1 x1 b1 = open_binding_wrt_aexpr_rec n1 e1 (close_binding_wrt_aexpr_rec n1 x1 b1).
Proof.
pose proof subst_binding_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_binding_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_obind_spec_rec_mutual :
(forall ob1 e1 x1 n1,
  subst_obind e1 x1 ob1 = open_obind_wrt_aexpr_rec n1 e1 (close_obind_wrt_aexpr_rec n1 x1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_obind_spec_rec :
forall ob1 e1 x1 n1,
  subst_obind e1 x1 ob1 = open_obind_wrt_aexpr_rec n1 e1 (close_obind_wrt_aexpr_rec n1 x1 ob1).
Proof.
pose proof subst_obind_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obind_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_work_spec_rec_subst_worklist_spec_rec_mutual :
(forall w1 e1 x1 n1,
  subst_work e1 x1 w1 = open_work_wrt_aexpr_rec n1 e1 (close_work_wrt_aexpr_rec n1 x1 w1)) /\
(forall wl1 e1 x1 n1,
  subst_worklist e1 x1 wl1 = open_worklist_wrt_aexpr_rec n1 e1 (close_worklist_wrt_aexpr_rec n1 x1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_work_spec_rec :
forall w1 e1 x1 n1,
  subst_work e1 x1 w1 = open_work_wrt_aexpr_rec n1 e1 (close_work_wrt_aexpr_rec n1 x1 w1).
Proof.
pose proof subst_work_spec_rec_subst_worklist_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_work_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_worklist_spec_rec :
forall wl1 e1 x1 n1,
  subst_worklist e1 x1 wl1 = open_worklist_wrt_aexpr_rec n1 e1 (close_worklist_wrt_aexpr_rec n1 x1 wl1).
Proof.
pose proof subst_work_spec_rec_subst_worklist_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_worklist_spec_rec : lngen.

(* end hide *)

Lemma subst_aexpr_spec :
forall e1 e2 x1,
  subst_aexpr e2 x1 e1 = open_aexpr_wrt_aexpr (close_aexpr_wrt_aexpr x1 e1) e2.
Proof.
unfold close_aexpr_wrt_aexpr; unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_aexpr_spec : lngen.

Lemma subst_abody_spec :
forall ab1 e1 x1,
  subst_abody e1 x1 ab1 = open_abody_wrt_aexpr (close_abody_wrt_aexpr x1 ab1) e1.
Proof.
unfold close_abody_wrt_aexpr; unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_abody_spec : lngen.

Lemma subst_binding_spec :
forall b1 e1 x1,
  subst_binding e1 x1 b1 = open_binding_wrt_aexpr (close_binding_wrt_aexpr x1 b1) e1.
Proof.
unfold close_binding_wrt_aexpr; unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_binding_spec : lngen.

Lemma subst_obind_spec :
forall ob1 e1 x1,
  subst_obind e1 x1 ob1 = open_obind_wrt_aexpr (close_obind_wrt_aexpr x1 ob1) e1.
Proof.
unfold close_obind_wrt_aexpr; unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_obind_spec : lngen.

Lemma subst_work_spec :
forall w1 e1 x1,
  subst_work e1 x1 w1 = open_work_wrt_aexpr (close_work_wrt_aexpr x1 w1) e1.
Proof.
unfold close_work_wrt_aexpr; unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_work_spec : lngen.

Lemma subst_worklist_spec :
forall wl1 e1 x1,
  subst_worklist e1 x1 wl1 = open_worklist_wrt_aexpr (close_worklist_wrt_aexpr x1 wl1) e1.
Proof.
unfold close_worklist_wrt_aexpr; unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_worklist_spec : lngen.

(* begin hide *)

Lemma subst_aexpr_subst_aexpr_subst_abody_subst_abody_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_aexpr e2 ->
  x2 <> x1 ->
  subst_aexpr e2 x1 (subst_aexpr e3 x2 e1) = subst_aexpr (subst_aexpr e2 x1 e3) x2 (subst_aexpr e2 x1 e1)) /\
(forall ab1 e1 e2 x2 x1,
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  subst_abody e1 x1 (subst_abody e2 x2 ab1) = subst_abody (subst_aexpr e1 x1 e2) x2 (subst_abody e1 x1 ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_aexpr_subst_aexpr :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_aexpr e2 ->
  x2 <> x1 ->
  subst_aexpr e2 x1 (subst_aexpr e3 x2 e1) = subst_aexpr (subst_aexpr e2 x1 e3) x2 (subst_aexpr e2 x1 e1).
Proof.
pose proof subst_aexpr_subst_aexpr_subst_abody_subst_abody_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_aexpr_subst_aexpr : lngen.

Lemma subst_abody_subst_abody :
forall ab1 e1 e2 x2 x1,
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  subst_abody e1 x1 (subst_abody e2 x2 ab1) = subst_abody (subst_aexpr e1 x1 e2) x2 (subst_abody e1 x1 ab1).
Proof.
pose proof subst_aexpr_subst_aexpr_subst_abody_subst_abody_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_abody_subst_abody : lngen.

(* begin hide *)

Lemma subst_binding_subst_binding_mutual :
(forall b1 e1 e2 x2 x1,
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  subst_binding e1 x1 (subst_binding e2 x2 b1) = subst_binding (subst_aexpr e1 x1 e2) x2 (subst_binding e1 x1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_binding_subst_binding :
forall b1 e1 e2 x2 x1,
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  subst_binding e1 x1 (subst_binding e2 x2 b1) = subst_binding (subst_aexpr e1 x1 e2) x2 (subst_binding e1 x1 b1).
Proof.
pose proof subst_binding_subst_binding_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_binding_subst_binding : lngen.

(* begin hide *)

Lemma subst_obind_subst_obind_mutual :
(forall ob1 e1 e2 x2 x1,
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  subst_obind e1 x1 (subst_obind e2 x2 ob1) = subst_obind (subst_aexpr e1 x1 e2) x2 (subst_obind e1 x1 ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obind_subst_obind :
forall ob1 e1 e2 x2 x1,
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  subst_obind e1 x1 (subst_obind e2 x2 ob1) = subst_obind (subst_aexpr e1 x1 e2) x2 (subst_obind e1 x1 ob1).
Proof.
pose proof subst_obind_subst_obind_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obind_subst_obind : lngen.

(* begin hide *)

Lemma subst_work_subst_work_subst_worklist_subst_worklist_mutual :
(forall w1 e1 e2 x2 x1,
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  subst_work e1 x1 (subst_work e2 x2 w1) = subst_work (subst_aexpr e1 x1 e2) x2 (subst_work e1 x1 w1)) /\
(forall wl1 e1 e2 x2 x1,
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  subst_worklist e1 x1 (subst_worklist e2 x2 wl1) = subst_worklist (subst_aexpr e1 x1 e2) x2 (subst_worklist e1 x1 wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_work_subst_work :
forall w1 e1 e2 x2 x1,
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  subst_work e1 x1 (subst_work e2 x2 w1) = subst_work (subst_aexpr e1 x1 e2) x2 (subst_work e1 x1 w1).
Proof.
pose proof subst_work_subst_work_subst_worklist_subst_worklist_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_work_subst_work : lngen.

Lemma subst_worklist_subst_worklist :
forall wl1 e1 e2 x2 x1,
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  subst_worklist e1 x1 (subst_worklist e2 x2 wl1) = subst_worklist (subst_aexpr e1 x1 e2) x2 (subst_worklist e1 x1 wl1).
Proof.
pose proof subst_work_subst_work_subst_worklist_subst_worklist_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_worklist_subst_worklist : lngen.

(* begin hide *)

Lemma subst_aexpr_close_aexpr_wrt_aexpr_rec_open_aexpr_wrt_aexpr_rec_subst_abody_close_abody_wrt_aexpr_rec_open_abody_wrt_aexpr_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_aexpr e2 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_aexpr e1 x1 e2 = close_aexpr_wrt_aexpr_rec n1 x2 (subst_aexpr e1 x1 (open_aexpr_wrt_aexpr_rec n1 (ae_var_f x2) e2))) *
(forall ab1 e1 x1 x2 n1,
  x2 `notin` fv_abody ab1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_abody e1 x1 ab1 = close_abody_wrt_aexpr_rec n1 x2 (subst_abody e1 x1 (open_abody_wrt_aexpr_rec n1 (ae_var_f x2) ab1))).
Proof.
apply_mutual_ind aexpr_abody_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_aexpr_close_aexpr_wrt_aexpr_rec_open_aexpr_wrt_aexpr_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_aexpr e2 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_aexpr e1 x1 e2 = close_aexpr_wrt_aexpr_rec n1 x2 (subst_aexpr e1 x1 (open_aexpr_wrt_aexpr_rec n1 (ae_var_f x2) e2)).
Proof.
pose proof subst_aexpr_close_aexpr_wrt_aexpr_rec_open_aexpr_wrt_aexpr_rec_subst_abody_close_abody_wrt_aexpr_rec_open_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_aexpr_close_aexpr_wrt_aexpr_rec_open_aexpr_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_abody_close_abody_wrt_aexpr_rec_open_abody_wrt_aexpr_rec :
forall ab1 e1 x1 x2 n1,
  x2 `notin` fv_abody ab1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_abody e1 x1 ab1 = close_abody_wrt_aexpr_rec n1 x2 (subst_abody e1 x1 (open_abody_wrt_aexpr_rec n1 (ae_var_f x2) ab1)).
Proof.
pose proof subst_aexpr_close_aexpr_wrt_aexpr_rec_open_aexpr_wrt_aexpr_rec_subst_abody_close_abody_wrt_aexpr_rec_open_abody_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_abody_close_abody_wrt_aexpr_rec_open_abody_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_binding_close_binding_wrt_aexpr_rec_open_binding_wrt_aexpr_rec_mutual :
(forall b1 e1 x1 x2 n1,
  x2 `notin` fv_binding b1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_binding e1 x1 b1 = close_binding_wrt_aexpr_rec n1 x2 (subst_binding e1 x1 (open_binding_wrt_aexpr_rec n1 (ae_var_f x2) b1))).
Proof.
apply_mutual_ind binding_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_binding_close_binding_wrt_aexpr_rec_open_binding_wrt_aexpr_rec :
forall b1 e1 x1 x2 n1,
  x2 `notin` fv_binding b1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_binding e1 x1 b1 = close_binding_wrt_aexpr_rec n1 x2 (subst_binding e1 x1 (open_binding_wrt_aexpr_rec n1 (ae_var_f x2) b1)).
Proof.
pose proof subst_binding_close_binding_wrt_aexpr_rec_open_binding_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_binding_close_binding_wrt_aexpr_rec_open_binding_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_obind_close_obind_wrt_aexpr_rec_open_obind_wrt_aexpr_rec_mutual :
(forall ob1 e1 x1 x2 n1,
  x2 `notin` fv_obind ob1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_obind e1 x1 ob1 = close_obind_wrt_aexpr_rec n1 x2 (subst_obind e1 x1 (open_obind_wrt_aexpr_rec n1 (ae_var_f x2) ob1))).
Proof.
apply_mutual_ind obind_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_obind_close_obind_wrt_aexpr_rec_open_obind_wrt_aexpr_rec :
forall ob1 e1 x1 x2 n1,
  x2 `notin` fv_obind ob1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_obind e1 x1 ob1 = close_obind_wrt_aexpr_rec n1 x2 (subst_obind e1 x1 (open_obind_wrt_aexpr_rec n1 (ae_var_f x2) ob1)).
Proof.
pose proof subst_obind_close_obind_wrt_aexpr_rec_open_obind_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obind_close_obind_wrt_aexpr_rec_open_obind_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_work_close_work_wrt_aexpr_rec_open_work_wrt_aexpr_rec_subst_worklist_close_worklist_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec_mutual :
(forall w1 e1 x1 x2 n1,
  x2 `notin` fv_work w1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_work e1 x1 w1 = close_work_wrt_aexpr_rec n1 x2 (subst_work e1 x1 (open_work_wrt_aexpr_rec n1 (ae_var_f x2) w1))) *
(forall wl1 e1 x1 x2 n1,
  x2 `notin` fv_worklist wl1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_worklist e1 x1 wl1 = close_worklist_wrt_aexpr_rec n1 x2 (subst_worklist e1 x1 (open_worklist_wrt_aexpr_rec n1 (ae_var_f x2) wl1))).
Proof.
apply_mutual_ind work_worklist_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_work_close_work_wrt_aexpr_rec_open_work_wrt_aexpr_rec :
forall w1 e1 x1 x2 n1,
  x2 `notin` fv_work w1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_work e1 x1 w1 = close_work_wrt_aexpr_rec n1 x2 (subst_work e1 x1 (open_work_wrt_aexpr_rec n1 (ae_var_f x2) w1)).
Proof.
pose proof subst_work_close_work_wrt_aexpr_rec_open_work_wrt_aexpr_rec_subst_worklist_close_worklist_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_work_close_work_wrt_aexpr_rec_open_work_wrt_aexpr_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_worklist_close_worklist_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec :
forall wl1 e1 x1 x2 n1,
  x2 `notin` fv_worklist wl1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  degree_aexpr_wrt_aexpr n1 e1 ->
  subst_worklist e1 x1 wl1 = close_worklist_wrt_aexpr_rec n1 x2 (subst_worklist e1 x1 (open_worklist_wrt_aexpr_rec n1 (ae_var_f x2) wl1)).
Proof.
pose proof subst_work_close_work_wrt_aexpr_rec_open_work_wrt_aexpr_rec_subst_worklist_close_worklist_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_worklist_close_worklist_wrt_aexpr_rec_open_worklist_wrt_aexpr_rec : lngen.

(* end hide *)

Lemma subst_aexpr_close_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr :
forall e2 e1 x1 x2,
  x2 `notin` fv_aexpr e2 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  lc_aexpr e1 ->
  subst_aexpr e1 x1 e2 = close_aexpr_wrt_aexpr x2 (subst_aexpr e1 x1 (open_aexpr_wrt_aexpr e2 (ae_var_f x2))).
Proof.
unfold close_aexpr_wrt_aexpr; unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_aexpr_close_aexpr_wrt_aexpr_open_aexpr_wrt_aexpr : lngen.

Lemma subst_abody_close_abody_wrt_aexpr_open_abody_wrt_aexpr :
forall ab1 e1 x1 x2,
  x2 `notin` fv_abody ab1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  lc_aexpr e1 ->
  subst_abody e1 x1 ab1 = close_abody_wrt_aexpr x2 (subst_abody e1 x1 (open_abody_wrt_aexpr ab1 (ae_var_f x2))).
Proof.
unfold close_abody_wrt_aexpr; unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_abody_close_abody_wrt_aexpr_open_abody_wrt_aexpr : lngen.

Lemma subst_binding_close_binding_wrt_aexpr_open_binding_wrt_aexpr :
forall b1 e1 x1 x2,
  x2 `notin` fv_binding b1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  lc_aexpr e1 ->
  subst_binding e1 x1 b1 = close_binding_wrt_aexpr x2 (subst_binding e1 x1 (open_binding_wrt_aexpr b1 (ae_var_f x2))).
Proof.
unfold close_binding_wrt_aexpr; unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_binding_close_binding_wrt_aexpr_open_binding_wrt_aexpr : lngen.

Lemma subst_obind_close_obind_wrt_aexpr_open_obind_wrt_aexpr :
forall ob1 e1 x1 x2,
  x2 `notin` fv_obind ob1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  lc_aexpr e1 ->
  subst_obind e1 x1 ob1 = close_obind_wrt_aexpr x2 (subst_obind e1 x1 (open_obind_wrt_aexpr ob1 (ae_var_f x2))).
Proof.
unfold close_obind_wrt_aexpr; unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_obind_close_obind_wrt_aexpr_open_obind_wrt_aexpr : lngen.

Lemma subst_work_close_work_wrt_aexpr_open_work_wrt_aexpr :
forall w1 e1 x1 x2,
  x2 `notin` fv_work w1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  lc_aexpr e1 ->
  subst_work e1 x1 w1 = close_work_wrt_aexpr x2 (subst_work e1 x1 (open_work_wrt_aexpr w1 (ae_var_f x2))).
Proof.
unfold close_work_wrt_aexpr; unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_work_close_work_wrt_aexpr_open_work_wrt_aexpr : lngen.

Lemma subst_worklist_close_worklist_wrt_aexpr_open_worklist_wrt_aexpr :
forall wl1 e1 x1 x2,
  x2 `notin` fv_worklist wl1 ->
  x2 `notin` fv_aexpr e1 ->
  x2 <> x1 ->
  lc_aexpr e1 ->
  subst_worklist e1 x1 wl1 = close_worklist_wrt_aexpr x2 (subst_worklist e1 x1 (open_worklist_wrt_aexpr wl1 (ae_var_f x2))).
Proof.
unfold close_worklist_wrt_aexpr; unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_worklist_close_worklist_wrt_aexpr_open_worklist_wrt_aexpr : lngen.

Lemma subst_aexpr_ae_abs :
forall x2 A1 ab1 e1 x1,
  lc_aexpr e1 ->
  x2 `notin` fv_aexpr e1 `union` fv_abody ab1 `union` singleton x1 ->
  subst_aexpr e1 x1 (ae_abs A1 ab1) = ae_abs (subst_aexpr e1 x1 A1) (close_abody_wrt_aexpr x2 (subst_abody e1 x1 (open_abody_wrt_aexpr ab1 (ae_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_aexpr_ae_abs : lngen.

Lemma subst_aexpr_ae_pi :
forall x2 A1 B1 e1 x1,
  lc_aexpr e1 ->
  x2 `notin` fv_aexpr e1 `union` fv_aexpr B1 `union` singleton x1 ->
  subst_aexpr e1 x1 (ae_pi A1 B1) = ae_pi (subst_aexpr e1 x1 A1) (close_aexpr_wrt_aexpr x2 (subst_aexpr e1 x1 (open_aexpr_wrt_aexpr B1 (ae_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_aexpr_ae_pi : lngen.

Lemma subst_aexpr_ae_bind :
forall x2 A1 ab1 e1 x1,
  lc_aexpr e1 ->
  x2 `notin` fv_aexpr e1 `union` fv_abody ab1 `union` singleton x1 ->
  subst_aexpr e1 x1 (ae_bind A1 ab1) = ae_bind (subst_aexpr e1 x1 A1) (close_abody_wrt_aexpr x2 (subst_abody e1 x1 (open_abody_wrt_aexpr ab1 (ae_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_aexpr_ae_bind : lngen.

Lemma subst_aexpr_ae_all :
forall x2 A1 B1 e1 x1,
  lc_aexpr e1 ->
  x2 `notin` fv_aexpr e1 `union` fv_aexpr B1 `union` singleton x1 ->
  subst_aexpr e1 x1 (ae_all A1 B1) = ae_all (subst_aexpr e1 x1 A1) (close_aexpr_wrt_aexpr x2 (subst_aexpr e1 x1 (open_aexpr_wrt_aexpr B1 (ae_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_aexpr_ae_all : lngen.

Lemma subst_work_w_infer :
forall x2 e2 e3 wl1 e1 x1,
  lc_aexpr e1 ->
  x2 `notin` fv_aexpr e1 `union` fv_worklist wl1 `union` singleton x1 ->
  subst_work e1 x1 (w_infer e2 e3 wl1) = w_infer (subst_aexpr e1 x1 e2) (subst_aexpr e1 x1 e3) (close_worklist_wrt_aexpr x2 (subst_worklist e1 x1 (open_worklist_wrt_aexpr wl1 (ae_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_work_w_infer : lngen.

Lemma subst_work_w_infer_app :
forall x2 A1 e2 e3 wl1 e1 x1,
  lc_aexpr e1 ->
  x2 `notin` fv_aexpr e1 `union` fv_worklist wl1 `union` singleton x1 ->
  subst_work e1 x1 (w_infer_app A1 e2 e3 wl1) = w_infer_app (subst_aexpr e1 x1 A1) (subst_aexpr e1 x1 e2) (subst_aexpr e1 x1 e3) (close_worklist_wrt_aexpr x2 (subst_worklist e1 x1 (open_worklist_wrt_aexpr wl1 (ae_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_work_w_infer_app : lngen.

Lemma subst_work_w_reduce :
forall x2 e2 wl1 e1 x1,
  lc_aexpr e1 ->
  x2 `notin` fv_aexpr e1 `union` fv_worklist wl1 `union` singleton x1 ->
  subst_work e1 x1 (w_reduce e2 wl1) = w_reduce (subst_aexpr e1 x1 e2) (close_worklist_wrt_aexpr x2 (subst_worklist e1 x1 (open_worklist_wrt_aexpr wl1 (ae_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_work_w_reduce : lngen.

(* begin hide *)

Lemma subst_aexpr_intro_rec_subst_abody_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_aexpr e1 ->
  open_aexpr_wrt_aexpr_rec n1 e2 e1 = subst_aexpr e2 x1 (open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) e1)) /\
(forall ab1 x1 e1 n1,
  x1 `notin` fv_abody ab1 ->
  open_abody_wrt_aexpr_rec n1 e1 ab1 = subst_abody e1 x1 (open_abody_wrt_aexpr_rec n1 (ae_var_f x1) ab1)).
Proof.
apply_mutual_ind aexpr_abody_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_aexpr_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_aexpr e1 ->
  open_aexpr_wrt_aexpr_rec n1 e2 e1 = subst_aexpr e2 x1 (open_aexpr_wrt_aexpr_rec n1 (ae_var_f x1) e1).
Proof.
pose proof subst_aexpr_intro_rec_subst_abody_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_aexpr_intro_rec : lngen.
Hint Rewrite subst_aexpr_intro_rec using solve [auto] : lngen.

Lemma subst_abody_intro_rec :
forall ab1 x1 e1 n1,
  x1 `notin` fv_abody ab1 ->
  open_abody_wrt_aexpr_rec n1 e1 ab1 = subst_abody e1 x1 (open_abody_wrt_aexpr_rec n1 (ae_var_f x1) ab1).
Proof.
pose proof subst_aexpr_intro_rec_subst_abody_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_abody_intro_rec : lngen.
Hint Rewrite subst_abody_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_binding_intro_rec_mutual :
(forall b1 x1 e1 n1,
  x1 `notin` fv_binding b1 ->
  open_binding_wrt_aexpr_rec n1 e1 b1 = subst_binding e1 x1 (open_binding_wrt_aexpr_rec n1 (ae_var_f x1) b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_binding_intro_rec :
forall b1 x1 e1 n1,
  x1 `notin` fv_binding b1 ->
  open_binding_wrt_aexpr_rec n1 e1 b1 = subst_binding e1 x1 (open_binding_wrt_aexpr_rec n1 (ae_var_f x1) b1).
Proof.
pose proof subst_binding_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_binding_intro_rec : lngen.
Hint Rewrite subst_binding_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_obind_intro_rec_mutual :
(forall ob1 x1 e1 n1,
  x1 `notin` fv_obind ob1 ->
  open_obind_wrt_aexpr_rec n1 e1 ob1 = subst_obind e1 x1 (open_obind_wrt_aexpr_rec n1 (ae_var_f x1) ob1)).
Proof.
apply_mutual_ind obind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_obind_intro_rec :
forall ob1 x1 e1 n1,
  x1 `notin` fv_obind ob1 ->
  open_obind_wrt_aexpr_rec n1 e1 ob1 = subst_obind e1 x1 (open_obind_wrt_aexpr_rec n1 (ae_var_f x1) ob1).
Proof.
pose proof subst_obind_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_obind_intro_rec : lngen.
Hint Rewrite subst_obind_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_work_intro_rec_subst_worklist_intro_rec_mutual :
(forall w1 x1 e1 n1,
  x1 `notin` fv_work w1 ->
  open_work_wrt_aexpr_rec n1 e1 w1 = subst_work e1 x1 (open_work_wrt_aexpr_rec n1 (ae_var_f x1) w1)) /\
(forall wl1 x1 e1 n1,
  x1 `notin` fv_worklist wl1 ->
  open_worklist_wrt_aexpr_rec n1 e1 wl1 = subst_worklist e1 x1 (open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) wl1)).
Proof.
apply_mutual_ind work_worklist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_work_intro_rec :
forall w1 x1 e1 n1,
  x1 `notin` fv_work w1 ->
  open_work_wrt_aexpr_rec n1 e1 w1 = subst_work e1 x1 (open_work_wrt_aexpr_rec n1 (ae_var_f x1) w1).
Proof.
pose proof subst_work_intro_rec_subst_worklist_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_work_intro_rec : lngen.
Hint Rewrite subst_work_intro_rec using solve [auto] : lngen.

Lemma subst_worklist_intro_rec :
forall wl1 x1 e1 n1,
  x1 `notin` fv_worklist wl1 ->
  open_worklist_wrt_aexpr_rec n1 e1 wl1 = subst_worklist e1 x1 (open_worklist_wrt_aexpr_rec n1 (ae_var_f x1) wl1).
Proof.
pose proof subst_work_intro_rec_subst_worklist_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_worklist_intro_rec : lngen.
Hint Rewrite subst_worklist_intro_rec using solve [auto] : lngen.

Lemma subst_aexpr_intro :
forall x1 e1 e2,
  x1 `notin` fv_aexpr e1 ->
  open_aexpr_wrt_aexpr e1 e2 = subst_aexpr e2 x1 (open_aexpr_wrt_aexpr e1 (ae_var_f x1)).
Proof.
unfold open_aexpr_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_aexpr_intro : lngen.

Lemma subst_abody_intro :
forall x1 ab1 e1,
  x1 `notin` fv_abody ab1 ->
  open_abody_wrt_aexpr ab1 e1 = subst_abody e1 x1 (open_abody_wrt_aexpr ab1 (ae_var_f x1)).
Proof.
unfold open_abody_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_abody_intro : lngen.

Lemma subst_binding_intro :
forall x1 b1 e1,
  x1 `notin` fv_binding b1 ->
  open_binding_wrt_aexpr b1 e1 = subst_binding e1 x1 (open_binding_wrt_aexpr b1 (ae_var_f x1)).
Proof.
unfold open_binding_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_binding_intro : lngen.

Lemma subst_obind_intro :
forall x1 ob1 e1,
  x1 `notin` fv_obind ob1 ->
  open_obind_wrt_aexpr ob1 e1 = subst_obind e1 x1 (open_obind_wrt_aexpr ob1 (ae_var_f x1)).
Proof.
unfold open_obind_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_obind_intro : lngen.

Lemma subst_work_intro :
forall x1 w1 e1,
  x1 `notin` fv_work w1 ->
  open_work_wrt_aexpr w1 e1 = subst_work e1 x1 (open_work_wrt_aexpr w1 (ae_var_f x1)).
Proof.
unfold open_work_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_work_intro : lngen.

Lemma subst_worklist_intro :
forall x1 wl1 e1,
  x1 `notin` fv_worklist wl1 ->
  open_worklist_wrt_aexpr wl1 e1 = subst_worklist e1 x1 (open_worklist_wrt_aexpr wl1 (ae_var_f x1)).
Proof.
unfold open_worklist_wrt_aexpr; default_simp.
Qed.

Hint Resolve subst_worklist_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
