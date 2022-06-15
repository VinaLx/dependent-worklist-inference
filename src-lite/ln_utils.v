Require Export Metalib.Metatheory.
Require Import Utf8.

Require Import decl.ln_inf.
Require Import bidir.ln_inf.

Ltac inst_cofinite_impl H x :=
  match type of H with
  | forall x, x `notin` ?L -> _ =>
      let Fr := fresh "Fr" in
      assert (x `notin` L) as Fr by auto;
      specialize (H x Fr); clear Fr
  end
.

Ltac inst_cofinites_with x :=
  repeat
    match goal with
    | H : forall x0, x0 `notin` ?L → _ |- _ =>
      inst_cofinite_impl H x
    end
.

(* Assuming the variable is created just for cofinite instantiation.
   It's cleared if nothing to instantiate *)
Ltac inst_cofinites_with' x :=
  match goal with
  | _ : forall x0, x0 `notin` ?L → _ |- _ =>
      inst_cofinites_with x
  end ||
    (clear x; fail "No cofinite quantification can be instantiated")
.

Ltac inst_cofinites :=
  match goal with
  | x : atom |- _ => inst_cofinites_with x
  end.

Ltac inst_cofinites_with_new :=
  let x := fresh "x" in
  pick fresh x; inst_cofinites_with x.

Ltac inst_cofinites_with_new' :=
  let x := fresh "x" in
  pick fresh x; inst_cofinites_with' x.

Ltac inst_cofinites_by F :=
  let L := F in
  let x := fresh "x" in
  pick fresh x for L; inst_cofinites_with x.

Ltac inst_cofinites_by' F :=
  let L := F in
  let x := fresh "x" in
  pick fresh x for L; inst_cofinites_with' x.

Ltac solve_lc_expr :=
  repeat
    match goal with
    | _ : _ |- lc_expr (e_abs ?e1 ?e2)  => inst_cofinites_with_new; eapply lc_e_abs_exists; intuition; eauto; econstructor;
                                           fold open_expr_wrt_expr_rec; intuition; eauto
    | _ : _ |- lc_expr (e_pi ?e1 ?e2)   => inst_cofinites_with_new; eapply lc_e_pi_exists; intuition; eauto
    | _ : _ |- lc_expr (e_all ?e1 ?e2)  => inst_cofinites_with_new; eapply lc_e_all_exists; intuition; eauto
    | _ : _ |- lc_expr (e_bind ?e1 ?e2) => inst_cofinites_with_new; eapply lc_e_bind_exists; intuition; eauto; econstructor;
                                           fold open_expr_wrt_expr_rec; intuition; eauto
    end; auto.


Ltac solve_lc_bexpr :=
  repeat
    match goal with
    | _ : _ |- lc_bexpr (be_abs ?e1 ?e2)  => inst_cofinites_with_new; eapply lc_be_abs_exists; intuition; eauto;
                                             econstructor; fold open_expr_wrt_expr_rec; intuition; eauto
    | _ : _ |- lc_bexpr (be_pi ?e1 ?e2)   => inst_cofinites_with_new; eapply lc_be_pi_exists; intuition; eauto
    | _ : _ |- lc_bexpr (be_all ?e1 ?e2)  => inst_cofinites_with_new; eapply lc_be_all_exists; intuition; eauto
    | _ : _ |- lc_bexpr (be_bind ?e1 ?e2) => inst_cofinites_with_new; eapply lc_be_bind_exists; intuition; eauto; econstructor;
                                            fold open_expr_wrt_expr_rec; intuition; eauto
    end.
