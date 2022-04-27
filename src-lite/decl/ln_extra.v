Require Import decl.ott.
Require Export decl.notations.


Scheme expr_ind_mut 
    := Induction for expr Sort Prop
  with Induction for body Sort Prop.

Lemma notin_fv_open_rec : forall x e1 e2 n,
  x `notin` fv_expr (open_expr_wrt_expr_rec n e2 e1) -> x `notin` fv_expr e1.
Proof.
  intros. generalize dependent n.
  pattern e1. 
  eapply expr_ind_mut with (
    P0 := fun b => forall n, x `notin` fv_body (open_body_wrt_expr_rec (S n) e2 b) -> x `notin` fv_body b
  )
  ; simpl; intros; eauto.
Qed.

Lemma notin_fv_open_var : forall x e y,
    x `notin` fv_expr (e ^^` y) -> x `notin` fv_expr e.
Proof.
  eauto using notin_fv_open_rec.
Qed.

Lemma notin_fv_open : forall x e1 e2,
    x `notin` fv_expr (e1 ^^ e2) -> x `notin` fv_expr e1.
Proof.
  eauto using notin_fv_open_rec.
Qed.

Lemma open_subst_eq : forall e x v, 
  x `notin` fv_expr e -> lc_expr v  ->
    e ^^ v = [v /_ x] e ^^ `x.
Proof.
  intros.  
  rewrite subst_expr_open_expr_wrt_expr. simpl.
  rewrite eq_dec_refl.
  rewrite subst_expr_fresh_eq.
  all : auto.
Qed. 