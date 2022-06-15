Require Export bidir.notations.

Scheme bexpr_mut := Induction for bexpr Sort Prop
  with bbody_mut := Induction for bbody Sort Prop.

Lemma bexpr_subst_open_comm : forall x v1 e v2
  , lc_bexpr v1 → x `notin` fv_bexpr v2
  → ([v1 /' x] e) ^^' v2 = [v1 /' x] e ^^' v2.
Proof.
  intros.
  rewrite subst_bexpr_open_bexpr_wrt_bexpr.
  rewrite (subst_bexpr_fresh_eq v2).
  all: easy.
Qed.

Lemma bbody_subst_open_comm : forall x v1 b v2
  , lc_bexpr v1 → x `notin` fv_bexpr v2
    → open_bbody_wrt_bexpr (subst_bbody v1 x b) v2
      = subst_bbody v1 x (open_bbody_wrt_bexpr b v2).
Proof.
  intros.
  rewrite subst_bbody_open_bbody_wrt_bexpr.
  rewrite (subst_bexpr_fresh_eq v2).
  all: easy.
Qed.

(*
Lemma dworklist_subst_open_comm : forall x v1 Γ v2
  , lc_bexpr v1 → x `notin` fv_bexpr v2
  → subst_dworklist v1 x Γ $ v2 = subst_dworklist v1 x (Γ $ v2).
Proof.
  intros.
  rewrite subst_dworklist_open_dworklist_wrt_bexpr.
  rewrite (subst_bexpr_fresh_eq v2).
  all: easy.
Qed.
*)

Lemma bexpr_open_r_close_l : forall e1 e2 x
  , x `notin` fv_bexpr e2
  → e1 = e2 ^`' x → e1 \`' x = e2.
Proof.
  intros * Fr H.
  assert (e1 \`' x = e2 ^`' x \`' x) by now rewrite H.
  now rewrite close_bexpr_wrt_bexpr_open_bexpr_wrt_bexpr in H0.
Qed.

Lemma bbody_open_r_close_l : forall b1 b2 x
  , x `notin` fv_bbody b2
  → b1 = open_bbody_wrt_bexpr b2 `'x → close_bbody_wrt_bexpr x b1 = b2.
Proof.
  intros * Fr H.
  assert (close_bbody_wrt_bexpr x b1 = close_bbody_wrt_bexpr x (open_bbody_wrt_bexpr b2 `'x)) by now rewrite H.
  now rewrite close_bbody_wrt_bexpr_open_bbody_wrt_bexpr in H0.
Qed.

Lemma close_bexpr_notin_rec : forall x e n,
    x `notin` fv_bexpr (close_bexpr_wrt_bexpr_rec n x e).
Proof.
  intros until e.

  induction e using bexpr_mut with
    (P0 := fun b =>
       forall n, x `notin` fv_bbody (close_bbody_wrt_bexpr_rec n x b));
    simpl; intros; auto.
  - destruct (lt_ge_dec n n0); auto.
  - unfold eq_dec. destruct EqDec_eq_of_X; auto.
Qed.


Lemma close_bexpr_notin : forall x e,
    x `notin` fv_bexpr (close_bexpr_wrt_bexpr x e).
Proof.
  intros. apply close_bexpr_notin_rec.
Qed.

Lemma close_bbody_close_rec : forall x b n,
    x `notin` fv_bbody (close_bbody_wrt_bexpr_rec n x b).
Proof.
  induction b; intros; simpl.
  eauto using close_bexpr_notin_rec.
Qed.

Lemma bbody_close_notin : forall x b,
    x `notin` fv_bbody (close_bbody_wrt_bexpr x b).
Proof.
  intros. apply close_bbody_close_rec.
Qed.

Lemma fv_bexpr_open_bexpr_notin_rec : forall x v
  , x `notin` fv_bexpr v → forall e n
  , x `notin` fv_bexpr e
  → x `notin` fv_bexpr (open_bexpr_wrt_bexpr_rec n v e).
Proof.
  intros until e.

  induction e using bexpr_mut with
    (P0 := fun b => forall n
      , x `notin` fv_bbody b
        → x `notin` fv_bbody (open_bbody_wrt_bexpr_rec n v b));
  simpl; intros; eauto 4.
  - destruct (lt_eq_lt_dec n n0); try destruct s; auto.
Qed.

Lemma fv_bexpr_open_bexpr_notin : forall e x v
  , x `notin` fv_bexpr e → x `notin` fv_bexpr v
  → x `notin` fv_bexpr (e ^^' v).
Proof.
  intros. eauto using fv_bexpr_open_bexpr_notin_rec.
Qed.
