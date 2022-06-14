Require Export alg.notations.
Require Export Utf8.

Scheme aexpr_mut := Induction for aexpr Sort Prop
  with abody_mut := Induction for abody Sort Prop.

Lemma fkv_aexpr_open_aexpr_notin_rec : forall x e2
  , x `notin` fkv_aexpr e2
  → forall e1 n
  , x `notin` fkv_aexpr e1
  → x `notin` fkv_aexpr (open_aexpr_wrt_aexpr_rec n e2 e1).
Proof.
  intros until e1.
  induction e1 using aexpr_mut with
    (P0 := fun b => forall n
      , x `notin` fkv_abody b
      → x `notin` fkv_abody (open_abody_wrt_aexpr_rec n e2 b))
  ; simpl; intros; auto.
  - destruct (lt_eq_lt_dec n n0). destruct s.
    all: auto.
Qed.

Lemma fkv_aexpr_open_aexpr_notin : forall x e1 e2
  , x `notin` fkv_aexpr e1 → x `notin` fkv_aexpr e2
  → x `notin` fkv_aexpr (e1 ^^′ e2).
Proof.
  intros.
  eauto using fkv_aexpr_open_aexpr_notin_rec.
Qed.

#[export]
Hint Resolve fkv_aexpr_open_aexpr_notin : lngen.

Lemma fkv_abody_open_abody_notin : forall x b e
  , x `notin` fkv_abody b → x `notin` fkv_aexpr e
  → x `notin` fkv_abody (open_abody_wrt_aexpr b e).
Proof.
  destruct b; simpl; intros.
  apply notin_union; apply fkv_aexpr_open_aexpr_notin; auto.
Qed.

#[export]
Hint Resolve fkv_abody_open_abody_notin : lngen.

Lemma aexpr_subst_open_comm : forall x v1 e v2
  , lc_aexpr v1 → x `notin` fv_aexpr v2
  → ([v1 /′ x] e) ^^′ v2 = [v1 /′ x] e ^^′ v2.
Proof.
  intros.
  rewrite subst_aexpr_open_aexpr_wrt_aexpr.
  rewrite (subst_aexpr_fresh_eq v2).
  all: easy.
Qed.

Lemma abody_subst_open_comm : forall x v1 b v2
  , lc_aexpr v1 → x `notin` fv_aexpr v2
    → open_abody_wrt_aexpr (subst_abody v1 x b) v2
      = subst_abody v1 x (open_abody_wrt_aexpr b v2).
Proof.
  intros.
  rewrite subst_abody_open_abody_wrt_aexpr.
  rewrite (subst_aexpr_fresh_eq v2).
  all: easy.
Qed.


(*
Lemma worklist_subst_open_comm : forall x v1 Γ v2
  , lc_aexpr v1 → x `notin` fv_aexpr v2
  → subst_worklist v1 x Γ $′ v2 = subst_worklist v1 x (Γ $′ v2).
Proof.
  intros.
  rewrite subst_worklist_open_worklist_wrt_aexpr.
  rewrite (subst_aexpr_fresh_eq v2).
  all: easy.
Qed.
*)

Lemma open_aexpr_fv_aexpr_notin_rec : forall x v e n
  , x `notin` fv_aexpr (open_aexpr_wrt_aexpr_rec n v e)
  → x `notin` fv_aexpr e.
Proof.
  intros until e.
  induction e using aexpr_mut with
    (P0 := fun b => forall n
      , x `notin` fv_abody (open_abody_wrt_aexpr_rec n v b)
        → x `notin` fv_abody b);
    simpl; intros; eauto 4.
Qed.

Lemma open_aexpr_fv_aexpr_notin : forall e x v,
  x `notin` fv_aexpr (e ^^′ v) → x `notin` fv_aexpr e.
Proof.
  intros. eauto using open_aexpr_fv_aexpr_notin_rec.
Qed.
