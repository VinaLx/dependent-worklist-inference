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

Lemma k_subst_aexpr_open_aexpr_wrt_aexpr_rec : forall e2 e1 x k n
  , k_subst_aexpr k x (open_aexpr_wrt_aexpr_rec n e2 e1)
    = open_aexpr_wrt_aexpr_rec n
        (k_subst_aexpr k x e2) (k_subst_aexpr k x e1).
Proof.
  intros e2 e1 x k.
  induction e1 using aexpr_mut with
    (P0 := (fun b => forall n, k_subst_abody k x (open_abody_wrt_aexpr_rec n e2 b) = open_abody_wrt_aexpr_rec n (k_subst_aexpr k x e2) (k_subst_abody k x b))); simpl; intros;
    try (rewrite IHe0, IHe1 || rewrite IHe1_1, IHe1_2 || rewrite IHe1); eauto.
  - destruct (lt_eq_lt_dec n n0). destruct s.
    all: simpl; auto.
Qed.

Lemma k_subst_abody_open_abody_wrt_aexpr_rec : forall b e x k n
  , k_subst_abody k x (open_abody_wrt_aexpr_rec n e b)
    = open_abody_wrt_aexpr_rec n
        (k_subst_aexpr k x e) (k_subst_abody k x b).
Proof.
  induction b; simpl; intros.
  now repeat rewrite k_subst_aexpr_open_aexpr_wrt_aexpr_rec.
Qed.

Lemma k_subst_aexpr_open_aexpr_wrt_aexpr : forall e2 e1 x k
  , k_subst_aexpr k x (e1 ^^′ e2)
    = (k_subst_aexpr k x e1) ^^′ (k_subst_aexpr k x e2).
Proof.
  intros.
  apply k_subst_aexpr_open_aexpr_wrt_aexpr_rec.
Qed.

Lemma k_subst_abody_open_abody_wrt_aexpr : forall b e x k
  , k_subst_abody k x (open_abody_wrt_aexpr b e)
    = open_abody_wrt_aexpr
        (k_subst_abody k x b) (k_subst_aexpr k x e).
Proof.
  intros.
  apply k_subst_abody_open_abody_wrt_aexpr_rec.
Qed.

Lemma k_subst_aexpr_fresh_eq : forall e k x
  , x `notin` fkv_aexpr e
  → k_subst_aexpr k x e = e.
Proof.
  intros e k x.
  induction e using aexpr_mut with
    (P0 := fun b => x `notin` fkv_abody b → k_subst_abody k x b = b);
    simpl; intros; try (rewrite IHe1, IHe2 || rewrite IHe0, IHe || rewrite IHe); auto.
  - destruct k0; simpl; auto.
    simpl in H. destruct (kx == x); [> .. | subst; auto].
    assert (kx <> x) by auto.
    contradiction.
Qed.

Lemma k_subst_abody_fresh_eq : forall b k x
  , x `notin` fkv_abody b
  → k_subst_abody k x b = b.
Proof.
  induction b; simpl; intros.
  repeat rewrite k_subst_aexpr_fresh_eq; auto.
Qed.

Lemma aexpr_k_subst_open_comm : forall x k e v
  , x `notin` fkv_aexpr v
  → (k_subst_aexpr k x e) ^^′ v = k_subst_aexpr k x (e ^^′ v).
Proof.
  intros.
  rewrite k_subst_aexpr_open_aexpr_wrt_aexpr.
  rewrite (k_subst_aexpr_fresh_eq v ).
  all: easy.
Qed.

Lemma abody_k_subst_open_comm : forall x k b v
  , x `notin` fkv_aexpr v
    → open_abody_wrt_aexpr (k_subst_abody k x b) v
      = k_subst_abody k x (open_abody_wrt_aexpr b v).
Proof.
  intros.
  rewrite k_subst_abody_open_abody_wrt_aexpr.
  rewrite k_subst_aexpr_fresh_eq.
  all: easy.
Qed.
