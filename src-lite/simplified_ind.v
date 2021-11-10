Require Export decl_notations.

Lemma lc_body_e : forall e A,
    lc_body (b_anno e A) -> lc_expr e.
Proof.
  now inversion 1.
Qed.

Lemma lc_body_b : forall e A,
    lc_body (b_anno e A) -> lc_expr A.
Proof.
  now inversion 1.
Qed.

#[local]
Hint Resolve lc_body_b lc_body_e : core.

#[local]
Hint Unfold open_body_wrt_expr : core.

Lemma lc_expr_ind' : ∀ (P : expr → Prop)
  , (∀ (x : var), P (e_var_f x))
  → (∀ (k : kind), P ⧼ k ⧽)
  → (∀ (n : number), P (e_num n))
  → P e_int
  → (∀ (A : expr), lc_expr A → P A → P (e_bot A))
  → (∀ (e1 e2 : expr)
    , lc_expr e1 → P e1 → lc_expr e2 → P e2 → P (e_app e1 e2))
  → (∀ (A e B : expr)
    , lc_expr A → P A
    → (∀ (x : exprvar), lc_expr (e ^` x))
    → (forall (x : exprvar), lc_expr (B ^` x))
    → P (λ_ A, e : B))
  → (∀ (A B : expr)
    , lc_expr A → P A → (∀ (x : exprvar), lc_expr (B ^` x))
    → (∀ (x : exprvar), P (B ^` x)) → P (e_pi A B))
  → (∀ (A e B : expr)
    , lc_expr A → P A
    → (∀ x, lc_expr (e ^` x))
    → (forall x, lc_expr (B ^` x))
    → P (Λ A, e : B))
  → (∀ (A B : expr)
    , lc_expr A → P A → (∀ (x : exprvar), lc_expr (B ^` x))
    → (∀ (x : exprvar), P (B ^` x)) → P (e_all A B))
  → (∀ (A e : expr)
    , lc_expr A → P A → lc_expr e → P e → P (e_castup A e))
  → (∀ (e : expr), lc_expr e → P e → P (e_castdn e))
  → ∀ (e : expr), lc_expr e → P e.
Proof.
  intros.
  match goal with
  | H : lc_expr ?e |- ?P ?e =>
    induction H;
    (* solve all cases except for special ones with 'body' *)
    eauto; repeat
    match goal with
    | H : context [open_body_wrt_expr ?b _] |- _ =>
      destruct b; unfold open_body_wrt_expr in H; simpl in H
    end;
    eauto
  end
.
Qed.
