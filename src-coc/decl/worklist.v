Require Export decl.notations.
Require Import Program.Equality.

Reserved Notation "G1 ⫢ G2" (at level 58, left associativity).
Fixpoint dwl_app (G1 G2 : dworklist) :=
  match G2 with
  | dwl_nil => G1
  | G2' ,' x : A => G1 ⫢ G2' ,' x : A
  | G2' ⊨  b => G1 ⫢ G2' ⊨ b
  | G2' ,' ◁ => G1 ⫢ G2' ,' ◁
  end
where "G1 ⫢ G2" := (dwl_app G1 G2) : dworklist_scope
.

Fixpoint dwl_dom (Γ : dworklist) : atoms :=
  match Γ with
  | dwl_nil => {}
  | Γ ⊨ w => dwl_dom Γ
  | Γ ,' x : A => add x (dwl_dom Γ)
  | Γ ,' ◁ => dwl_dom Γ
  end
.

Reserved Notation "⌊ wl ⌋" (at level 0, wl at level 58, no associativity).
Fixpoint to_ctx (Γ : dworklist) : context :=
  match Γ with
  | Γ' ⊨ w => ⌊ Γ' ⌋
  | Γ' ,' x : A => ⌊ Γ' ⌋ , x : A
  | Γ' ,' ◁ => ⌊ Γ' ⌋
  | dwl_nil => ctx_nil
  end
where "⌊ wl ⌋" := (to_ctx wl) : context_scope.

Reserved Notation "⌈ ctx ⌉" (at level 0, ctx at level 58, no associativity).
Fixpoint to_wl (Γ : context) : dworklist :=
  match Γ with
  | ctx_nil => dwl_nil
  | Γ, x : A => ⌈ Γ ⌉ ,' x : A
  end
where "⌈ ctx ⌉" := (to_wl ctx) : dworklist_scope
.

Lemma app_to_bctx_distr : forall Γ1 Γ2,
    ⌊ Γ1 ⫢ Γ2 ⌋ = ⌊ Γ1 ⌋ ,, ⌊ Γ2 ⌋.
Proof.
  induction Γ2; simpl; intros; auto.
  - now rewrite IHΓ2.
Qed.


Fixpoint wrap_expr_wrt_context (Γ : context) (e : expr) :=
  match Γ with
  | ctx_nil => e
  | Γ' , x : A =>
      wrap_expr_wrt_context Γ' (e_pi A (close_expr_wrt_expr x e))
  end
.

Inductive apply_dcont : dcont → expr → dworklist → Prop :=
| apdc_done : forall e, apply_dcont dc_done e dwl_nil
| apdc_app : forall A e c,
    apply_dcont (dc_app e c) A (dwl_nil ⊨ A ⋅ e ⇒ c)
| apdc_check : forall A B,
    apply_dcont (dc_check B) A (dwl_nil ⊨ A ⧼~~⧽ B)
.

Inductive dnotags : dworklist → Prop :=
| dnt_nil : dnotags dwl_nil
| dnt_cons : forall Γ w, dnotags Γ → dnotags (Γ ⊨ w)
| dnt_var : forall Γ x A, dnotags Γ → dnotags (Γ ,' x : A)
.

Inductive wrap_expr : expr → dworklist → expr → Prop :=
| wr_nil : forall e, wrap_expr e dwl_nil e
| wr_cons : forall Γ w e e', wrap_expr e Γ e' → wrap_expr e (Γ ⊨ w) e'
| wr_var : forall Γ x A e e'
  , wrap_expr (e_pi A (close_expr_wrt_expr x e)) Γ e'
  → wrap_expr e (Γ ,' x : A) e'
.

Reserved Notation "⪧ wl" (at level 60, no associativity).
Inductive dwl_step : dworklist → Prop :=
| dst_nil : ⪧ dwl_nil
| dst_infer : forall Γ e c A
  , ⌊ Γ ⌋ ⊢ e : A
  → ⪧ Γ ⊨ c $ A
  → ⪧ Γ ⊨ e ⇒' c
| dst_infer_app : forall Γ A c e B
  , ⌊ Γ ⌋ ⊢ e : A
  → ⪧ Γ ⊨ c $ B ^^ e
  → ⪧ Γ ⊨ e_pi A B ⋅ e ⇒ c
| dst_comp : forall Γ A k
  , A <> ◻
  → ⌊ Γ ⌋ ⊢ A : ⧼ k ⧽
  → ⪧ Γ ⊨ A ⧼~~⧽ A
| dst_comp_box : forall Γ
  , ⪧ Γ
  → ⪧ Γ ⊨ ◻ ⧼~~⧽ ◻
| dst_check : forall Γ ψ e A
  , ⌊ Γ ⌋ ,, ψ ⊢ e : A
  → ⪧ Γ ⊨ ψ ⊢' e ⇐ A
| dst_app_cont : forall Γ1 Γ2 c e e' Γ'
  , dnotags Γ2
  → wrap_expr e Γ2 e'
  → apply_dcont c e' Γ'
  → ⪧ Γ1 ⫢ Γ' ⫢ Γ2
  → ⪧ Γ1,' ◁ ⫢ Γ2 ⊨ c $ e
| dst_bind : forall Γ x A k
  , ⪧ Γ
  → ⌊ Γ ⌋ ⊢ A : ⧼ k ⧽
  → x `notin` dwl_dom Γ
  → ⪧ Γ ,' x : A
where "⪧ wl" := (dwl_step wl) : type_scope
.

Reserved Notation "⪧₂ wl" (at level 60, no associativity).
Inductive dwl_step_c : dworklist → Prop :=
| dst2_nil : ⪧₂ dwl_nil
| dst2_infer : forall Γ e c A
  , (⌊ Γ ⌋ ⊢ e ⇒ A)
  → ¬ (exists f a, e = e_app f a)
  → ⪧₂ Γ ⊨ c $ A
  → ⪧₂ Γ ⊨ e ⇒' c
| dst2_app : forall Γ f e c F
  , ⪧₂ Γ ⊨ F ⋅ e ⇒ c
  → ⌊ Γ ⌋ ⊢ f ⇒ F
  → ⪧₂ Γ ⊨ e_app f e ⇒' c
| dst2_infer_app : forall Γ A c e B
  , (⌊ Γ ⌋ ⊢ e ⇐ A)
  → ⪧₂ Γ ⊨ c $ B ^^ e
  → ⪧₂ Γ ⊨ e_pi A B ⋅ e ⇒ c
| dst2_comp : forall Γ A k
  , A <> ◻
  → ⌊ Γ ⌋ ⊢ A : ⧼ k ⧽
  → ⪧₂ Γ ⊨ A ⧼~~⧽ A
| dst2_comp_box : forall Γ
  , ⪧₂ Γ
  → ⪧₂ Γ ⊨ ◻ ⧼~~⧽ ◻
| dst2_check : forall Γ ψ e A
  , ⪧₂ Γ ⫢ ⌈ ψ ⌉ ,' ◁ ⊨ e ⇒' __ ⧼~~⧽ A
  → ⪧₂ Γ ⊨ ψ ⊢' e ⇐ A
| dst2_app_cont : forall Γ1 Γ2 c e e' Γ'
  , dnotags Γ2
  → wrap_expr e Γ2 e'
  → apply_dcont c e' Γ'
  → ⪧₂ Γ1 ⫢ Γ' ⫢ Γ2
  → ⪧₂ Γ1,' ◁ ⫢ Γ2 ⊨ c $ e
| dst2_bind : forall Γ x A k
  , ⪧₂ Γ
  → ⌊ Γ ⌋ ⊢ A ⇒ ⧼ k ⧽
  → x `notin` dwl_dom Γ
  → ⪧₂ Γ ,' x : A
where "⪧₂ wl" := (dwl_step_c wl) : type_scope
.

#[export]
Hint Constructors dwl_step dwl_step_c : core.
