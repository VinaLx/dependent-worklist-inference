Require Export decl_notations.

Notation "k $ e" :=
  (open_dworklist_wrt_expr k e)
    (at level 57, left associativity) : dworklist_scope.

Reserved Notation "G1 ⫢ G2" (at level 58, left associativity).
Fixpoint dwl_app (G1 G2 : dworklist) :=
  match G2 with
  | dwl_nil => G1
  | G2' ,' x : A => G1 ⫢ G2' ,' x : A
  | G2' ⊨ b => G1 ⫢ G2' ⊨ b
  end
where "G1 ⫢ G2" := (dwl_app G1 G2) : dworklist_scope
.

Definition dwl_ocons (Γ : dworklist) (b : obindd) :=
  match b with
  | dob_none => Γ
  | dob_bind x A => Γ ,' x : A
  end
.

Notation "Γ ,? b" :=
  (dwl_ocons Γ b)
    (at level 58, left associativity) : dworklist_scope.

Reserved Notation "⌊ wl ⌋" (at level 0, no associativity).
Fixpoint to_ctx (Γ : dworklist) : context :=
  match Γ with
  | Γ' ⊨ w => ⌊ Γ' ⌋
  | Γ' ,' x : A => ⌊ Γ' ⌋ , x : A
  | dwl_nil => ctx_nil
  end
where "⌊ wl ⌋" := (to_ctx wl) : context_scope.


Reserved Notation "⪧ wl" (at level 60, no associativity).
Inductive dwl_step : dworklist → Prop :=
| dst_infer : forall Γ e1 e2 c A
  , ⌊ Γ ⌋ ⊢ e1 <: e2 ⇒ A
  → ⪧ Γ ⫢ c $ A
  → ⪧ Γ ⊨ e1 <: e2 ⇒ c
| dst_infer_app : forall Γ A e1 e2 c B
  , ⌊ Γ ⌋ ⊢ A ⋅ e1 & e2 ⇒ B
  → ⪧ Γ ⫢ c $ B
  → ⪧ Γ ⊨ A ⋅ e1 & e2 ⇒ c
| dst_reduce : forall Γ A c B
  , ⌊ Γ ⌋ ⊢ A ⟼ B
  → ⪧ Γ ⫢ c $ B
  → ⪧ Γ ⊨ A ⟼ c
| dst_comp : forall Γ A B k
  , ⌊ Γ ⌋ ⊢ A <: B : ⧼ k ⧽
  → ⪧ Γ ⊨ A ≲ B
| dst_comp_box : forall Γ
  , ⪧ Γ ⊨ ◻ ≲ ◻
| dst_check : forall Γ ob e1 e2 A
  , ⪧ Γ ,? ob ⊨ e1 <: e2 ⇒ (dwl_nil ⊨ ↑0 ≲ A)
  → ⪧ Γ ⊨ ob ⊢? e1 <: e2 ⇐ A
where "⪧ wl" := (dwl_step wl) : type_scope
.
