Require Export bidir.notations.

Reserved Notation "G1 ⫢ G2" (at level 58, left associativity).
Fixpoint dwl_app (G1 G2 : dworklist) :=
  match G2 with
  | dwl_nil => G1
  | G2' ,′' x : A => G1 ⫢ G2' ,′' x : A
  | G2' ⊨ b => G1 ⫢ G2' ⊨ b
  end
where "G1 ⫢ G2" := (dwl_app G1 G2) : dworklist_scope
.

Definition dwl_ocons (Γ : dworklist) (b : obindd) :=
  match b with
  | dob_none => Γ
  | dob_bind x A => Γ ,′' x : A
  end
.

Notation "Γ ,? b" :=
  (dwl_ocons Γ b)
    (at level 58, left associativity) : dworklist_scope.

Reserved Notation "⌊ wl ⌋" (at level 0, no associativity).
Fixpoint to_bctx (Γ : dworklist) : bcontext :=
  match Γ with
  | Γ' ⊨ w => ⌊ Γ' ⌋
  | Γ' ,′' x : A => ⌊ Γ' ⌋ ,' x : A
  | dwl_nil => bctx_nil
  end
where "⌊ wl ⌋" := (to_bctx wl) : bcontext_scope.

Inductive apply_dcont : dcont → bexpr → dworklist → Prop :=
| apdc_done : forall e, apply_dcont dc_done e dwl_nil
| apdc_app : forall A e1 e2 c,
  apply_dcont (dc_app e1 e2 c) A (dwl_nil ⊨ A ⋅ e1 & e2 ⇒ c)
| apdc_reduce : forall A c,
  apply_dcont (dc_reduce c) A (dwl_nil ⊨ A ⟼ c)
| apdc_check : forall A B,
  apply_dcont (dc_check B) A (dwl_nil ⊨ A ≲ B)
| apdc_inst : forall A B c k,
  apply_dcont (dc_inst B c) A (dwl_nil ⊨ c $ A ⊨ A <: B ⇐ ⧼k⧽')
.

Reserved Notation "⪧ wl" (at level 60, no associativity).
Inductive dwl_step : dworklist → Prop :=
| dst_nil : ⪧ dwl_nil
| dst_infer : forall Γ e1 e2 c A
  , ⌊ Γ ⌋ ⊢ e1 <: e2 ⇒ A
  → ⪧ Γ ⊨ c $ A
  → ⪧ Γ ⊨ e1 <: e2 ⇒ c
| dst_infer_app : forall Γ A c e1 e2 B C
  , ⌊ Γ ⌋ ⊢ A ⇒Π B, C
  → ⌊ Γ ⌋ ⊢ e1 <: e2 ⇐ B
  → ⪧ Γ ⊨ c $ B ^^' e1
  → ⪧ Γ ⊨ A ⋅ e1 & e2 ⇒ c
| dst_reduce : forall Γ A c B
  , ⌊ Γ ⌋ ⊢ A ⟼ B
  → ⪧ Γ ⊨ c $ B
  → ⪧ Γ ⊨ A ⟼ c
| dst_comp : forall Γ A B k
  , ⌊ Γ ⌋ ⊢ A <: B ⇒ ⧼ k ⧽'
  → ⪧ Γ
  → ⪧ Γ ⊨ A ≲ B
| dst_comp_box : forall Γ
  , ⪧ Γ
  → ⪧ Γ ⊨ ◻' ≲ ◻'
| dst_check : forall Γ ob e1 e2 A
  , ⪧ Γ ,? ob ⊨ e1 <: e2 ⇒ dc_check A
  → ⪧ Γ ⊨ ob ⊢? e1 <: e2 ⇐ A
| dst_app_cont : forall Γ c e Γ'
  , apply_dcont c e Γ'
  → ⪧ Γ ⫢ Γ'
  → ⪧ Γ ⊨ c $ e
where "⪧ wl" := (dwl_step wl) : type_scope
.

#[export]
Hint Constructors dwl_step : core.
