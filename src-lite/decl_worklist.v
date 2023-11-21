Require Export bidir.notations.
Require Import Program.Equality.
Require Import bidir.properties.
Require Import ln_utils.

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

Fixpoint dwl_dom (Γ : dworklist) : atoms :=
  match Γ with
  | dwl_nil => {}
  | Γ ⊨ w => dwl_dom Γ
  | Γ ,′' x : A => add x (dwl_dom Γ)
  end
.

Notation "Γ ,? b" :=
  (dwl_ocons Γ b)
    (at level 58, left associativity) : dworklist_scope.

Reserved Notation "⌊ wl ⌋" (at level 0, wl at level 58, no associativity).
Fixpoint to_bctx (Γ : dworklist) : bcontext :=
  match Γ with
  | Γ' ⊨ w => ⌊ Γ' ⌋
  | Γ' ,′' x : A => ⌊ Γ' ⌋ ,' x : A
  | dwl_nil => bctx_nil
  end
where "⌊ wl ⌋" := (to_bctx wl) : bcontext_scope.

Lemma app_to_bctx_distr : forall Γ1 Γ2,
    ⌊ Γ1 ⫢ Γ2 ⌋ = ⌊ Γ1 ⌋ ,,' ⌊ Γ2 ⌋.
Proof.
  induction Γ2; simpl; intros; auto.
  - now rewrite IHΓ2.
Qed.

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
  , ⌊ Γ ⌋ ⊢ A <: B ⇐ ⧼ k ⧽'
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
| dst_bind : forall Γ x A k
  , ⪧ Γ
  → ⌊ Γ ⌋ ⊢ A ⇐ ⧼ k ⧽'
  → x `notin` dwl_dom Γ
  → ⪧ Γ ,′' x : A
where "⪧ wl" := (dwl_step wl) : type_scope
.

#[export]
Hint Constructors dwl_step : core.


Lemma solve_infer_infer : forall Γ e1 e2 c
  , ⪧ Γ ⊨ e1 <: e2 ⇒ c
  → exists A, ⌊ Γ ⌋ ⊢ e1 <: e2 ⇒ A ∧ ⪧ Γ ⊨ c $ A.
Proof.
  intros.
  inversion H; subst.
  eauto.
Qed.

Lemma solve_check_check : forall Γ ob e1 e2 A
  , ⪧ Γ ⊨ ob ⊢? e1 <: e2 ⇐ A
  → ⌊ Γ ,? ob ⌋ ⊢ e1 <: e2 ⇐ A.
Proof.
  intros.
  dependent destruction H.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H0.
  inversion H1; subst.
  - eauto.
  - eauto using infer_k_check.
Qed.

Inductive vsign : Set :=
| v_pos : vsign
| v_neg : vsign
.

Definition vneg (s : vsign) : vsign :=
  match s with
  | v_pos => v_neg
  | v_neg => v_pos
  end
.

Reserved Notation "Γ ⊢ e1 ⤚ ⇥ e2"
  (at level 65, e1 at level 50, no associativity).
Inductive dmonoize : bcontext → bexpr → bexpr → Prop :=
| dmz_var   : forall Γ x, Γ ⊢ `'x  ⤚ ⇥ `'x
| dmz_kind  : forall Γ k, Γ ⊢ ⧼k⧽' ⤚ ⇥ ⧼k⧽'
| dmz_num : forall Γ n, Γ ⊢ be_num n ⤚ ⇥ be_num n
| dmz_int : forall Γ, Γ ⊢ be_int   ⤚ ⇥ be_int
| dmz_bot : forall Γ A
  , Γ ⊢ be_bot A ⤚ ⇥ be_bot A
| dmz_app : forall Γ f1 f2 a
  , mono_btype a
  → Γ ⊢ f1 ⤚ ⇥ f2
  → Γ ⊢ be_app f1 a ⤚ ⇥ be_app f2 a
| dmz_abs : forall L Γ e1 A B e2
  , (forall x, x `notin` L → Γ,' x : A ⊢ e1 ^`' x ⤚ ⇥ e2 ^`' x)
  → Γ ⊢ λ, A , e1 : B ⤚ ⇥ λ, A , e2 : B
| dmz_pi : forall L Γ A B1 B2
  , mono_btype A
  → (forall x, x `notin` L →
      Γ,' x : A ⊢ B1 ^`' x ⤚ ⇥ B2 ^`' x)
  → Γ ⊢ be_pi A B1 ⤚ ⇥ be_pi A B2
| dmz_bind : forall L Γ e1 A B e2
  , (forall x, x `notin` L → Γ,' x : A ⊢ e1 ^`' x ⤚ ⇥ e2 ^`' x)
  → Γ ⊢ Λ, A , e1 : B ⤚ ⇥ Λ, A , e2 : B
| dmz_forall : forall Γ A B C e
  , mono_btype e
  → Γ ⊢ e ⇐ A
  → Γ ⊢ B ^^' e ⤚ ⇥ C
  → Γ ⊢ be_all A B ⤚ ⇥ C
(*
| dmz_forall_neg : forall Γ L A B C
  , (forall x, x `notin` L → x `notin` fv_bexpr (B ^`' x))
  → (forall x, x `notin` L → Γ ⊢ B ^`' x ⤚ v_neg ⇥ C)
  → Γ ⊢ be_all A B ⤚ v_neg ⇥ C
*)
| dmz_castdn : forall Γ e1 e2
  , Γ ⊢ e1 ⤚ ⇥ e2
  → Γ ⊢ be_castdn e1 ⤚ ⇥ be_castdn e2
| dmz_castup : forall Γ e1 A e2
  , Γ ⊢ e1 ⤚ ⇥ e2
  → Γ ⊢ be_castup A e1 ⤚ ⇥ be_castup A e2
| dmz_anno : forall Γ e1 e2 A
  , Γ ⊢ e1 ⤚ ⇥ e2
  → Γ ⊢ be_anno e1 A ⤚ ⇥ be_anno e2 A
where "Γ ⊢ e1 ⤚ ⇥ e2" := (dmonoize Γ e1 e2) : type_scope.


Lemma dmonoize_welltyped : forall Γ e e' d A
  , Γ ⊢ e ⤚ ⇥ e'
  → busub Γ e e d A
  → busub Γ e e' d A.
Proof.
  induction 1; intros.
  1-7: admit.
  - admit.
  - admit.
  - admit.
Admitted.
