Require Import decl.worklist.
Require Import Program.Equality.

Theorem soundness__infer : forall Γ e c,
    ⪧ Γ ⊨ e ⇒' c → exists A, ⌊ Γ ⌋ ⊢ e : A ∧ ⪧ Γ ⊨ c $ A.
Proof.
  intros.
  dependent destruction H.
  - exists A. now split.
Qed.

Theorem soundness__check : forall Γ e A,
    ⪧ Γ ⊨ e ⇐' A → ⌊ Γ ⌋ ⊢ e : A.
Proof.
  intros.
  now dependent destruction H.
Qed.

Lemma to_ctx_to_wl_id : forall Γ,
    ⌊ ⌈ Γ ⌉ ⌋ = Γ.
Proof.
  intros.
  induction Γ; simpl.
  - reflexivity.
  - now rewrite IHΓ.
Qed.

Theorem completeness : forall Γ e A,
    Γ ⊢ e : A → ⪧ ⌈ Γ ⌉ ⊨ e ⇐' A.
Proof.
  intros.
  constructor.
  now rewrite to_ctx_to_wl_id.
Qed.

Theorem soundness__infer2 : forall Γ e c,
    ⪧₂ Γ ⊨ e ⇒' c → exists A, ⌊ Γ ⌋ ⊢ e ⇒ A ∧ ⪧ Γ ⊨ c $ A.
Proof.
  intros.
  dependent destruction H.
  - admit.
  - admit.
Admitted.

Theorem soundness__check2 : forall Γ e A,
    ⪧ Γ ⊨ e ⇐' A → ⌊ Γ ⌋ ⊢ e ⇐ A.
Proof.
Admitted.

Theorem completeness2 : forall Γ e A,
    Γ ⊢ e : A → ⪧₂ ⌈ Γ ⌉ ⊨ e ⇐' A.
Proof.
  intros.
  induction H.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  -
Admitted.
