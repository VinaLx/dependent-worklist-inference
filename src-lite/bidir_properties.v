Require Import decl_notations.
Require Import Coq.Program.Equality.

Scheme Induction for busub Sort Prop
  with Induction for bwf_context Sort Prop
  with Induction for infer_app Sort Prop
  with Induction for greduce Sort Prop.

Lemma check_sub_invert : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 ⇐ A ->
    A = ◻ \/ exists B k, Γ ⊢ B <: A ⇒ ⧼ k ⧽ /\ Γ ⊢ e1 <: e2 ⇒ B.
Proof.
  intros. dependent induction H; eauto.
Qed.

Scheme busub_refl_mut := Induction for busub     Sort Prop
  with  iapp_refl_mut := Induction for infer_app Sort Prop.

Theorem bidir_refl_l : forall Γ e1 e2 d A,
    busub Γ e1 e2 d A -> busub Γ e1 e1 d A.
Proof.
  intros.
  pattern Γ, e1, e2, d, A, H.
  apply busub_refl_mut with
      (P0 := fun c A e1 e2 B (H : c ⊢ A ⋅ e1 & e2 ⇒ B) => c ⊢ A ⋅ e1 & e1 ⇒ B);
    intros; eauto.
Qed.

Theorem bidir_weakening : forall Γ1 Γ2 Γ3 e1 e2 d A,
    busub (Γ1,,      Γ3) e1 e2 d A -> ⫦ Γ1 ,, Γ2 ,, Γ3 ->
    busub (Γ1,, Γ2,, Γ3) e1 e2 d A.
Proof.
Admitted.

Theorem bidir_narrowing : forall Γ1 x B Γ2 e1 e2 d C,
    busub (Γ1, x : B,, Γ2) e1 e2 d C -> forall A k,
      Γ1 ⊢ A ⇒ ⧼ k ⧽ -> busub (Γ1, x : A,, Γ2) e1 e2 d C.
Proof.
Admitted.
