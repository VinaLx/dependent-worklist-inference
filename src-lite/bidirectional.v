Require Import decl.properties.
Require Import Program.Tactics.
Require Import bidir.properties.
Require Import bidir.elaboration.

Fixpoint to_bexpr (e : expr) : bexpr :=
  match e with
  | e_var_f x => be_var_f x
  | e_var_b x => be_var_b x
  | e_kind k_star => be_kind bk_star
  | e_kind k_box => be_kind bk_box
  | e_num n => be_num n
  | e_int => be_int
  | e_bot A => be_anno be_bot (to_bexpr A)
  | e_app f a => be_app (to_bexpr f) (to_bexpr a)
  | e_abs  A (b_anno e B) => be_anno (be_abs  (to_bexpr e)) (be_pi  (to_bexpr A) (to_bexpr B))
  | e_bind A (b_anno e B) => be_anno (be_bind (to_bexpr e)) (be_all (to_bexpr A) (to_bexpr B))
  | e_pi  A B => be_pi  (to_bexpr A) (to_bexpr B)
  | e_all A B => be_all (to_bexpr A) (to_bexpr B)
  | e_castup A e => be_anno (be_castup (to_bexpr e)) (to_bexpr A)
  | e_castdn e => be_castdn (to_bexpr e)
  end
.

Fixpoint to_bcontext (Γ : context) : bcontext :=
  match Γ with
  | ctx_nil => bctx_nil
  | ctx_cons Γ' x A => bctx_cons (to_bcontext Γ') x (to_bexpr A)
  end
.

Lemma in_context_elab : forall Γ x A,
    x :_ A ∈ Γ -> ⊢ Γ -> forall Γ', wf_context_elab Γ' Γ -> exists A' k, in_bctx x A' Γ' /\ busub_elab Γ' A' A' d_infer ⧼k⧽' Γ A A ⧼(to_k k)⧽.
Proof.
  intros * In Wf.
  induction In; intros.
  - inversion H1; subst. exists A', k.
    split. eapply inb_here. admit. admit.
Admitted.

Theorem bidir_sound : forall Γ' e1' e2' d A' Γ e1 e2 A,
  busub_elab Γ' e1' e2' d A' Γ e1 e2 A → Γ ⊢ e1 <: e2 : A.
Proof.
  intros.
  induction H.
  1-7: admit.
  -
    replace B with (B ^^ t) by admit.
    eapply s_app.
Admitted.

Theorem bidir_complete : forall Γ e1 e2 A
  , Γ ⊢ e1 <: e2 : A
  -> busub_elab
      (to_bcontext Γ) (to_bexpr e1) (to_bexpr e2) d_infer (to_bexpr A)
      Γ e1 e2 A.
Proof.
  intros. pattern Γ, e1, e2, A, H.
  apply usub_mut with
    (P0 := fun Γ (_ : ⊢ Γ) => wf_context_elab (to_bcontext Γ) Γ); intros.
  - admit.
  - admit.
  - admit.
  - admit.
  - simpl. eapply bse_anno.
Admitted.




(*
Theorem bidir_sound : forall Γ e1 e2 A d,
    busub Γ e1 e2 d A -> Γ ⊢ e1 <: e2 : A
Proof.
  intros.
  pattern Γ, e1, e2, d, A, H.
  apply busub_ind_dep with
      (P0 := fun Γ (_ : ⫦ Γ) => ⊢ Γ)
      (P1 := fun G A e B (_ : G ⊢ A ⋅ e ⇒ B) =>
        exists D E, G ⊢ e : D
        /\ B = E ^^ e /\ (A = e_pi D E \/ G ⊢ A <: e_pi D E : ⋆))
      (P2 := fun G A B (_ : G ⊢ A ⟼ B) => A ⟶ B \/ exists C, G ⊢ A <: C : ⋆ /\ C ⟶ B);
    intros.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - (* app *)
    destruct H1 as (D & E & Ht & -> & [-> | Hsub]).
    + eauto.
    + eauto.
  - admit.
  - admit.
  - (* castdn *) destruct H1.
    + eauto.
    + destruct_conjs.
      assert (G ⊢ e0 <: e3 : H1) by eauto 3.
      eauto 3.
  - admit.
  - admit.
  - admit.
  - admit.

  (* wf *)
  - admit.
  - admit.

  (* infer_app *)
  - exists A0, B; eauto.
  - destruct H1 as (D & E & Ht & -> & [Eb | Hsub]).
    + exists D, E; repeat split; eauto 3; right.
      rewrite <- Eb.
      pick fresh x and apply s_forall_l; eauto; admit.
    + exists D, E; repeat split; eauto 3; right.
      admit.

  (* greduce *)
  - auto.
  - right.
    assert (G ⊢ e_all A0 B <: B ^^ t : ⋆) by admit.
    destruct H1.
    + eauto.
    + destruct_conjs. exists H1. admit.

Admitted.

Theorem bidir_complete : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> Γ ⊢ e1 <: e2 ⇐ A.
Proof.
  intros.
  pattern Γ, e1, e2, A, H.
  apply usub_mut with (P0 := fun Γ (_ : ⊢ Γ) => ⫦ Γ); intros.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - (* app *)
    eapply bs_sub with (A := B ^^ t).
    + eapply bs_app; eauto 3; admit.
    + admit.
  - admit.
  - admit.
  - eapply bs_sub with (A := B).
    + eapply bs_castdn; eauto 3; admit.
    + admit.
  - admit.
  - admit.
  - admit.
  - (* sub, seems doable *)
    admit.

  (* ⫦ Γ *)
  - auto.
  - admit.
Admitted.
*)
