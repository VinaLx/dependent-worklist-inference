Require Import decl_properties.
Require Import Program.Tactics.
Require Import bidir_properties.

Theorem bidir_sound : forall Γ e1 e2 A d,
    busub Γ e1 e2 d A -> Γ ⊢ e1 <: e2 : A.
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
