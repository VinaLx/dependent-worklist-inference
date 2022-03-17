Require Import Program.Tactics.

Require Import decl.properties.
Require Import bidir.notations.
Require Import bidir.properties.
Require Import bidir.elaboration.
Require Import transform_properties.
Require Import ln_utils.

Theorem bidir_complete1 : forall Γ e1 e2 A
  , Γ ⊢ e1 <: e2 : A
  → to_bcontext Γ ⊢ to_bexpr e1 <: to_bexpr e2 ⇒ to_bexpr A.
Proof.
  induction 1.

  1-9: admit.
  - simpl. econstructor.
    eapply bs_castup with (B := (to_bexpr B)).
    + admit.
    + admit.
(*
  1-14: admit.
  - admit. *)
Admitted.

Theorem bidir_complete2 : forall Γ e1 e2 A
  , Γ ⊢ e1 <: e2 : A
  → to_bcontext Γ ⊢ to_bexpr e1 <: to_bexpr e2 ⇐ to_bexpr A.
Proof.
  induction 1.
  1-7: admit.
  - admit.
Admitted.

(* dummy condition *)
Definition ctx_condition : context → bcontext → Prop := fun c c' => True.
Definition condition : expr → bexpr → Prop := fun e e' => True.

Theorem bidir_complete3 : forall Γ e1 e2 A
  , Γ ⊢ e1 <: e2 : A
  → exists Γ' e1' e2' A', Γ' ⊢ e1' <: e2' ⇒ A' ∧ ctx_condition Γ Γ'
    ∧ condition e1 e1' ∧ condition e2 e2' ∧ condition A A'.
Proof.
  induction 1.
  1-6: admit.
  - admit.
Admitted.


Theorem bidir_complete4 : forall Γ e1 e2 A Γ' e1' e2' A'
  , usub_elab Γ e1 e2 A Γ' e1' e2' A'
  → Γ' ⊢ e1' <: e2' ⇒ A'.
Proof with eauto with bidir.
  intros.
  pattern Γ, e1, e2, A, Γ', e1', e2', A', H.
  apply usub_elab_mut with (
    P0:= fun Γ Γ' (_ : wf_context_elab Γ Γ') => wf_bcontext Γ'); intros; try (constructor; auto; fail).
  - econstructor; auto; eauto...
  - econstructor; intros.
    + econstructor; eauto...
      * intros. inst_cofinites_with x. eapply bs_sub with (A:=B1' ^`' x)...
    + eapply bs_pi_inf with (L:=L); eauto.
      * inst_cofinites_with_new...
      * intros. inst_cofinites_with x...
      * intros. inst_cofinites_with x.
        replace (Γ'0,' x : A2') with (Γ'0,' x : A2',,'bctx_nil) by auto.
        eapply bidir_narrowing with (B:=A1'); simpl; eauto.
    + eapply bs_pi_inf with (L:=L); eauto...
      * intros. inst_cofinites_with x...
        replace (Γ'0,' x : A2') with (Γ'0,' x : A2',,'bctx_nil) by auto.
        eapply bidir_narrowing with (B:=A1'); simpl; eauto...
  - econstructor; eauto... 
  - econstructor; eauto...
    + admit. (* monotype *)
    + econstructor; intros.
      * admit. (* type_correctness *)
      * eapply bs_sub with (A:=A'0); eauto...
        admit. (* type_correctness *)
  - eapply bs_anno.
    + eapply bs_bind.
      * eauto...
      * admit.  (* type_correctness *)
      * intros. eapply bs_sub.
        inst_cofinites_with x. eauto...
        eauto...
      * intros. simpl. inst_cofinites_with x. admit. (* fv_eexpr *)
      * intros. simpl. inst_cofinites_with x. admit. (* fv_eexpr *)
    + eauto... 
    + eapply bs_forall with (L:=L); eauto...
      * intros. replace (Γ'0,' x : A2') with (Γ'0,' x : A2',,'bctx_nil) by auto.
        eapply bidir_narrowing with (B:=A1'); eauto.
  - econstructor; eauto.
    eapply bs_castup with (B:=B'); eauto.
    + eapply bidir_refl_l in H0. exact H0.
    + admit. (* breduce *)
    + eapply bs_sub with (A:=B'). auto. admit. (* type_correctness *)
  - eapply bs_castdn with (A:=A'0). exact H0. admit. (* breduce *) auto.
  - eapply bs_forall_l with (t:=t'); eauto...
    + admit. (* monotype *)
  - econstructor; eauto.
  - eapply bs_forall; eauto.
  - econstructor.
    eapply bs_sub with (A:=A'0); eauto.
    + admit. (* bidir_refl_r *)
    + admit. (* bidir_refl_r *)
  - econstructor.
    + auto.
    + admit. (* ctx_dom *)
    + exact H1.
Admitted.


(* completeness / totality of elaboration system *)
Theorem usub_elab_total : forall Γ e1 e2 A
  , Γ ⊢ e1 <: e2 : A
  → usub_elab Γ e1 e2 A
              (to_bcontext Γ) (to_bexpr e1) (to_bexpr e2) (to_bexpr A).
Proof.
  induction 1.
  1-14: admit.
  - simpl. admit. 
Admitted.

Check busub_elab_mut.


Theorem bidir_sound : forall Γ' e1' e2' d A' Γ e1 e2 A,
    busub_elab Γ' e1' e2' d A' Γ e1 e2 A → Γ ⊢ e1 <: e2 : A.
Proof.
  intros.
  pattern Γ', e1', e2', d, A', Γ, e1, e2, A, H.

  Check busub_elab_mut.
  eapply busub_elab_mut with
    (P0 := fun Γ' Γ (_ : wf_bcontext_elab Γ' Γ) => ⊢ Γ ); intros; try (constructor; auto; fail).
  - eauto.
  - eauto.
  - eauto.
  - admit. (* P1 app *)
  - econstructor; eauto.
    + intros. admit. (* fv_eexpr *)
    + intros. admit. (* fv_eexpr *)
  - econstructor; eauto.
    + admit. (* breduce *)
    + admit. (* breduce *)
  - econstructor.
    + eauto.
    + admit.
    + eauto.
  - eapply ott.s_forall_l with (t:=t).
    + admit.
    + eauto.
    + eauto.
    + auto.
    + eauto.
  - econstructor; eauto.
  - eapply ott.s_forall; eauto.
  - auto.
  - eapply ott.s_sub; eauto.
  - econstructor; eauto.
    + admit.  
Admitted.


(*
Theorem bidir_sound : forall Γ' e1' e2' d A' Γ e1 e2 A,
  busub_elab Γ' e1' e2' d A' Γ e1 e2 A → Γ ⊢ e1 <: e2 : A.
Proof.
  intros.
  induction H; try solve constructor.
  (* pattern Γ', e1, e2', d, A', Γ, e1, e2, A, H.
  eapply busub_ind_dep with
    (P0 := fun Γ' (_ : ⫦ Γ') => ⊢ Γ). *)
  - constructor; auto. admit.
  - constructor.
Admitted.
*)



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
