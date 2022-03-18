Require Import Program.Tactics.
Require Import Metalib.FSetWeakNotin.

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

Ltac solve_trivial_mono_or_lc :=
  match goal with
  | H : mono_type ?P |- _ => dependent destruction H; eauto; fail
  | H : lc_expr ?P |- _ => dependent destruction H; eauto; fail                                                           
  end.


Lemma usub_elab_keeps_mono : forall Γ e1 e2 A Γ' e1' e2' A',
    usub_elab Γ e1 e2 A Γ' e1' e2' A' ->
        (mono_type e1 /\ mono_type e2 -> mono_btype e1' /\ mono_btype e2') /\ lc_bexpr e1' /\ lc_bexpr e2'.
Proof.
  intros.
  induction H; repeat split; destruct_conjs; intros; auto; try solve_trivial_mono_or_lc.
  - dependent destruction H7. dependent destruction H16.
    constructor.
    + dependent destruction H8. dependent destruction H18.
      inst_cofinites_with_new.
      eapply lc_be_pi_exists with (x1:=x); destruct_conjs; auto.
    + eapply bmono_lambda with (L:=(L `union` L0 `union` L1)).
      intros. inst_cofinites_with x. destruct_conjs. intuition.
  - dependent destruction H7. dependent destruction H16.
    constructor.
    + dependent destruction H8. dependent destruction H18.
      inst_cofinites_with_new.
      eapply lc_be_pi_exists with (x1:=x); destruct_conjs; auto.
    + eapply bmono_lambda with (L:=(L `union` L0 `union` L1)).
      intros. inst_cofinites_with x. destruct_conjs. intuition.
  - constructor; inst_cofinites_with_new. eapply lc_be_abs_exists with (x1:=x). destruct_conjs. auto.
    eapply lc_be_pi_exists with (x1:=x); destruct_conjs; auto.
  - constructor; inst_cofinites_with_new. eapply lc_be_abs_exists with (x1:=x). destruct_conjs. auto.
    eapply lc_be_pi_exists with (x1:=x); destruct_conjs; auto. 
  - dependent destruction H5. dependent destruction H13. eapply bmono_pi with (L:=L `union` L0 `union` L1).
    + intuition. 
    + intros. inst_cofinites_with x. destruct_conjs. intuition. 
  - dependent destruction H5. dependent destruction H13. eapply bmono_pi with (L:=L `union` L0 `union` L1).
    + intuition. 
    + intros. inst_cofinites_with x. destruct_conjs. intuition. 
  - inst_cofinites_with_new. eapply lc_be_pi_exists with (x1:=x); destruct_conjs; auto.
  - inst_cofinites_with_new. eapply lc_be_pi_exists with (x1:=x); destruct_conjs; auto.
  - dependent destruction H2. dependent destruction H3. constructor; intuition.
  - dependent destruction H2. dependent destruction H3. constructor; intuition.
  - dependent destruction H9. dependent destruction H18.
    econstructor.
    + inst_cofinites_with_new. eapply lc_be_all_exists with (x1:=x); intuition.
    + eapply bmono_bind with (L:=L `union` L0 `union` L1). intros. inst_cofinites_with x. intuition.
  - dependent destruction H9. dependent destruction H18.
    econstructor.
    + inst_cofinites_with_new. eapply lc_be_all_exists with (x1:=x); intuition.
    + eapply bmono_bind with (L:=L `union` L0 `union` L1). intros. inst_cofinites_with x. intuition.
  - econstructor.
    + inst_cofinites_with_new. apply lc_be_bind_exists with (x1:=x). destruct_conjs. auto.
    + inst_cofinites_with_new. apply lc_be_all_exists with (x1:=x); destruct_conjs; auto.
  - econstructor.
    + inst_cofinites_with_new. apply lc_be_bind_exists with (x1:=x). destruct_conjs. auto.
    + inst_cofinites_with_new. apply lc_be_all_exists with (x1:=x); destruct_conjs; auto.
  - dependent destruction H4. dependent destruction H15. constructor; intuition.
  - dependent destruction H4. dependent destruction H15. constructor; intuition.
  - dependent destruction H2. dependent destruction H3. constructor; intuition.
  - dependent destruction H2. dependent destruction H3. constructor; intuition.
  - inst_cofinites_with_new. eapply lc_be_all_exists with (x1:=x); destruct_conjs; auto. 
  - inst_cofinites_with_new. eapply lc_be_all_exists with (x1:=x); destruct_conjs; auto. 
  - inst_cofinites_with_new. eapply lc_be_all_exists with (x1:=x); destruct_conjs; auto. 
  - inst_cofinites_with_new. eapply lc_be_all_exists with (x1:=x); destruct_conjs; auto. 
  - constructor; intuition.
  - constructor; intuition.
Qed. 


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
    + eapply usub_elab_keeps_mono; eauto.
    + eapply iapp_pi with (k:=bk_star); intros.
      * admit. (* type_correctness *)
      * eapply bs_sub with (A:=A'0); eauto...
        admit. (* type_correctness *)
  - eapply bs_anno.
    + eapply bs_bind with (L:=L).
      * eauto...
      * intros. inst_cofinites_with x. eauto... 
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
    + eapply usub_elab_keeps_mono; eauto. 
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


Theorem bidir_sound : forall Γ' e1' e2' d A' Γ e1 e2 A,
    busub_elab Γ' e1' e2' d A' Γ e1 e2 A → Γ ⊢ e1 <: e2 : A.
Proof.
  intros.
  pattern Γ', e1', e2', d, A', Γ, e1, e2, A, H.
  eapply busub_elab_mut with
    (P0 := fun Γ' Γ (_ : wf_bcontext_elab Γ' Γ) => ⊢ Γ )
    (P1 := fun Γ' A' t' B' Γ A t B (_ : infer_app_elab Γ' A' t' B' Γ A t B) =>
      exists D E, B = E ^^ t /\ Γ ⊢ t : D /\ (Γ ⊢ A <: e_pi D E : ⋆ \/ A = e_pi D E)
    )
    (P2 := fun Γ' A' B' (_ : greduce_elab Γ' A' B') => True);
    intros; try (constructor; auto; fail).
  - eauto.
  - eauto.
  - eauto.
  - destruct H1 as [D [E]]. destruct_conjs.
    rewrite H1. econstructor.
    + admit. (* monotype *)
    + eauto.
    + inversion H3.
      * econstructor; eauto.
      * rewrite <- H4. auto.
  - econstructor; eauto.
    + intros. admit. (* fv_eexpr *)
    + intros. admit. (* fv_eexpr *)
  - econstructor; eauto.
    + admit. (* breduce *)
    + admit. (* breduce *)
  - econstructor.
    + eauto.
    + admit. (* P2 breduce *)
    + eauto.
  - eapply ott.s_forall_l with (t:=t).
    + admit. (* monotype *)
    + eauto.
    + eauto.
    + auto.
    + eauto.
  - econstructor; eauto.
  - eapply ott.s_forall; eauto.
  - auto.
  - eapply ott.s_sub; eauto.
  - econstructor; eauto.
    + admit. (* ctx_dom *)
  - exists A0, B. auto.
  - destruct H2 as [D [E ]]. exists D, E. destruct_conjs. repeat split; auto.
    inversion H4; left; eapply ott.s_forall_l with (t:=t); eauto.
    + admit.
    + admit.
    + admit.
    + admit.
    + rewrite <- H5. admit.
Admitted.


 
