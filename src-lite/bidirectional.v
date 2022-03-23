Require Import Program.Tactics.
Require Import Metalib.FSetWeakNotin.

Require Import decl.properties.
Require Import bidir.notations.
Require Import bidir.properties.
Require Import bidir.elaboration.
Require Import transform_properties.
Require Import ln_utils.

(* Theorem bidir_complete1 : forall Γ e1 e2 A
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
Admitted. *)

(* Theorem bidir_complete2 : forall Γ e1 e2 A
  , Γ ⊢ e1 <: e2 : A
  → to_bcontext Γ ⊢ to_bexpr e1 <: to_bexpr e2 ⇐ to_bexpr A.
Proof.
  induction 1.
  1-7: admit.
  - admit.
Admitted. *)

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

Ltac destruct_mono :=
  repeat
    match goal with
    | H : mono_type (?P ?x) |- _ => dependent destruction H
    end.

Ltac solve_trivial_mono := 
  destruct_mono; econstructor; intuition; eauto; fail.

Ltac usub_elab_keeps_mono_impl H L L0 L1 := 
  apply H with (L:=(L `union` L0 `union` L1)); try (intuition; fail); intros x Hx; inst_cofinites_with x; destruct_conjs; intuition.

Lemma usub_elab_keeps_mono : forall Γ e1 e2 A Γ' e1' e2' A',
   usub_elab Γ e1 e2 A Γ' e1' e2' A' ->
       (mono_type e1 /\ mono_type e2 -> mono_btype e1' /\ mono_btype e2').
Proof.
 intros.
 induction H; repeat split; destruct_conjs; intros; auto; try solve_trivial_mono.
 - destruct_mono. econstructor.
   + destruct_mono. usub_elab_keeps_mono_impl bmono_lambda L L0 L1.
   + destruct_mono. usub_elab_keeps_mono_impl bmono_pi L L0 L1.
  - destruct_mono. econstructor.
    + usub_elab_keeps_mono_impl bmono_lambda L L0 L1.
    + usub_elab_keeps_mono_impl bmono_pi L L0 L1.
  - destruct_mono. usub_elab_keeps_mono_impl bmono_pi L L0 L1.
  - destruct_mono. usub_elab_keeps_mono_impl bmono_pi L L0 L1.
  - destruct_mono. admit.
  - admit.
  - constructor; intuition. admit.
  - constructor; intuition. admit.
Admitted.


Ltac simpl_auto_impl := simpl in *; auto; fail.

Lemma usub_elab_keeps_feexpr : forall Γ e1 e2 A Γ' e1' e2' A' x,
   usub_elab Γ e1 e2 A Γ' e1' e2' A' -> x `notin` ott.fv_eexpr (erase e1) ->  x `notin` ott.fv_eexpr (berase e1').
Proof.
  intros.
  induction H; try simpl_auto_impl. 
  - admit.
  - admit. 
  - admit.
  - admit.
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
    + eapply bs_pi with (L:=L); eauto.
      * inst_cofinites_with_new...
      * intros. inst_cofinites_with x...
      * intros. inst_cofinites_with x.
        replace (Γ'0,' x : A2') with (Γ'0,' x : A2',,'bctx_nil) by auto.
        eapply bidir_narrowing with (B:=A1'); simpl; eauto.
    + eapply bs_pi with (L:=L); eauto...
      * intros. inst_cofinites_with x...
        replace (Γ'0,' x : A2') with (Γ'0,' x : A2',,'bctx_nil) by auto.
        eapply bidir_narrowing with (B:=A1'); simpl; eauto...
  - econstructor; eauto... 
  - econstructor; eauto...
    + eapply usub_elab_keeps_mono; eauto.
    + constructor; admit.
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
  - econstructor; eauto. 
  - econstructor.
    + auto.
    + admit. (* ctx_dom *)
    + exact H1.
Admitted.


(* completeness / totality of elaboration system *)
(* Theorem usub_elab_total : forall Γ e1 e2 A
  , Γ ⊢ e1 <: e2 : A
  → usub_elab Γ e1 e2 A
              (to_bcontext Γ) (to_bexpr e1) (to_bexpr e2) (to_bexpr A).
Proof.
  induction 1.
  1-14: admit.
  - simpl. admit. 
Admitted. *)


Theorem bidir_sound : forall Γ' e1' e2' d A' Γ e1 e2 A,
    busub_elab Γ' e1' e2' d A' Γ e1 e2 A → Γ ⊢ e1 <: e2 : A.
Proof.
  intros.
  pattern Γ', e1', e2', d, A', Γ, e1, e2, A, H.
  eapply busub_elab_mut with
    (P0 := fun Γ' Γ (_ : wf_bcontext_elab Γ' Γ) => ⊢ Γ )
    (P1 := fun Γ' A' F' Γ A F  (_ : infer_app_elab Γ' A' F' Γ A F) =>
      match F with 
      | dfun_pi B C => 
        match A with 
        | e_pi B' C' => True
        | e_all B' C' => Γ ⊢ A <: e_pi B C : ⋆ 
        | _ => False
        end  
      end
    )
    (P2 := fun Γ' A' B' (_ : greduce_elab Γ' A' B') => True);
    intros; try (constructor; auto; fail).
  - eauto.
  - eauto.
  - eauto.
  - dependent destruction i.
    + econstructor. admit. eauto. auto.
    + econstructor. admit. eauto. eapply ott.s_sub; eauto.
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
  - dependent destruction F. dependent destruction i.
    + rewrite x. rewrite <- x in H1. econstructor; assert (mono_type t) by admit; eauto; admit.  
    + rewrite <- x in H3. econstructor; assert (mono_type t) by admit; eauto. admit. rewrite <- x. auto. admit.
Admitted.


 
