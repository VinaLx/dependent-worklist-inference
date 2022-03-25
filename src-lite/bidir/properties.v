Require Import decl.notations.
Require Export bidir.notations.
Require Import bidir.elaboration.
Require Import ln_utils.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.

Scheme Induction for busub Sort Prop
  with Induction for wf_bcontext Sort Prop
  with Induction for infer_app Sort Prop
  with Induction for greduce Sort Prop.


Lemma check_sub_invert : forall Γ e1 e2 A,
  Γ ⊢ e1 <: e2 ⇐ A ->
  A = ◻' \/ exists B k, Γ ⊢ B <: A ⇒ ⧼ k ⧽' /\ Γ ⊢ e1 <: e2 ⇒ B.
Proof.
  intros. dependent induction H; eauto.
Admitted.


Scheme  wf_bcontext_lc_mut := Induction for wf_bcontext Sort Prop
  with  busub_lc_mut       := Induction for busub       Sort Prop
  with  infer_app_lc_mut   := Induction for infer_app   Sort Prop.

Check wf_bcontext_lc_mut.

Ltac solve_lcb := 
  match goal with 
  | _ : _ |- lc_bexpr (be_abs ?e) => inst_cofinites_with_new; eapply lc_be_abs_exists; destruct_conjs; eauto
  | _ : _ |- lc_bexpr (be_pi ?A ?B ) => inst_cofinites_with_new; eapply lc_be_pi_exists; destruct_conjs; eauto
  | _ : _ |- lc_bexpr (be_bind ?e) => inst_cofinites_with_new; eapply lc_be_bind_exists; destruct_conjs; eauto
  | _ : _ |- lc_bexpr (be_all ?A ?B ) => inst_cofinites_with_new; eapply lc_be_all_exists; destruct_conjs; eauto
  end.


Lemma bwf_lc : forall Γ',
  ⫦ Γ' -> lc_bcontext Γ'.
Proof.
  intros.
  pattern Γ', H.
  eapply wf_bcontext_lc_mut with 
  (P0 := 
    fun Γ' e1' e2' d A' (_ : busub Γ' e1' e2' d A') => lc_bexpr e1' /\ lc_bexpr e2' /\ lc_bexpr A'
  )
  (P1 := fun Γ' A' F' (_ : infer_app Γ' A' F') => 
    match F' with 
    | fun_pi B C => forall x, lc_bexpr (C ^^' `'x)
    end
  )
  ; intros; try (intuition; fail); repeat split; auto; try solve_lcb.
  - induction i; auto. dependent destruction H0. dependent destruction w. auto.
  - intuition.
  - intuition.
  - dependent destruction l0. auto.
Qed.

Lemma bidir_lc : forall Γ' e1' e2' A',
  Γ' ⊢ e1' <: e2' ⇒ A' -> lc_bcontext Γ' /\ lc_bexpr e1' /\ lc_bexpr e2'.
Proof.
  intros.
  induction H; try (intuition; fail); repeat split; auto; try solve_lcb; intuition; eapply bwf_lc; auto.
Qed.


Scheme busub_refl_mut := Induction for busub     Sort Prop
  with  iapp_refl_mut := Induction for infer_app Sort Prop.


Theorem bidir_refl_l : forall Γ e1 e2 d A,
  busub Γ e1 e2 d A -> busub Γ e1 e1 d A.
Proof.
  intros; induction H; eauto.
Qed.

Hint Resolve bidir_refl_l : bidir.

Theorem bidir_elab_refl_l : forall Γ' e1' e2' d A' Γ e1 e2 A,
  busub_elab Γ' e1' e2' d A' Γ e1 e2 A -> 
  busub_elab Γ' e1' e1' d A' Γ e1 e1 A.
Proof.
  intros.
  induction H; try solve [ auto | econstructor; eauto ].
Qed.

Lemma lc_binsert_middle : forall Γ1 Γ2 Γ3,
    lc_bcontext Γ2 -> lc_bcontext (Γ1,,'Γ3) -> lc_bcontext (Γ1,,'Γ2,,'Γ3).
Proof.
  intros.
  induction Γ2.
  - auto.
  - inversion H. simpl in *.
    induction Γ3.
    + simpl in *. constructor; auto.
    + simpl in *. inversion H0. 
      specialize (IHΓ2 H3). inversion IHΓ2.
      constructor; auto.
Qed.

Lemma lc_bmiddle : forall Γ1 Γ2 Γ3,
    lc_bcontext (Γ1,,'Γ2,,'Γ3) -> lc_bcontext Γ2.
Proof.
  intros.
  induction Γ3.
  - induction Γ2; simpl in *. auto.
    inversion H. constructor; auto.
  - inversion H. auto.
Qed.

Lemma in_bctx_weakening : forall Γ1 Γ2 Γ3 x A,
    lc_bcontext Γ2 -> in_bctx x A (Γ1 ,,' Γ3) -> in_bctx x A (Γ1 ,,' Γ2 ,,' Γ3).
Proof.
  intros.
  induction Γ3.
  - induction Γ2.
    + auto.
    + inversion H. simpl in *. econstructor; auto.
  - simpl in *. inversion H0. subst.
    + apply inb_here. 2: auto. apply lc_binsert_middle; auto.
    + apply inb_there. auto. apply IHΓ3. auto.
Qed.

Theorem bidir_weakening : forall Γ1 Γ2 Γ3 e1 e2 d A,
  busub (Γ1,,'       Γ3) e1 e2 d A -> ⫦ Γ1 ,,' Γ2 ,,' Γ3 ->
  busub (Γ1,,' Γ2,,' Γ3) e1 e2 d A.
Proof.
  intros until A. intro Hsub.
  dependent induction Hsub; intro Hwf; auto.
  - constructor. auto. eapply in_bctx_weakening; auto. admit.
  - econstructor. eapply IHHsub; auto.
  - econstructor. eapply IHHsub; auto. auto.
    intros. specialize (H2 x H3). admit. admit.
  - econstructor. eapply IHHsub1; auto. eapply IHHsub2; auto. auto. admit. admit.
  - econstructor. auto. admit. admit. admit. (* *** *)
  - econstructor.
Admitted.

(* Theorem bidir_elab_weakening : forall Γ1' Γ2' Γ3' e1' e2' d k Γ1 Γ2 Γ3 e1 e2,
  busub_elab (Γ1',,'         Γ3') e1' e2' d ⧼k⧽' (Γ1,,      Γ3) e1 e2 ⧼(to_k k)⧽ ->
  wf_context_elab (Γ1',,'Γ2',,'Γ3') (Γ1,,Γ2,,Γ3) ->
  busub_elab (Γ1',,'  Γ2',,' Γ3') e1' e2' d ⧼k⧽' (Γ1,, Γ2,, Γ3) e1 e2 ⧼(to_k k)⧽.
Proof.
  intros.
Admitted. *)

Theorem bidir_narrowing : forall Γ1 x B Γ2 e1 e2 d C,
  busub (Γ1,' x : B,,' Γ2) e1 e2 d C -> 
  forall A k, Γ1 ⊢ A <: B ⇒ ⧼ k ⧽' -> 
  busub (Γ1,' x : A,,' Γ2) e1 e2 d C.
Proof.
Admitted.


Hint Resolve bidir_narrowing : bidir.

(* Theorem bidir_elab_narrowing : forall Γ1' x B' Γ2' e1' e2' d C' Γ1 B Γ2 e1 e2 C,
  busub_elab (Γ1',' x : B',,' Γ2') e1' e2' d C' (Γ1, x : B,, Γ2) e1 e2 C ->
  forall A A' k, Γ1' ⊢ A' <: B' ⇒ ⧼ k ⧽' ->
  busub_elab (Γ1',' x : A',,' Γ2') e1' e2' d C' (Γ1, x : A,, Γ2) e1 e2 C.
Proof.
Admitted. *)


