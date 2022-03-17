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
      * intros. simpl. admit. (* fv_eexpr *)
      * intros. simpl. admit. (* fv_eexpr *)
    + eapply bs_forall with (L:=L); eauto...
      * intros. admit. (* type_correctness *)
    + eapply bs_forall with (L:=L); eauto...
      * intros. admit. (* type_correctness *)
  - econstructor.
    eapply bs_castup with (B:=B').
    + eapply bidir_refl_l in H0. exact H0.
    + admit. (* breduce *)
    + eapply bs_sub with (A:=B'). auto. admit. (* type_correctness *)
    + exact H0.
    + exact H1.
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


Theorem bidir_sound : forall Γ' e1' e2' d A' Γ e1 e2 A,
    busub_elab Γ' e1' e2' d A' Γ e1 e2 A → Γ ⊢ e1 <: e2 : A.
Proof.
  induction 1.
  1-5: admit.
  - econstructor. admit.
Admitted.


(*
Theorem bidir_complete : forall Γ e1 e2 A
  , Γ ⊢ e1 <: e2 : A
  -> to_bcontext Γ ⊢ to_bexpr e1 <: to_bexpr e2 ⇒ to_bexpr A.
Proof.
  intros. pattern Γ, e1, e2, A, H.
  apply usub_mut with
    (P0 := fun Γ (_ : ⊢ Γ) => bwf_context (to_bcontext Γ)); intros.
(* busub *)
  (* var *)
  - constructor; auto. induction i; simpl in *.
    + apply inb_here. apply to_bcontext_keeps_lc. auto. eapply to_bexpr_keeps_lc; auto.
    + apply inb_there. eapply to_bexpr_keeps_lc; eauto.
      eapply IHi. inversion w. auto. inversion H0. auto.
  (* num *)
  - constructor. auto.
  (* star *)
  - constructor. auto.
   (* int  *)
  - constructor. auto.
  (* bot *)
  - simpl. destruct k; econstructor; eauto.
    + eapply bs_bot. apply bidir_refl_l in H0. eauto.
    + eapply bs_bot. apply bidir_refl_l in H0. eauto.
  (* abs *)
  - simpl. econstructor.
    + eapply bs_abs with (k1:= to_bk k1) (k2:= to_bk k2) (L:=L).
      * apply bidir_refl_l in H0. destruct k1; simpl in *; eauto.
      * intros. specialize (H2 x H5). apply bidir_refl_l in H2.
        rewrite_to_expr B1 x. destruct k2; simpl in *; auto.
      * intros. eapply bs_sub with (A:=(to_bexpr (B1 ^` x))) (k:=to_bk k2).
        -- rewrite_to_expr e0 x. rewrite_to_expr e3 x. auto.
           specialize (H4 x H5). simpl in H4. auto.
        -- specialize (H2 x H5). apply bidir_refl_l in H2.
          rewrite_to_expr B1 x. simpl in H2. destruct k2; auto.
    + eapply bs_pi_inf with (k1:=to_bk k1) (k2:=to_bk k2) (L:=L).
      * eapply bidir_refl_l in H0. destruct k1; simpl in *; eauto.
      * destruct k1; eauto.
      * intros. specialize (H2 x H5). apply bidir_refl_l in H2.
        rewrite_to_expr B1 x. simpl in H2. destruct k2; auto.
      * intros. specialize (H2 x H5). simpl in H2.
        replace ((to_bcontext G),' x : (to_bexpr A1)) with ((to_bcontext G),' x : (to_bexpr A1),,'bctx_nil) in H2.
        eapply bidir_narrowing with (A:=to_bexpr A2) (k:=to_bk k1) in H2.
        -- rewrite_to_expr B1 x. rewrite_to_expr B2 x. destruct k2; auto.
        -- destruct k1; auto.
        -- auto.
    + eapply bs_pi_inf with (k1:=to_bk k1) (k2:=to_bk k2) (L:=L).
      * eapply bidir_refl_l in H1. destruct k1; simpl in *; eauto.
      * destruct k1; eauto.
      * intros. specialize (H3 x H5). simpl in H3.
        replace ((to_bcontext G),' x : (to_bexpr A1)) with ((to_bcontext G),' x : (to_bexpr A1),,'bctx_nil) in H3.
        eapply bidir_narrowing with (A:=to_bexpr A2) (k:=to_bk k1) in H3. simpl in H3.
        -- apply bidir_refl_l in H3. rewrite_to_expr B2 x. destruct k2; auto.
        -- destruct k1; auto.
        -- auto.
      * intros. specialize (H3 x H5).
        simpl in H3. rewrite_to_expr B1 x. rewrite_to_expr B2 x. destruct k2; auto.
  (* pi *)
  - replace (to_bexpr (e_pi A1 B1)) with (be_pi (to_bexpr A1) (to_bexpr B1)) by auto.
    replace (to_bexpr (e_pi A2 B2)) with (be_pi (to_bexpr A2) (to_bexpr B2)) by auto.
    replace (to_bexpr ⧼ k2 ⧽) with (⧼ to_bk k2 ⧽') by (destruct k2; auto).
    eapply bs_pi_inf with (k1:=to_bk k1) (L:=L).
    + destruct k1; auto.
    + destruct k1; auto.
    + intros. specialize (H2 x H4). rewrite_to_expr B1 x.
      destruct k2; auto.
    + intros. specialize (H3 x H4). rewrite_to_expr B1 x. rewrite_to_expr B2 x.
      destruct k2; auto.
  - eapply bs_app with (A:=(to_bexpr (e_pi A0 B))); fold to_bexpr.
    + apply to_bexpr_keeps_mono_type. auto.
    + auto.
    + replace (to_bexpr (B ^^ t)) with ((to_bexpr B) ^^' (to_bexpr t)) by (eapply open_bexpr_wrt_bexpr_rec_exchanges_to_bexpr; eauto).
      econstructor; fold to_bexpr.
      * intros. admit. (* *** *)
      * eapply bs_sub. exact H0.
        admit. (* type_correctness *)
  - econstructor; fold to_bexpr.
    + eapply bs_bind with (k:=to_bk k) (L:=L); fold to_bexpr.
      * apply bidir_refl_l in H0. destruct k; auto.
      * intros. specialize (H2 x H5). apply bidir_refl_l in H2. simpl in H2.
        rewrite_to_expr B1 x. auto.
      * intros. specialize (H4 x H5). simpl in H4.
        eapply bs_sub with (k:=bk_star).
        rewrite_to_expr e0 x. rewrite_to_expr e3 x. eauto.
        rewrite_to_expr B1 x.
        specialize (H2 x H5). apply bidir_refl_l in H2. simpl in H2. auto.
      * intros. rewrite_to_expr e0 x.
        specialize (n x H5). rewrite (to_bexpr_keeps_fv (e0 ^` x)) in n.
        apply n.
      * intros. rewrite_to_expr e3 x.
        specialize (n0 x H5). rewrite (to_bexpr_keeps_fv (e3 ^` x)) in n0.
        apply n0.
    + eapply bs_forall with (k:=to_bk k); fold to_bexpr.
      * destruct k; eauto.
      * destruct k; eauto.
      * intros. specialize (H2 x H5). simpl in H2.
        rewrite_to_expr B1 x. rewrite_to_expr B2 x. auto.
    + eapply bs_forall with (k:=to_bk k); fold to_bexpr.
      * destruct k; auto.
      * destruct k; auto.
      * intros. specialize (H3 x H5). simpl in H3.
        rewrite_to_expr B2 x. rewrite_to_expr B1 x. auto.
        replace ((to_bcontext G),' x : (to_bexpr A1)) with ((to_bcontext G),' x : (to_bexpr A1),,'bctx_nil) in H3.
        eapply bidir_narrowing with (A:=to_bexpr A2) (k:=to_bk k) in H3.
        auto. destruct k; auto. auto.
  - simpl. eapply bs_anno with (k:=to_bk k).
    eapply bs_castup with (k:=to_bk k) (B:=to_bexpr B).
    + apply bidir_refl_l in H0. destruct k; auto.
    + apply to_bexpr_keeps_reduce. auto.
    + eapply bs_sub with (A:=to_bexpr B). auto.
      admit. (* type_correctness *)
    + destruct k; auto.
    + destruct k; auto.
  - eapply bs_castdn with (k:=to_bk k) (A:=to_bexpr A0); fold to_bexpr.
    + destruct k; auto.
    + constructor.
      * apply to_bcontext_keeps_lc. apply wf_lc. eapply usub_context_is_wf. eauto.
      * apply to_bexpr_keeps_reduce. auto.
    + auto.
   - eapply bs_forall_l with (t:=to_bexpr t) (k:=to_bk k); fold to_bexpr.
    + apply to_bexpr_keeps_mono_type. auto.
    + destruct k; auto.
    + eapply bs_sub with (k:=to_bk k); eauto.
      destruct k; auto.
    + replace (to_bexpr (B ^^ t)) with ((to_bexpr B) ^^' (to_bexpr t)) in H2 by (eapply open_bexpr_wrt_bexpr_rec_exchanges_to_bexpr; eauto).
      auto.
    + intros. specialize (H3 x H4). simpl in H4.
      rewrite_to_expr B x. auto.
  - eapply bs_forall_r with (k:=to_bk k) (L:=L).
    + destruct k; auto.
    + auto.
    + intros. fold to_bexpr. specialize (H2 x H3). simpl in H2.
      rewrite_to_expr C x. auto.
  - eapply bs_forall with (k:=to_bk k) (L:=L).
    + destruct k; auto.
    + destruct k; auto.
    + intros. fold to_bexpr. specialize (H2 x H3). simpl in H2.
      rewrite_to_expr B x. rewrite_to_expr C x. auto.
  - admit.
(* wf_context *)
  - constructor.
  - simpl. apply bwf_cons with (k:=to_bk k).
    + auto.
    + apply to_bcontext_keeps_notin; auto.
    + destruct k; auto.
Admitted.


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
