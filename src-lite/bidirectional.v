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
  - destruct_mono. admit.  (* *** *)
  - admit.  (* *** *)
  - constructor; intuition. admit.  (* *** *)
  - constructor; intuition. admit.  (* *** *)
Admitted.

Scheme expr_ind_mut 
    := Induction for expr Sort Prop
  with Induction for body Sort Prop.

Lemma open_expr_wrt_new_var_keeps_notin_erase : forall e x x' n0,
  x <> x' -> x `notin` ott.fv_eexpr (erase e) <-> x `notin` ott.fv_eexpr (erase (open_expr_wrt_expr_rec n0 `x' e)).
Proof.
  intros; split; intros. 
  - generalize dependent n0. generalize dependent H0. pattern e.
    eapply expr_ind_mut with 
    (P0 := fun b => 
      match b with 
      | b_anno e A => forall n0, 
          x `notin` ott.fv_eexpr (erase e) ->
          x `notin` ott.fv_eexpr (erase (open_expr_wrt_expr_rec n0 `x' e))
      end
    ); intros; auto; try (simpl in *; auto; fail).
    + simpl. destruct (lt_eq_lt_dec n n0); simpl.
      * destruct s; simpl; auto.
      * auto.
    + destruct b; simpl in *; auto. 
    + destruct b; simpl in *; auto.
  - generalize dependent n0. pattern e. 
    eapply expr_ind_mut with 
    (P0 := fun b => 
      match b with 
      | b_anno e A => forall n0, 
          x `notin` ott.fv_eexpr (erase (open_expr_wrt_expr_rec n0 `x' e)) ->
          x `notin` ott.fv_eexpr (erase e) 
      end
    ); intros; auto; try (simpl in *; eauto; fail).  
    + destruct b; simpl in *. eauto. 
    + destruct b; simpl in *. eauto.
Qed.

Lemma open_bexpr_wrt_new_var_keeps_notin_berase : forall x x' e n0,
  x <> x' -> x `notin` ott.fv_eexpr (berase e) <-> x `notin` ott.fv_eexpr (berase (open_bexpr_wrt_bexpr_rec n0 `'x' e)).
Proof.
  intros; split; intros.
  - generalize dependent n0. generalize dependent H0.
    induction e; intros; auto; try (simpl in *; auto; fail).
    + simpl. destruct (lt_eq_lt_dec n n0); simpl.
      * destruct s; simpl; auto.
      * auto.
  - generalize dependent n0. 
    induction e; intros; auto; try (simpl in *; eauto; fail).
Qed.

Ltac auto_open_expr_wrt_new_var_keeps_notin_erase := 
  match goal with 
  | H : ?x `notin` ott.fv_eexpr (erase ?e) |- ?x `notin` ott.fv_eexpr (berase ?e') =>  
      match goal with 
      | H1 : ?x `notin` ott.fv_eexpr (erase (?e ^^ `?x0)) -> ?x `notin` ott.fv_eexpr (berase (?e' ^^' `' ?x0)) |- _ => 
        eapply open_expr_wrt_new_var_keeps_notin_erase with (x':=x0) (n0:=0) in H; eauto;
        specialize (H1 H); eapply open_bexpr_wrt_new_var_keeps_notin_berase with (n0:=0); eauto                                     
      end 
  end.


Lemma usub_elab_keeps_feexpr : forall Γ e1 e2 A Γ' e1' e2' A' x,
   usub_elab Γ e1 e2 A Γ' e1' e2' A' -> x `notin` ott.fv_eexpr (erase e1) ->  x `notin` ott.fv_eexpr (berase e1').
Proof.
  intros.
  induction H; try (simpl in *; auto; fail); simpl in *; inst_cofinites_by (add x L).
  - auto_open_expr_wrt_new_var_keeps_notin_erase. 
  - apply notin_union; auto. apply notin_union_2 in H0. 
    auto_open_expr_wrt_new_var_keeps_notin_erase. 
  - auto_open_expr_wrt_new_var_keeps_notin_erase.
  - apply notin_union; auto. apply notin_union_2 in H0.
    auto_open_expr_wrt_new_var_keeps_notin_erase. 
  - apply notin_union; auto. apply notin_union_2 in H0.
    auto_open_expr_wrt_new_var_keeps_notin_erase.
Qed.


Lemma wf_context_elab_same_dom : forall Γ Γ',
    wf_context_elab Γ Γ' -> ctx_dom Γ = bctx_dom Γ'.
Proof.
  intros. induction H; auto.
  simpl. rewrite IHwf_context_elab; auto.
Qed.

Theorem bidir_complete4 : forall Γ e1 e2 A Γ' e1' e2' A'
  , usub_elab Γ e1 e2 A Γ' e1' e2' A'
  → Γ' ⊢ e1' <: e2' ⇒ A'.
Proof with eauto with bidir.
  intros.
  pattern Γ, e1, e2, A, Γ', e1', e2', A', H.
  apply usub_elab_mut with 
    (P0 := 
      fun Γ Γ' (_ : wf_context_elab Γ Γ') => wf_bcontext Γ'); 
    intros; try (constructor; auto; fail).
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
    + constructor; eapply busub_all_lc; eauto.
  - eapply bs_anno.
    + eapply bs_bind with (L:=L).
      * eauto...
      * intros. inst_cofinites_with x. eauto... 
      * intros. eapply bs_sub.
        inst_cofinites_with x. eauto...
        eauto...
      * intros. simpl. inst_cofinites_with x. eapply usub_elab_keeps_feexpr; eauto. 
      * intros. simpl. inst_cofinites_with x. eapply usub_elab_keeps_feexpr; eauto.
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
  - econstructor; eauto.
    + rewrite <- (wf_context_elab_same_dom Γ0 Γ'0); auto.
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

Ltac destruct_bmono :=
  repeat
    match goal with
    | H : mono_btype (?P ?x) |- _ => dependent destruction H
    end.

Ltac solve_trivial_bmono := 
    destruct_bmono; econstructor; intuition; eauto; fail.   

Lemma busub_elab_keeps_mono : forall Γ' e1' e2' d A' Γ e1 e2 A,
   busub_elab Γ' e1' e2' d A' Γ e1 e2 A ->
       (mono_btype e1' /\ mono_btype e2' -> mono_type e1 /\ mono_type e2).
Proof.
  intros.
  induction H; repeat split; destruct_conjs; intros; auto; try solve_trivial_bmono.
  - econstructor. admit. (* *** *)
  - econstructor. admit. (* *** *)
  - destruct_bmono. eapply mono_lambda with (L:= L `union` L0 `union` L1); intros; inst_cofinites_with x; intuition.
    + admit. (* *** *)
    + admit. (* *** *)
  - destruct_bmono. eapply mono_lambda with (L:= L `union` L0 `union` L1); intros; inst_cofinites_with x; intuition.
    + admit. (* *** *)
    + admit. (* *** *)
  - destruct_bmono. eapply mono_pi with (L:= L `union` L0 `union` L1); intros; inst_cofinites_with x; intuition.
  - destruct_bmono. eapply mono_pi with (L:= L `union` L0 `union` L1); intros; inst_cofinites_with x; intuition.
  - destruct_bmono. eapply mono_bind with (L:= L `union` L0 `union` L1); intros; inst_cofinites_with x; intuition. 
    + admit. (* *** *)
    + admit. (* *** *)
  - destruct_bmono. eapply mono_bind with (L:= L `union` L0 `union` L1); intros; inst_cofinites_with x; intuition. 
    + admit. (* *** *)
    + admit. (* *** *)
  - destruct_bmono. constructor. intuition. admit. (* *** *)
  - destruct_bmono. constructor. intuition. admit. (* *** *)
  - destruct_bmono; intuition.
  - destruct_bmono; intuition.
  - intuition.
  - intuition.
Admitted.

Lemma inv_forall_new : forall Γ A B t,
  Γ ⊢ e_all A B : ⋆ -> mono_type t -> Γ ⊢ t : A -> Γ ⊢ B ^^ t : ⋆.
Proof.
  intros.
  dependent induction H.
Admitted.

Lemma inv_forall : forall Γ A B x,
  Γ ⊢ e_all A B : ⋆ ->  exists L, x `notin` L -> Γ, x : A ⊢ B ^^ `x :  ⋆.
Proof.
  intros.
  dependent induction H.
  - exists L. intros. eauto. 
  - exists L. intros. specialize (H1 x H3). apply refl_r in H1. auto.
  - exists L. intros. eauto.
  - eapply star_sub_inversion_l in H0. 
    apply (IHusub1 A B (eq_refl (e_all A B)) (eq_refl (e_all A B)) H0). 
Qed.

Lemma wf_bcontext_elab_same_dom : forall Γ' Γ,
  wf_bcontext_elab Γ' Γ -> bctx_dom Γ' = ctx_dom Γ.
Proof.
  intros. induction H; auto.
  simpl. rewrite IHwf_bcontext_elab; auto.
Qed.

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
        | e_pi _ _ => True
        | e_all _ _ => Γ ⊢ A : ⋆ -> Γ ⊢ A <: e_pi B C : ⋆
        | _ => False
        end  
      end
    );
    intros; try (constructor; auto; fail).
  - eauto.
  - eauto.
  - eauto.
  - dependent destruction i.
    + econstructor. admit. eauto. auto.
    + assert (Γ0 ⊢ e_all A0 B0 : ⧼ k_star ⧽) as Htc by admit. specialize (H3 Htc).
      econstructor. eapply busub_elab_keeps_mono; eauto. eauto. eapply ott.s_sub; eauto. 
  - econstructor; eauto.
    + intros. admit. (* fv_eexpr *)
    + intros. admit. (* fv_eexpr *)
  - econstructor; eauto.
    + admit. (* breduce *)
    + admit. (* breduce *)
  - eapply ott.s_castdn with (A:=A0).
    + eauto.
    + admit. (* P2 breduce *)
    + eauto.
  - eapply ott.s_forall_l with (t:=t); eauto.
    + eapply busub_elab_keeps_mono; eauto.
  - econstructor; eauto.
  - eapply ott.s_forall; eauto.
  - auto.
  - eapply ott.s_sub; eauto.
  - econstructor; eauto.
    + rewrite <- (wf_bcontext_elab_same_dom Γ'0 Γ0); auto. 
  - dependent destruction F. dependent destruction i.
    + intros. rewrite x.
      eapply ott.s_forall_l with (t:=t) (L:=ctx_dom Γ0).
      * eapply busub_elab_keeps_mono; eauto.
      * admit.
      * eauto.
      * eapply inv_forall_new; eauto. admit.
      * intros. admit.
    + intros. rewrite <- x in H3.
      assert (Γ0 ⊢ B ^^ t: ⧼ k_star ⧽) by admit.
      rewrite <- x in H5. specialize (H3 H5). econstructor.
      * admit.
      * admit.
      * eauto.
      * rewrite <- x. auto.
      * admit.
Admitted.


 
