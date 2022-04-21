Require Import Program.Tactics.
Require Import Metalib.FSetWeakNotin.

Require Import decl.properties.
Require Import bidir.notations.
Require Import bidir.properties.
Require Import bidir.elaboration.
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
(* Definition ctx_condition : context → bcontext → Prop := fun c c' => True.
Definition condition : expr → bexpr → Prop := fun e e' => True.

Theorem bidir_complete3 : forall Γ e1 e2 A
  , Γ ⊢ e1 <: e2 : A
  → exists Γ' e1' e2' A', Γ' ⊢ e1' <: e2' ⇒ A' ∧ ctx_condition Γ Γ'
    ∧ condition e1 e1' ∧ condition e2 e2' ∧ condition A A'.
Proof.
  induction 1.
  1-6: admit.
  - admit.
Admitted. *)

Ltac destruct_mono :=
  repeat
    match goal with
    | H : mono_type (?P ?x) |- _ => dependent destruction H
    end.

Ltac solve_lc_bexpr := 
  repeat 
    match goal with 
    | _ : _ |- lc_bexpr (be_abs ?e) => inst_cofinites_with_new; eapply lc_be_abs_exists; intuition; eauto
    | _ : _ |- lc_bexpr (be_pi ?e1 ?e2) =>  inst_cofinites_with_new; eapply lc_be_pi_exists; intuition; eauto
    | _ : _ |- lc_bexpr (be_all ?e1 ?e2) =>  inst_cofinites_with_new; eapply lc_be_all_exists; intuition; eauto
    | _ : _ |- lc_bexpr (be_bind ?e1) =>  inst_cofinites_with_new; eapply lc_be_bind_exists; intuition; eauto
    | _ : _ |- lc_bexpr (?e) => econstructor
    end.
    
Ltac solve_trivial_mono := 
  destruct_mono; econstructor; intuition; eauto; fail.

Ltac usub_elab_keeps_mono_impl H L L0 L1 := 
  apply H with (L:=(L `union` L0 `union` L1)); try (intuition; fail); intros x Hx; inst_cofinites_with x; destruct_conjs; intuition.

Lemma usub_elab_keeps_mono : forall Γ e1 e2 A Γ' e1' e2' A',
   usub_elab Γ e1 e2 A Γ' e1' e2' A' ->
       (mono_type e1 /\ mono_type e2 -> mono_btype e1' /\ mono_btype e2') /\ lc_bexpr e1' /\ lc_bexpr e2'.
Proof.
 intros.
 induction H; repeat split; destruct_conjs; intros; auto; try solve_trivial_mono; try solve_lc_bexpr.
 - destruct_mono. econstructor. inst_cofinites_with_new. eapply lc_be_pi_exists with (x1:=x); intuition. 
  + eapply bmono_lambda with (L:=L `union` (L0 `union` L1)). intros. inst_cofinites_with x. intuition. 
 - destruct_mono. econstructor. inst_cofinites_with_new. eapply lc_be_pi_exists with (x1:=x); intuition. 
  + eapply bmono_lambda with (L:=L `union` (L0 `union` L1)). intros. inst_cofinites_with x. intuition. 
 - destruct_mono. eapply bmono_pi with (L:=L `union` (L0 `union` L1)). intuition. intros. inst_cofinites_with x. intuition.
 - destruct_mono. eapply bmono_pi with (L:=L `union` (L0 `union` L1)). intuition. intros. inst_cofinites_with x. intuition.
 - destruct_mono. econstructor. solve_lc_bexpr.
   eapply bmono_bind with (L:=L `union` (L0 `union` L1)). intros. inst_cofinites_with x. intuition.
 - destruct_mono. econstructor. solve_lc_bexpr.
   eapply bmono_bind with (L:=L `union` (L0 `union` L1)). intros. inst_cofinites_with x. intuition.
Qed.

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
    induction e; intros; auto; try (simpl in *; eauto).
Qed.

Ltac convert_to_open_expr_wrt_new_var := 
  match goal with 
  | H : ?x `notin` ott.fv_eexpr (erase ?e) |- ?x `notin` ott.fv_eexpr (berase ?e') =>  
      match goal with 
      | H1 : ?x `notin` ott.fv_eexpr (erase (?e ^^ `?x0)) -> ?x `notin` ott.fv_eexpr (berase (?e' ^^' `' ?x0)) |- _ => 
        eapply open_expr_wrt_new_var_keeps_notin_erase with (x':=x0) (n0:=0) in H; eauto;
        specialize (H1 H); eapply open_bexpr_wrt_new_var_keeps_notin_berase with (n0:=0); eauto                                     
      end 
  end.


Lemma usub_elab_keeps_notin_fv_erase_l : forall Γ e1 e2 A Γ' e1' e2' A' x,
   usub_elab Γ e1 e2 A Γ' e1' e2' A' -> x `notin` ott.fv_eexpr (erase e1) ->  x `notin` ott.fv_eexpr (berase e1').
Proof.
  intros.
  induction H; try (simpl in *; auto; fail); simpl in *; inst_cofinites_by (add x L).
  - convert_to_open_expr_wrt_new_var. 
  - apply notin_union; auto. apply notin_union_2 in H0. 
    convert_to_open_expr_wrt_new_var. 
  - convert_to_open_expr_wrt_new_var.
  - apply notin_union; auto. apply notin_union_2 in H0.
    convert_to_open_expr_wrt_new_var. 
  - apply notin_union; auto. apply notin_union_2 in H0.
    convert_to_open_expr_wrt_new_var.
Qed.

Ltac convert_match_to_open_bexpr_wrt_new_var := 
  match goal with 
  | H : ?x `notin` ott.fv_eexpr (berase ?e') |- ?x `notin` ott.fv_eexpr (erase ?e) =>  
      match goal with 
      | H1 : ?x `notin` ott.fv_eexpr (berase (?e' ^^' `'?x0)) -> ?x `notin` ott.fv_eexpr (erase (?e ^^ ` ?x0)) |- _ => 
        eapply open_bexpr_wrt_new_var_keeps_notin_berase with (x':=x0) (n0:=0) in H; eauto;
        specialize (H1 H); eapply open_expr_wrt_new_var_keeps_notin_erase with (n0:=0); eauto                                     
      end 
  end.

Ltac convert_all_to_open_bexpr_wrt_new_var x0 := 
  repeat 
  match goal with 
  | e' : bexpr |- _ =>   
    match goal with 
    | H : ?x `notin` ott.fv_eexpr (berase e') |- _ =>  
        eapply open_bexpr_wrt_new_var_keeps_notin_berase with (x':=x0) (n0:=0) in H
    end                  
  | e : expr |- _ =>
    match goal with 
    | _ : _ |- ?x `notin` ott.fv_eexpr (erase e) =>
        eapply open_expr_wrt_new_var_keeps_notin_erase with (n0:=0)
    end
  end.


Lemma notin_union_equiv_notin_conj : forall x s s',
    x `notin` s `union` s' <-> x `notin` s /\ x `notin` s'.
Proof.
  intros; split; intros.
  - split.
    + apply notin_union_1 in H. auto.
    + apply notin_union_2 in H. auto.
  - destruct_conjs. apply notin_union; auto.
Qed.

Ltac destruct_notin_union :=
  repeat
    match goal with
    | H : ?x `notin` ?s `union` ?s' |- _ => apply notin_union_equiv_notin_conj in H; destruct_conjs
    end.


Lemma busub_elab_keeps_notin_fv_erase : forall Γ' e1' e2' d' A' Γ e1 e2 A x,
   busub_elab Γ' e1' e2' d' A' Γ e1 e2 A -> 
   (x `notin` ott.fv_eexpr (berase e1') -> x `notin` ott.fv_eexpr (erase e1)) /\
   (x `notin` ott.fv_eexpr (berase e2') -> x `notin` ott.fv_eexpr (erase e2)).
Proof.
  intros.
  induction H; try (simpl in *; split; destruct_conjs; auto); inst_cofinites_by (add x L); intros; destruct_conjs;
    try (convert_match_to_open_bexpr_wrt_new_var; eauto);
    try (destruct_notin_union; apply notin_union; auto; convert_match_to_open_bexpr_wrt_new_var; eauto).
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
    + eapply bs_pi with (L:=L); eauto...
    + eapply bs_pi with (L:=L); eauto...
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
      * intros. simpl. inst_cofinites_with x. eapply usub_elab_keeps_notin_fv_erase_l; eauto. 
      * intros. simpl. inst_cofinites_with x. eapply usub_elab_keeps_notin_fv_erase_l; eauto.
    + eauto... 
    + eapply bs_forall with (L:=L); eauto...
  - econstructor; eauto.
    eapply bs_castup with (B:=B'); eauto.
    + eapply bidir_refl_l in H0. exact H0.
    + admit. (* breduce *)
    + eapply bs_sub with (A:=B'). auto. admit. (* type_correctness *)
  - admit.
   (* eapply bs_castdn. exact H0. admit. breduce auto. *)
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
    destruct_bmono; try solve [intuition | econstructor; intuition; eauto]; fail.   

Ltac solve_lc_expr := 
  repeat 
    match goal with 
    | _ : _ |- lc_expr (e_abs ?e1 ?e2) => inst_cofinites_with_new; eapply lc_e_abs_exists; intuition; eauto; econstructor; 
                                      fold open_expr_wrt_expr_rec; intuition; eauto
    | _ : _ |- lc_expr (e_pi ?e1 ?e2) =>  inst_cofinites_with_new; eapply lc_e_pi_exists; intuition; eauto
    | _ : _ |- lc_expr (e_all ?e1 ?e2) =>  inst_cofinites_with_new; eapply lc_e_all_exists; intuition; eauto
    | _ : _ |- lc_expr (e_bind ?e1 ?e2) =>  inst_cofinites_with_new; eapply lc_e_bind_exists; intuition; eauto; econstructor; 
                                        fold open_expr_wrt_expr_rec; intuition; eauto
    end; auto.
        

Lemma busub_elab_keeps_mono : forall Γ' e1' e2' d A' Γ e1 e2 A,
   busub_elab Γ' e1' e2' d A' Γ e1 e2 A ->
       (mono_btype e1' /\ mono_btype e2' -> mono_type e1 /\ mono_type e2) /\ lc_expr e1 /\ lc_expr e2.
Proof.
  intros.
  induction H; repeat split; destruct_conjs; intros; auto; try solve_trivial_bmono; try solve_lc_expr.
  - destruct_bmono. eapply mono_lambda with (L:= L `union` L0 `union` L1); auto.
    + solve_lc_expr.
    + intros. inst_cofinites_with x; intuition.
  - destruct_bmono. eapply mono_lambda with (L:= L `union` L0 `union` L1); auto.
    + solve_lc_expr. 
    + intros. inst_cofinites_with x; intuition.
  - destruct_bmono. eapply mono_pi with (L:= L `union` L0 `union` L1).
    + intuition.
    + intros. inst_cofinites_with x. intuition.
  - destruct_bmono. eapply mono_pi with (L:= L `union` L0 `union` L1).
    + intuition.
    + intros. inst_cofinites_with x. intuition.
  - destruct_bmono. eapply mono_bind with (L:= L `union` L0 `union` L1); auto.
    + solve_lc_expr. 
    + intros. inst_cofinites_with x. intuition.
  - destruct_bmono. eapply mono_bind with (L:= L `union` L0 `union` L1); auto.
    + solve_lc_expr.
    + intros. inst_cofinites_with x. intuition. 
Qed.


Lemma inv_forall : forall Γ A B,
  Γ ⊢ e_all A B : ⋆ -> exists L, (forall x, x `notin` L -> Γ, x : A ⊢ B ^^ `x : ⋆ ).
Proof.
  intros.
  dependent induction H.
  - exists L. intros. eauto. 
  - exists L. intros. specialize (H1 x H3). apply refl_r in H1. auto.
  - exists L. intros. eauto.
  - eapply star_sub_inversion_l in H0. 
    apply (IHusub1 A B (eq_refl (e_all A B)) (eq_refl (e_all A B)) H0). 
Qed.


Lemma open_subst_usub : forall Γ x A B t,
  Γ, x : A ⊢ B ^^ ` x : ⧼ k_star ⧽ -> x `notin` fv_expr B -> Γ ⊢ t : A -> mono_type t -> Γ ⊢ B ^^ t : ⋆.
Proof.
  intros.
  specialize (substitution_cons Γ x ⧼ k_star ⧽ A (B ^^ ` x) (B ^^ ` x) t H H1 H2).
  simpl. intros.
  apply monotype_lc in H2.
  specialize (open_subst_eq B x t H0 H2). intros.
  rewrite <- H4 in H3. auto.
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
    )
    (P2 := fun Γ' A' B' (_ : greduce_elab Γ' A' B') =>
      breduce A' B'                                
    );
    intros; try (constructor; auto; fail).
  - eauto.
  - eauto.
  - eauto.
  - dependent destruction i.
    + econstructor.
      eapply busub_elab_keeps_mono; eauto. eauto. auto.
    + specialize (type_correctness Γ0 e0 e3 (e_all A0 B0) H0). intros.
      inversion H5. inversion H6. destruct H6 as [k]. destruct k.
      * specialize (H3 H6). econstructor. eapply busub_elab_keeps_mono; eauto. eauto. eapply ott.s_sub; eauto.
      * dependent destruction H6. apply refl_r in H6_0. eapply box_never_welltype in H6_0. contradiction.
  - econstructor; eauto.
    + intros. inst_cofinites_with x. eapply busub_elab_keeps_notin_fv_erase with (e1:=e0 ^^ `x) (e2:=e3 ^^ `x); eauto.
    + intros. inst_cofinites_with x. eapply busub_elab_keeps_notin_fv_erase; eauto.
  - econstructor; eauto.
    + admit. (* reduce *)
    + admit. (* reduce *)
  - eapply ott.s_castdn with (A:=A0).
    + eauto.
    + admit. (* reduce *)
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
      specialize (inv_forall Γ0 A0 B H2). intros. destruct H3 as [L].
      eapply type_correctness in H0 as HtcA. destruct HtcA.
      * subst. eapply not_eall_box in H2. contradiction. 
      * destruct H4 as [k]. eapply ott.s_forall_l with (t:=t); eauto.
        -- eapply busub_elab_keeps_mono; eauto.
        -- inst_cofinites_by (L `union` fv_expr B). eapply open_subst_usub; eauto.
           eapply busub_elab_keeps_mono; eauto.
    + intros. rewrite <- x in H3.
      specialize (inv_forall Γ0 A0 B H4). intros. 
      destruct H5 as [L]. inst_cofinites_by (L `union` fv_expr B `union` ctx_dom Γ0).
      assert (¬ x1 `in` fv_expr B ) by auto.
      assert (mono_type t) as Hmonot. { eapply busub_elab_keeps_mono with (e1':=t'); eauto. }
      specialize (open_subst_usub Γ0 x1 A0 B t H5 H6 H0 Hmonot). intros.
      eapply type_correctness in H0 as Htca. destruct Htca.
      * subst. eapply not_eall_box in H4. contradiction.
      * destruct H8 as [k]. rewrite <- x in H7. specialize (H3 H7). eapply ott.s_forall_l with (L:=L `union` ctx_dom Γ0 `union` singleton x1); eauto.
        -- rewrite <- x. auto.
        -- intros. 
           assert (⊢Γ0). { apply wt_wf in H8. auto. }
           assert (Γ0, x2 : A0, x1 : A0 ⊢ B ^^ ` x1 : ⧼ k_star ⧽). 
              { replace (Γ0, x2 : A0, x1 : A0) with (Γ0,,(ctx_nil, x2 : A0),,(ctx_nil, x1 : A0)). 
                apply weakening; auto. simpl. eapply ott.wf_cons with (k:=k); eauto.
                replace (Γ0, x2 : A0) with (Γ0,,(ctx_nil, x2 : A0),,ctx_nil).
                apply weakening; eauto. simpl. econstructor; eauto. auto. auto. 
              }
           assert (Γ0, x2 : A0 ⊢ ` x2 : A0). 
              { econstructor; auto. econstructor; auto. eauto.  apply usub_all_lc in H8. eapply in_here; intuition. }
            assert (mono_type ` x2) by auto.
            specialize (substitution_cons (Γ0, x2:A0) x1 ⧼ k_star ⧽ A0 (B ^^ ` x1) (B ^^ ` x1) (`x2) H11 H12 H13). simpl. 
            intros. eapply open_subst_usub; eauto.
  - admit. (* breduce *) 
  - admit. (* breduce *) 
Admitted.


 
