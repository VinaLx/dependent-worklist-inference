Require Import worklist.
Require Import decl_worklist.
Require Import transfer.syntax.
Require Import transfer.properties.

Require Import decl.notations.
Require Import Equality.
Require Import ln_utils.

Require Import alg.ln_inf_extra.

Lemma bwf_prefix : forall Γ1 Γ2, ⫦ Γ1 ,,' Γ2 → ⫦ Γ1.
Proof.
  induction Γ2; simpl; intros; auto.
  - inversion H; subst; auto.
Qed.

#[export]
Hint Resolve bwf_prefix : btyping.

Lemma bctx_dwl_dom : forall Γ
  , bctx_dom ⌊ Γ ⌋ [=] dwl_dom Γ.
Proof.
  induction Γ; simpl; fsetdec.
Qed.

Lemma solve_wf : forall Γ, ⪧ Γ → ⫦ ⌊ Γ ⌋.
Proof.
  induction 1; simpl in *; auto.
  - destruct ob; simpl in *; auto.
    now dependent destruction IHdwl_step.
  - rewrite app_to_bctx_distr in IHdwl_step.
    eauto using bwf_prefix.
  - econstructor; eauto.
    assert (bctx_dom ⌊ Γ ⌋ [=] dwl_dom Γ) by apply bctx_dwl_dom.
    fsetdec.
Qed.

#[export]
  Hint Resolve solve_wf : core.

Lemma wl_app_assoc : forall Γ1 Γ2 Γ3,
  Γ1 ⫢ Γ2 ⫢ Γ3 = Γ1 ⫢ (Γ2 ⫢ Γ3).
Proof.
  induction Γ3; simpl; auto.
Qed.

Lemma wl_ocons_assoc : forall Γ1 Γ2 ob,
    Γ1 ⫢ Γ2 ,? ob = Γ1 ⫢ (Γ2 ,? ob).
Proof.
  destruct ob; auto.
Qed.

Lemma solve_prefix : forall Γ1 Γ2,
    ⪧ Γ1 ⫢ Γ2 → ⪧ Γ1.
Proof.
  intros.
  dependent induction H;
    destruct Γ2; simpl in *;
    inversion x; subst;
    eauto.
  - now eapply IHdwl_step with (Γ4 := Γ2 ⊨ c $ A).
  - now eapply IHdwl_step with (Γ4 := Γ2 ⊨ c $ B ^^' e1).
  - now eapply IHdwl_step with (Γ4 := Γ2 ⊨ c $ B).
  - eapply IHdwl_step with (Γ4 := Γ2,? ob ⊨ e1 <: e2 ⇒ dc_check A).
    simpl. now rewrite wl_ocons_assoc.
  - eapply IHdwl_step with (Γ4 := Γ2 ⫢ Γ').
    apply wl_app_assoc.
Qed.

Corollary solve_uncons : forall Γ w,
    ⪧ Γ ⊨ w → ⪧ Γ.
Proof.
  intros *.
  replace (Γ ⊨ w) with (Γ ⫢ (dwl_nil ⊨ w)) by auto.
  apply solve_prefix.
Qed.

Lemma binds_notin_absurd : forall A x (e : A) xs,
    binds x A xs → x `notin` dom xs → False.
Proof.
  induction xs; simpl; intros.
  - inversion H.
  - destruct a. destruct H.
    + inversion H; subst. assert (x <> x) by auto. contradiction.
    + eauto.
Qed.

Ltac discharge_bind :=
  match goal with
  | H : binds ?x ?e1 (pair ?y ?e2 :: ?xs) |- _ =>
      destruct H as [H | H];
      [> inversion H; subst
      |  try solve [exfalso; eauto using binds_notin_absurd]]
  end
.

Ltac destruct_inst :=
  match goal with
  | H : _ ⊩ _ :?′ _ ⇝? _ |- _ =>
      dependent destruction H
  | H : _ ⊩ ob_none ⇝? _ |- _ =>
      dependent destruction H
  | H : _ ⊩ _ ⊨′ _ ⟿ ?Γ ⫣ _ |- _ =>
      lazymatch Γ with
      | _ ⊨ _ => fail
      | _ => dependent destruction H
      end
  | H : _ ; ?x0 ≔ ⧼ _ ⧽ ⊩ ⧼ `^ ?x0 ⧽ ⇝ _ |- _ =>
      dependent destruction H; discharge_bind
  | H : _ ⊩ _ ,′ _ ⟿ _ ⫣ _ |- _ =>
      dependent destruction H
  | H : _ ⊩ _ $′ _ ⇝′ _ |- _ =>
      dependent destruction H
  | H : _ ⊩ _ ⊢? _ <: _ ⇐′ _ ⇝′ _ |- _ =>
      dependent destruction H
  | H : _ ⊩ _ <: _ ⇒′ _ ⇝′ _ |- _ =>
      dependent destruction H
  end
.

Ltac destruct_insts := repeat destruct_inst.

Lemma busub_renaming : forall Γ1 x A Γ2 x' e1 e2 d B
   , busub (Γ1 ,' x : A ,,' Γ2) e1 e2 d B
   → x' `notin` add x (bctx_dom Γ1 `union` bctx_dom Γ2)
   → busub (Γ1 ,' x' : A ,,' (subst_bcontext `' x' x Γ2))
       ([`'x'/' x] e1) ([`'x'/' x] e2) d ([`'x'/' x] B).
Proof.
Admitted.

Corollary busub_renaming_cons : forall Γ x A x' e1 e2 d B
  , busub (Γ ,' x  : A) e1 e2 d B
  → x' `notin` add x (bctx_dom Γ)
  → busub (Γ ,' x' : A)
      ([`'x'/' x] e1) ([`'x'/' x] e2) d ([`'x'/' x] B).
Proof.
  intros.
  replace (Γ ,' x' : A) with
    (Γ ,' x' : A ,,' (subst_bcontext `' x' x bctx_nil)) in * by auto.
  apply busub_renaming; simpl; auto.
Qed.


Theorem wl_sound : forall Γ',
    ⪧′ Γ' → exists Γ Θ, nil ⊩ Γ' ⟿ Γ ⫣ Θ ∧ ⪧ Γ.
Proof.
  intros * H.
  induction H; intros.
  (* nil *)
  - eauto.
  (* var *)
  - admit.
  (* num *)
  - destruct IHwl_step as (Γ0 & Θ & Inst & DeclSolve).
    destruct_insts. dependent destruction H0.
    exists (Γ0 ⊨ be_num n ⇒ c0), Θ; split.
    + eauto 8.
    + inversion DeclSolve; subst.
      apply dst_infer with (A := be_int).
      * eapply solve_wf in DeclSolve. simpl in DeclSolve. auto.
      * auto.
  (* int *)
  - admit.
  (* star *)
  - admit.
  (* star check *)
  - admit.
  (* bot check *)
  - admit.
  (* app *)
  - admit.
  (* lambda check *)
  - admit.
  (* pi *)
  - repeat (inst_cofinites_by' gather_atoms_transfer).
    destruct H0 as (Γ0 & Θ & Inst & Solve).
    destruct_insts.
    conclude_dets.
    exists (Γ0 ⊨ be_pi e3 (e2 \`' x) <: be_pi e0 (e7 \`' x) ⇒ c0), Θ'. split.
    + constructor; [> assumption | ..].
      constructor; [> .. | eauto with ss_strengthen].
      * pick fresh x' and apply inste_pi;
          [> eauto with ss_strengthen | ..].
        rewrite <- subst_bexpr_spec.
        eapply inst_e_rename with (x := x) (x' := x') in H9.
        erewrite <- subst_aexpr_intro in H9.
        eapply inst_e_strengthening_k_cons.
        -- eassumption.
        -- eauto 2 using fkv_aexpr_open_aexpr_notin.
        -- auto.
        -- simpl. eauto 3 with ss_dom.
      * (* basically the same case as above, need optimization *)
        pick fresh x' and apply inste_pi;
          [> eauto with ss_strengthen | ..].
        rewrite <- subst_bexpr_spec.
        eapply inst_e_rename with (x := x) (x' := x') in H7.
        erewrite <- subst_aexpr_intro in H7.
        eapply inst_e_strengthening_k_cons.
        -- eassumption.
        -- eauto 2 using fkv_aexpr_open_aexpr_notin.
        -- auto.
        -- simpl. eauto 3 with ss_dom.
    + eapply dst_infer with (A := ⧼k1⧽').
      * pick fresh x' excluding (add x (bctx_dom ⌊ Γ0 ⌋)) and apply bs_pi .
        -- apply solve_uncons in Solve.
           apply solve_check_check in Solve. simpl in Solve.
           eassumption.
        -- apply solve_check_check in Solve. simpl in Solve.
           assumption.
        -- do 3 apply solve_uncons in Solve.
           apply solve_check_check in Solve. simpl in Solve.
           apply busub_renaming_cons with (x' := x') in Solve; auto.
           simpl in Solve.
           rewrite <- subst_bexpr_spec. assumption.
        -- do 2 apply solve_uncons in Solve.
           apply solve_check_check in Solve. simpl in Solve.
           apply busub_renaming_cons with (x' := x') in Solve; auto.
           simpl in Solve.
           repeat rewrite <- subst_bexpr_spec. assumption.
      * eauto using solve_uncons.
  (* bind check *)
  - admit.
  (* forall L *)
  - admit.
  (* forall R *)
  - admit.
  (* forall LR *)
  - admit.
  (* castdn *)
  - admit.
  (* castup *)
  - admit.
  (* anno *)
  - admit.
  (* ex infer *)
  - destruct IHwl_step as (Γ0 & Θ & Inst & Solve).
    dependent destruction Inst.
    dependent destruction H1.
    exists Γ0, Θ. admit.
  (* ex inst l *)
  -  destruct IHwl_step as (Γ0 & Θ & Inst & Solve).
     destruct_insts.
    admit.
  (* ex inst r *)
  - admit.
  (* app infer rec *)
  - admit.
  (* app infer base *)
  - admit.
  (* app infer ex *)
  - admit.
  (* gen-red base *)
  - admit.
  (* gen-red rec *)
  - admit.
  (* kind-ex *)
  - admit.
  - admit.
  - admit.
  - admit.
  (* check *)
  - admit.
  (* compatible *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  (* var binding *)
  - admit.
  (* ex binding *)
  - admit.
  (* kex binding *)
  - admit.
Admitted.
