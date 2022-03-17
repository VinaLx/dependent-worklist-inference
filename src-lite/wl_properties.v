Require Import worklist.
Require Import decl_worklist.
Require Import transfer.syntax.
Require Import transfer.properties.

Require Import decl.notations.
Require Import Equality.
Require Import ln_utils.

Lemma solve_wf : forall Γ, ⪧ Γ → ⫦ ⌊ Γ ⌋.
Proof.
  induction 1; simpl.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma solve_prefix : forall Γ1 Γ2,
    ⪧ Γ1 ⫢ Γ2 → ⪧ Γ1.
Proof.
  intros.
  dependent induction H.
  - destruct Γ1; destruct Γ2; solve [auto | inversion x].
  - admit.
Admitted.

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
    apply inst_wl_split in Inst as (Γ1 & Γ2 & Θ0 & -> & Inst1 & Inst2).
    pick fresh x for (fv_worklist c `union` fv_ss Θ).
    rewrite (subst_worklist_intro x) in Inst2; auto.
    assert (exists Θ', Θ0 ;; Θ' = Θ) as (Θ' & <-)
        by eauto using inst_wl_ss_extend.
    eapply inst_wl_rev_subst with (e := be_int) in Inst2
        as (c' & Θ'' & <- & <- & Inst2).
    exists (Γ1 ⊨ be_num n ⇒ close_dworklist_wrt_bexpr x c'). exists (Θ0 ;; Θ'') (* todo *).
    split.
    + apply instwl_cons with Θ0.
      * auto.
      * eapply instw_infer; eauto. intros.
        rewrite (subst_worklist_intro x).
        rewrite (subst_dworklist_intro x).
        apply inst_wl_rename.
        rewrite open_dworklist_wrt_bexpr_close_dworklist_wrt_bexpr. auto.
        all: admit.
    + eapply dst_infer with be_int.
      * admit.
      * now rewrite <- subst_dworklist_spec.
    + admit.
    + admit.
    + admit.
  (* int *)
  - admit.
  (* star *)
  - admit.
  (* star check *)
  - admit.
  (* bot check *)
  - admit.
  (* app *)
  - destruct IHwl_step as (Γ' & Θ & Inst & Solve).
    dependent destruction Inst.
    dependent destruction H0.
    dependent destruction Solve.

    admit.
  (* lambda check *)
  - admit.
  (* pi *)
  - inst_cofinites_with_new.
    inst_cofinites_with_new.
    inst_cofinites_with_new.
    destruct H0 as (Γ0 & Θ & Inst & Solve).
    dependent destruction Inst.
    dependent destruction Inst.
    dependent destruction Inst.
    dependent destruction Inst.
    dependent destruction H0. dependent destruction H0.
    dependent destruction H4. dependent destruction H4.
    apply inst_wl_split in Inst as (Γ1 & Γ2 & Θ' & -> & Inst1 & Inst2).
    dependent destruction Inst1.
    pick fresh x' for all.
    rewrite (subst_worklist_intro x) in Inst2.
    assert (exists Θ'0, Θ' ; x1 ≔ ⧼k0⧽ ;; Θ'0 = Θ) as (Θ'0 & <-)
        by eauto using inst_wl_ss_extend.
    eapply inst_wl_rev_subst with (e := ⧼k0⧽') in Inst2
        as (c_' & Θ'0' & <- & <- & Inst2).
    exists (Γ0 ⊨ be_pi A0 (close_bexpr_wrt_bexpr x e1) <: be_pi A4 (close_bexpr_wrt_bexpr x e0) ⇒ (close_dworklist_wrt_bexpr x c_')), nil. split.
    all: admit.
    (*
    + admit.
    + eapply dst_infer with (⧼k0⧽').
      dependent destruction H10.
      dependent destruction H10.
      assert (A5 = ⧼k0⧽') as -> by admit.
      assert (e4 = e5) as -> by admit.
      all: admit.
    *)
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
  - admit.
  (* ex inst l *)
  - admit.
  (* ex inst r *)
  - admit.
  (* app infer rec *)
  - admit.
  (* app infer base *)
  - admit.
  (* app infer ex *)
  - admit. (* todo, fix the rule *)
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
