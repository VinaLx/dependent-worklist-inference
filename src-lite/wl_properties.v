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
    inversion Inst; subst.
    inversion H6; subst.
    exists (Γ1 ⊨ be_num n ⇒ c0), Θ; split.
    + now constructor.
    + econstructor. 2: eauto. admit.
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

    dependent destruction Inst.
    dependent destruction Inst.
    dependent destruction H1.
    dependent destruction H12.
    dependent destruction H12.

    dependent destruction Solve.
    all: admit.
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
