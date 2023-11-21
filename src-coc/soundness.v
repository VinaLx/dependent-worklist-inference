Require Import alg.worklist.
Require Import decl.worklist.
Require Import transfer.
Require Import ln_utils.

Require Import Program.Equality.

Tactic Notation "dd" ident(H) := dependent destruction H.

Ltac gather_all_atoms :=
  let xs := gather_atoms_with (fun x : atoms => x) in
  let x  := gather_atoms_with (fun x : atom => singleton x) in
  let ae := gather_atoms_with
              (fun e : aexpr =>
                 fv_aexpr e `union` fex_aexpr e `union` fkv_aexpr e) in
  let c  := gather_atoms_with
              (fun c : cont =>
                 fv_cont c `union` fex_cont c `union` fkv_cont c) in
  let L := beautify_fset (xs `union` x `union` ae `union` c) in
  constr:(L).

Ltac decompose_transfer :=
  match goal with
  (* wls *)
  | H : _ ⊢ _ ⊨′ _ ⟿ _ ⊣ _ |- _ => dd H
  | H : _ ⊢ _ ,′ _ ⟿ _ ⊣ _ |- _ => dd H
  (* kinds *)
  | H : _ ⊢ ak_star ~> _ |- _ => dd H
  | H : _ ⊢ ak_box  ~> _ |- _ => dd H
  | H : _ ⊢ ak_ex _ ~> _ |- _ => dd H
  (* exprs *)
  | H :  _ ⊢ `^ _ ⇝ _ |- _ => dd H
  (* works *)
  | H : _ ⊢ _ ~~ _ ⇒′ _ ⇝′ _ |- _ => dd H
  | H : _ ⊢ _ ~~ _ ⇐′ _ ⇝′ _ |- _ => dd H
  | H : _ ⊢ _ $′ _  ⇝′ _ |- _ => dd H
  (* actx *)
  | H : _ ⊢ actx_nil ⟿′′ _ |- _ => dd H
  end
.

Ltac decompose_transfers :=
  repeat decompose_transfer.

Ltac cleanup_duplication :=
  match goal with
  | H : In (⧼^?x⧽= ?k)  (_; ⧼^?x⧽= ?k)  |- _ => clear H
  | H : In (⧼^?x⧽= ?k1) (_; ⧼^?x⧽= ?k2) |- _ =>
      apply wf_il_inst_unique_consₖ in H;
      eauto with wf_il;
      subst
  | H : In (^?x :_ ?k1 = ?A1) (_; ^?x :_ ?k2 = ?A2) |- _ =>
      let Ek := fresh "Ek" in
      let Ea := fresh "Ea" in
      apply wf_il_inst_unique_consₓ in H as (Ek & Ea);
      eauto with wf_il;
      subst
  end
.

Ltac cleanup_duplications :=
  repeat cleanup_duplication.

Theorem soundness: forall Γ',
    ⪧′ Γ' → exists Γ Θ, nil ⊢ Γ' ⟿ Γ ⊣ Θ ∧ ⪧ Γ.
Proof.
  induction 1.
  1-5: admit.
  - destruct IHwl_step as (Γ0 & Θ & Trans & R).
    admit.
  - admit.
  - repeat inst_cofinites_by' gather_all_atoms.
    destruct H0 as (Γ0 & Θ & Trans & R).
    decompose_transfers.
    cleanup_duplications. simpl in *.
    exists (Γ0 ⊨ e_abs (close_expr_wrt_expr x e5) ⇒ c0), Θ2.
    split.
    + admit.
    + admit.
  (* app infer *)
  - repeat inst_cofinites_by' gather_all_atoms.
    destruct H0 as (Γ0 & Θ & Trans & R).
    decompose_transfers.
  - admit.
  (* ex insts *)
  - admit.
  - destruct IHwl_step as (Γ0 & Θ & Trans & R). admit.
  - admit.
  (* kind ex *)
  - admit.
  - admit.
  - admit.
  - admit.
  (* check *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  (* apply cont *)
  - destruct IHwl_step as (Γ0 & Θ & Trans & R).
    admit.
  (* binds *)
  - admit.
  - admit.
  - admit.
Admitted.
