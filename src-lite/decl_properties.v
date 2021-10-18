Require Export decl_notations.
Require Export Coq.Program.Equality.

Definition wf_dom : forall {Γ}, ⊢ Γ -> atoms.
Proof.
  intros.
  set (x := ctx_dom Γ). exact x.
Defined.

Ltac gather_for_weakening :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : context => ctx_dom x) in
  let D := gather_atoms_with wf_dom in
  constr:(A `union` B `union` C `union` D).

Ltac apply_fresh_base_fixed H gather_vars atom_name :=
  let L := gather_vars in
  let L := beautify_fset L in
  let x := fresh atom_name in
  pick fresh x excluding L and apply H.

Tactic Notation "pick" "fresh" ident(x) "and" "apply" constr(H) "for" "weakening" :=
  apply_fresh_base_fixed H gather_for_weakening x.

Scheme usub_mut := Induction for usub       Sort Prop
  with   wf_mut := Induction for wf_context Sort Prop.

Lemma wt_wf : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> ⊢ Γ.
Proof.
  intros; induction H; auto.
Qed.


Theorem refl_l : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> Γ ⊢ e1 : A.
Proof.
  intros. induction H; eauto 3.
Qed.

Lemma ctx_app_cons : forall Γ1 Γ2 x A,
    Γ1 ,, Γ2 , x : A = Γ1 ,, (Γ2 , x : A).
Proof.
  auto.
Qed.

Hint Rewrite ctx_app_cons : ctx.

Lemma weakening_auto_helper : forall Γ1 Γ2 x A,
    ⊢ Γ1 ,, Γ2 , x : A -> ⊢ Γ1 ,, (Γ2 , x : A).
Proof.
  auto.
Qed.

Hint Resolve refl_l : weakening.
Hint Resolve weakening_auto_helper : weakening.

Lemma in_ctx_weakening : forall Γ1 Γ2 Γ3 x A,
    in_ctx x A (Γ1 ,, Γ3) -> in_ctx x A (Γ1 ,, Γ2 ,, Γ3).
Proof.
Admitted.

Theorem weakening : forall Γ1 Γ2 Γ3 e1 e2 A,
    Γ1 ,, Γ3 ⊢ e1 <: e2 : A ->
    ⊢ Γ1 ,, Γ2 ,, Γ3 ->
    Γ1 ,, Γ2 ,, Γ3 ⊢ e1 <: e2 : A.
Proof with unfold wf_dom; autorewrite with ctx; eauto 6 with weakening.
  intros * H.
  dependent induction H; intros.
  - constructor. auto. auto using in_ctx_weakening.
  - auto.
  - auto.
  - auto.
  - eauto.
  - pick fresh x and apply s_abs for weakening...
  - pick fresh x and apply s_pi for weakening...
  - eapply s_app; eauto 3.
  - pick fresh x and apply s_bind for weakening...
  - eapply s_castup; eauto 3.
  - eapply s_castdn; eauto 3.
  - pick fresh x and apply s_forall_l for weakening...
  - pick fresh x and apply s_forall_r for weakening...
  - pick fresh x and apply s_forall for weakening...
  - eapply s_sub; eauto 3.
Qed.

Theorem narrowing : forall Γ1 Γ2 x A B e1 e2 C k,
    Γ1, x : B,, Γ2 ⊢ e1 <: e2 : C ->
    Γ1 ⊢ A <: B : e_kind k ->
    Γ1, x : A,, Γ2 ⊢ e1 <: e2 : C.
Proof with autorewrite with ctx; eauto.
  intros * Hind Hsub.
  remember (Γ1, x : B,, Γ2) as Γ.
  generalize Γ2, HeqΓ. clear HeqΓ Γ2.
  pattern Γ, e1, e2, C, Hind.
  apply usub_mut with
    (P0 := fun Γ (_ : ⊢ Γ) =>
      forall Γ2, Γ = Γ1 , x : B,, Γ2 -> ⊢ Γ1 , x : A ,, Γ2); intros; subst.
  - apply s_var.
    + auto.
    + admit.
  - auto.
  - auto.
  - auto.
  - eauto.
  - pick fresh x' and apply s_abs...
  - pick fresh x' and apply s_pi...
  - eauto.
  - pick fresh x' and apply s_bind...
  - eauto.
  - eauto.
  - pick fresh x' and apply s_forall_l...
  - pick fresh x' and apply s_forall_r...
  - pick fresh x' and apply s_forall...
  - eauto.

  - destruct Γ2; simpl in H; inversion H.
  - destruct Γ2; simpl in *; inversion H1; subst.
    + eauto using refl_l.
    + apply wf_cons with k0; auto. admit.
Admitted.

Corollary narrowing_cons : forall Γ x A B e1 e2 C k
  , Γ, x : B ⊢ e1 <: e2 : C -> Γ ⊢ A <: B : ⧼k⧽
  -> Γ, x : A  ⊢ e1 <: e2 : C.
Proof.
  intros.
  replace (Γ, x : A) with (Γ , x : A ,, ctx_nil);
    eauto using narrowing.
Qed.

Theorem refl_r : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> Γ ⊢ e2 : A.
Proof.
  intros. induction H; eauto 3.
  - eapply s_sub with (e_pi A2 B2) k2.
    + pick fresh x and apply s_abs; eauto using narrowing_cons.
    + pick fresh x and apply s_pi; eauto.
      eapply narrowing_cons; eauto.
  - pose proof H4 as H5.
    pick fresh x; specialize (H5 x Fr);
      apply wt_wf in H5; inversion H5; subst; eauto.
  (* app, need equiv apply *)
  - admit.
    (* eapply s_sub with (e_all A2 B2) k_star.
    + pick fresh x and apply s_bind; eauto using narrowing_cons.
    + pick fresh x and apply s_forall; eauto using narrowing_cons.
     *)
  - eapply s_sub with (e_all A2 B2) k_star.
    + pick fresh x and apply s_bind; eauto using narrowing_cons.
    + pick fresh x and apply s_forall; eauto using narrowing_cons.
  - pick fresh x and apply s_forall; eauto using narrowing_cons.
Admitted.
