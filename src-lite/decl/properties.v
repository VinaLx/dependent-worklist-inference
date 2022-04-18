Require Export decl.notations.
Require Import ln_utils.
Require Import Program.Tactics.
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

Scheme usub_mut := Induction for usub        Sort Prop
  with             Induction for wf_context  Sort Prop.

Scheme wf_mut   := Induction for wf_context  Sort Prop
  with             Induction for usub        Sort Prop.


Lemma monotype_lc : forall e,
    mono_type e -> lc_expr e.
Proof.
  intros. induction H; auto. 
Qed.

  
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


Ltac solve_lc_with x0 :=
  match goal with
  | _ : _ |- lc_expr (e_pi ?A ?B) => eapply lc_e_pi_exists with (x1:=x0); auto
  | _ : _ |- lc_expr (e_abs ?A ?B) => eapply lc_e_abs_exists with (x1:=x0); auto; constructor; auto
  | _ : _ |- lc_expr (e_bind ?A ?B) => eapply lc_e_bind_exists with (x1:=x0); auto; constructor; try fold open_expr_wrt_expr_rec; auto
  | _ : _ |- lc_expr (e_all ?A ?B) => eapply lc_e_all_exists with (x1:=x0); auto
  end.


Lemma wf_lc : forall Γ,
  ⊢ Γ -> lc_context Γ.
Proof.
  intros. 
  pattern Γ, H.
  apply wf_mut with
    (P0:= fun c e e0 e1 (_ : c ⊢ e <: e0 : e1) => lc_expr e /\ lc_expr e0 /\ lc_expr e1); intros; destruct_conjs;
  try solve [constructor; auto | repeat (split; constructor)].
  - induction i.
    + split. constructor. auto.
    + apply IHi. inversion w. auto. inversion H0. auto.
  - destruct_conjs. pick_fresh x0. specialize (H2 x0 Fr). specialize (H4 x0 Fr). destruct_conjs. repeat split. 
    eapply lc_e_abs_exists with (x1:=x0); auto. econstructor; fold open_expr_wrt_expr_rec; inst_cofinites_with x0; intuition.
    eapply lc_e_abs_exists with (x1:=x0); auto. econstructor; fold open_expr_wrt_expr_rec; inst_cofinites_with x0; intuition.
    eapply lc_e_pi_exists with (x1:=x0); auto. 
  - pick_fresh x0. specialize (H2 x0 Fr). specialize (H3 x0 Fr). destruct_conjs. 
    repeat split; auto; solve_lc_with x0.
  - destruct_conjs. repeat split; try  constructor; auto.
    inversion H3. apply lc_body_expr_wrt_expr. auto. auto.
  - pick_fresh x0. specialize (H2 x0 Fr). specialize (H4 x0 Fr). destruct_conjs.
    repeat split.
    eapply lc_e_bind_exists with (x1:=x0); auto. econstructor; fold open_expr_wrt_expr_rec; inst_cofinites_with x0; intuition.
    eapply lc_e_bind_exists with (x1:=x0); auto. econstructor; fold open_expr_wrt_expr_rec; inst_cofinites_with x0; intuition.
    eapply lc_e_all_exists with (x1:=x0); auto. 
  - destruct_conjs. repeat split; auto. pick_fresh x0. specialize (H3 x0 Fr). destruct_conjs.
    solve_lc_with x0.
  - destruct_conjs. repeat split; auto. pick_fresh x0. specialize (H2 x0 Fr). destruct_conjs.
    solve_lc_with x0.
  - pick fresh x0. specialize (H2 x0 Fr); destruct_conjs. repeat split; auto; solve_lc_with x0.
Qed.

Theorem usub_context_is_wf : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> ⊢ Γ.
Proof.
  intros.
  induction H; auto.
Qed.


Hint Resolve refl_l : weakening.
Hint Resolve weakening_auto_helper : weakening.


Lemma lc_insert_middle : forall Γ1 Γ2 Γ3,
    lc_context Γ2 -> lc_context (Γ1,,Γ3) -> lc_context (Γ1,,Γ2,,Γ3).
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

Lemma lc_middle : forall Γ1 Γ2 Γ3,
    lc_context (Γ1,,Γ2,,Γ3) -> lc_context Γ2.
Proof.
  intros.
  induction Γ3.
  - induction Γ2; simpl in *. auto.
    inversion H. constructor; auto.
  - inversion H. auto.
Qed.
  

Lemma in_ctx_weakening : forall Γ1 Γ2 Γ3 x A,
    lc_context Γ2 -> in_ctx x A (Γ1 ,, Γ3) -> in_ctx x A (Γ1 ,, Γ2 ,, Γ3).
Proof.
  intros.
  induction Γ3.
  - induction Γ2.
    + auto.
    + inversion H. simpl in *. econstructor; auto.
  - simpl in *. inversion H0. subst.
    + apply in_here. 2: auto. apply lc_insert_middle; auto.
    + apply in_there. auto. apply IHΓ3. auto.
Qed.

Theorem weakening : forall Γ1 Γ2 Γ3 e1 e2 A,
    Γ1 ,, Γ3 ⊢ e1 <: e2 : A ->
    ⊢ Γ1 ,, Γ2 ,, Γ3 ->
    Γ1 ,, Γ2 ,, Γ3 ⊢ e1 <: e2 : A.
Proof with unfold wf_dom; autorewrite with ctx; eauto 6 with weakening.
  intros * H.
  dependent induction H; intros.
  - constructor. auto. apply in_ctx_weakening. apply wf_lc in H1.
    apply lc_middle in H1. auto. auto.
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

Lemma ctx_equiv : forall Γ1 Γ2 x A B,
  ctx_dom (Γ1, x : A,, Γ2) = ctx_dom (Γ1, x : B,, Γ2).
intros.
  induction Γ2.
  - auto.
  - simpl. rewrite IHΓ2. auto.
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
             forall Γ2, Γ = Γ1 , x : B,, Γ2 -> ⊢ Γ1 , x : A ,, Γ2);
    intros; subst.
  - destruct (x==x0). 
    + subst. assert (A0=B) by admit. subst. eapply s_sub with (A:=A).
      * apply s_var; auto. admit.
      * replace (Γ1, x0 : A,, Γ2) with (Γ1,,((ctx_nil,x0 : A),,Γ2),,ctx_nil). eapply weakening.
        simpl. eauto.
        simpl. admit. admit.
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
    + apply wf_cons with k0; auto. rewrite (ctx_equiv Γ1 Γ2 x A B). auto.
Admitted.

Corollary narrowing_cons : forall Γ x A B e1 e2 C k
  , Γ, x : B ⊢ e1 <: e2 : C -> Γ ⊢ A <: B : ⧼k⧽
  -> Γ, x : A  ⊢ e1 <: e2 : C.
Proof.
  intros.
  replace (Γ, x : A) with (Γ , x : A ,, ctx_nil);
    eauto using narrowing.
Qed.

Lemma reduction_subst : forall e1 e2 x v,
  lc_expr v → e1 ⟶ e2 → [v /_ x] e1 ⟶ [v /_ x] e2.
Proof.
  intros. induction H0.
  - simpl. constructor. admit. auto.
  - simpl. replace ([v /_ x] e1 ^^ e2) with (([v /_ x] e1) ^^ ([v /_ x]e2));
     [> constructor; admit| admit].
  - admit.
  - simpl. eauto.
  - admit.
  - simpl. constructor; admit.
Admitted.

Theorem equiv_subst : forall Γ1 Γ2 x A e1 e2 B
  , Γ1 , x : A ,, Γ2 ⊢ e1 <: e2 : B → forall v1 v2
  , Γ1 ⊢ v1 <: v2 : A → Γ1 ⊢ v2 <: v1 : A
  → Γ1 ,, ⟦v1 /_ x⟧ Γ2 ⊢ [v1 /_ x] e1 <: [v2 /_ x] e2 : [v1 /_ x] B
  ∧ Γ1 ,, ⟦v1 /_ x⟧ Γ2 ⊢ [v2 /_ x] e1 <: [v1 /_ x] e2 : [v1 /_ x] B.
Proof.
  intros * H.
  remember (Γ1, x : A,, Γ2) as Γ.
  generalize dependent Γ2.
  pattern Γ, e1, e2, B, H.
  apply usub_mut with
    (P0 := fun c wf => forall Γ2 v1 v2, c = Γ1 , x : A ,, Γ2
      → Γ1 ⊢ v1 <: v2 : A → Γ1 ⊢ v2 <: v1 : A → ⊢ Γ1 ,, ⟦v1 /_ x⟧ Γ2);
    intros; subst; simpl.
  - destruct (x0 == x).
    + admit.
    + admit.
  - eauto 6.
  - eauto 6.
  - eauto 6.
  - split.
    + admit.
    + admit.
  - split.
    + pick fresh x' and apply s_abs; admit.
    + apply s_sub with (e_pi ([v2 /_ x] A1) ([v1 /_ x] B1)) k2.
      admit.
      * econstructor.

Admitted.


Theorem refl_r : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> Γ ⊢ e2 : A.
Proof.
  intros. induction H; eauto 3.
  - eapply s_sub with (e_pi A2 B2) k2.
    + pick fresh x and apply s_abs; eauto using narrowing_cons.
    + pick fresh x and apply s_pi; eauto.
  - pose proof H4 as H5.
    pick fresh x; specialize (H5 x Fr);
      apply wt_wf in H5; inversion H5; subst; eauto.
  (* app, need equiv apply *)
  - eapply s_sub with (e_all A2 B2) k_star.
    + pick fresh x and apply s_bind; eauto using narrowing_cons.
    + pick fresh x and apply s_forall; eauto using narrowing_cons.
  - pick fresh x and apply s_forall; eauto using narrowing_cons.
Qed.


Lemma star_sub_inversion_l : forall Γ A B,
    Γ ⊢ A <: ⋆ : B -> A = ⋆.
Admitted.

Theorem type_correctness : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> A = ◻ \/ exists k, Γ ⊢ A : e_kind k.
Admitted.

Lemma box_never_welltype : forall Γ A,
    ~ (Γ ⊢ ◻ : A).
Proof.
  intros. intro.
  dependent induction H; auto.
Qed.

Lemma not_eall_box : forall Γ B,
    ~ (Γ ⊢ e_all ◻ B : ⋆).
Proof.
  intros. intro.
  dependent induction H; auto.
  + apply box_never_welltype in H0. contradiction.
  + apply box_never_welltype in H. contradiction.
  + apply box_never_welltype in H. contradiction.
  + apply star_sub_inversion_l in H0.
    eauto.
Qed.


Corollary substitution_cons : forall Γ x A B e1 e2 e3,
    Γ, x : B ⊢ e1 <: e2 : A ->
    Γ ⊢ e3 : B -> mono_type e3 ->
    Γ ⊢ [e3 /_ x] e1 <: [e3 /_ x] e2 : [e3 /_ x] A.
Admitted.

