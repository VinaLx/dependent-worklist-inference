Require Import Program.Tactics.
Require Export Program.Equality.

Require Export decl.ln_extra.
Require Import ln_utils.


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

  
Lemma usub_context_is_wf : forall Γ e1 e2 A,
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


Lemma wf_context_split : forall Γ1 Γ2,
  ⊢ Γ1,,Γ2 -> ⊢ Γ1.
Proof.
  induction Γ2; intros.
  - auto.
  - dependent destruction H. auto.
Qed.

Lemma weakening_auto_helper : forall Γ1 Γ2 x A,
    ⊢ Γ1 ,, Γ2 , x : A -> ⊢ Γ1 ,, (Γ2 , x : A).
Proof.
  auto.
Qed.


Lemma wf_lc : forall Γ,
  ⊢ Γ -> lc_context Γ.
Proof.
  intros. 
  pattern Γ, H.
  apply wf_mut with
    (P0:= fun Γ e1 e2 A (_ : Γ ⊢ e1 <: e2 : A) => lc_expr e1 /\ lc_expr e2 /\ lc_expr A); intros; destruct_conjs;
  try solve [constructor; auto | repeat (split; constructor)].
  - induction i.
    + split. constructor. auto.
    + apply IHi. inversion w. auto. inversion H0. auto.
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
  - repeat split; eauto. dependent destruction H3. apply lc_body_expr_wrt_expr; auto. 
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
Qed.


Lemma usub_all_lc : forall Γ e1 e2 A,
  usub Γ e1 e2 A -> lc_context Γ /\ lc_expr e1 /\ lc_expr e2 /\ lc_expr A.
Proof.
  intros.
  pattern Γ, e1, e2, A, H.
  eapply usub_mut with (
    P0 := fun Γ (_ : ⊢ Γ) => lc_context Γ
  ); intros; destruct_conjs; try solve [constructor; auto | repeat (split; constructor)].
  - dependent induction i; intuition.
    + dependent destruction w. dependent destruction H2. intuition.
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
  - intuition. dependent destruction H4. apply lc_body_expr_wrt_expr; auto.
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
  - destruct_conjs; repeat split; auto; solve_lc_expr. 
Qed.

Hint Resolve refl_l : weakening.
Hint Resolve weakening_auto_helper : weakening.

Lemma lc_app : forall Γ1 Γ2, 
  lc_context Γ1 -> lc_context Γ2 -> lc_context (Γ1,,Γ2).
Proof.
  induction Γ2; intros.
  - auto.
  - simpl. inversion H0. constructor; auto.
Qed.

Lemma lc_split_r : forall Γ1 Γ2, 
  lc_context (Γ1,,Γ2) -> lc_context Γ2.
Proof.
  induction Γ2; intros.
  - auto.
  - inversion H. constructor; auto.
Qed.

Lemma lc_split_l : forall Γ1 Γ2, 
  lc_context (Γ1,,Γ2) -> lc_context Γ1.
Proof.
  induction Γ2; intros.
  - auto.
  - inversion H. auto.
Qed.

Lemma lc_split : forall Γ1 Γ2, 
  lc_context (Γ1,,Γ2) -> lc_context Γ1 /\ lc_context Γ2.
Proof.
  split. 
  - now apply lc_split_l in H.
  - now apply lc_split_r in H.
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
    + apply in_here. 2: auto. apply lc_split in H5.
      repeat apply lc_app. all : intuition.
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
    apply lc_split_l in H1. apply lc_split_r in H1. auto. auto.
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

Corollary weakening_cons : forall Γ x B e1 e2 A,
    Γ ⊢ e1 <: e2 : A ->
    ⊢ Γ , x : B ->
    Γ , x : B ⊢ e1 <: e2 : A.
Proof.
  intros. replace (Γ , x : B) with (Γ ,, (ctx_nil, x : B) ,, ctx_nil) by reflexivity.
  now apply weakening.
Qed.

Lemma ctx_equiv : forall Γ1 Γ2 x A B,
  ctx_dom (Γ1, x : A,, Γ2) = ctx_dom (Γ1, x : B,, Γ2).
Proof.
  intros.
  induction Γ2.
  - auto.
  - simpl. rewrite IHΓ2. auto.
Qed.

Lemma binds_insert : forall Γ1 x (A : expr) Γ2,
   lc_context Γ1 -> lc_context Γ2 -> lc_expr A -> x :_ A ∈ Γ1 , x : A ,, Γ2.
Proof.
  induction Γ2; simpl; intros.
  - auto.   
  - inversion H0. constructor; auto. 
Qed.


Lemma binds_in_dom : forall Γ x A,
    x :_ A ∈ Γ -> x `in` ctx_dom Γ.
Proof.
  intros. induction Γ.
  - inversion H.
  - inversion H; simpl; auto.
Qed.

Lemma in_dom_insert : forall x Γ1 Γ2 (A : expr),
    x `in` ctx_dom (Γ1 , x : A ,, Γ2).
Proof.
  induction Γ2; intros; simpl; auto.
Qed.

Lemma binds_type_equal : forall Γ1 x A B Γ2,
    x :_ A ∈ Γ1 , x : B ,, Γ2 ->
    ⊢ Γ1 , x : B ,, Γ2 ->
    A = B.
Proof.
  unfold binds. intros. induction Γ2. simpl in *.
  - inversion H.
    + auto.
    + inversion H0. subst.
      apply binds_in_dom in H7. contradiction.
  - inversion H.
    + subst. inversion H0. 
      assert (x0 `in` ctx_dom (Γ1 , x0 : B ,, Γ2))
        by apply in_dom_insert. contradiction.
    + inversion H0; auto.
Qed.

Lemma binds_type_not_equal : forall Γ1 x x' (A : expr) B C Γ2,
    x :_ A ∈ Γ1 , x' : B ,, Γ2 ->
    x' <> x ->
    lc_expr C ->
    x :_ A ∈ Γ1 , x' : C ,, Γ2.
Proof.
  intros.
  induction Γ2.
  - inversion H. 
    + subst. contradiction.
    + econstructor; auto.
  - inversion H.
    + simpl. econstructor. 
      * apply lc_split in H6. destruct H6. inversion H6. 
        apply lc_app; auto.
      * auto. 
    + simpl. constructor; auto.
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
    + subst. assert (A0=B) by now eapply binds_type_equal; eauto. subst. eapply s_sub with (A:=A).
      * apply s_var; auto. apply usub_all_lc in Hsub. apply wf_lc in w. apply lc_split_r in w. eapply binds_insert; intuition.
      * replace (Γ1, x0 : A,, Γ2) with (Γ1, x0 : A,, Γ2,,ctx_nil) by auto. eapply weakening; simpl; eauto.
        eapply weakening_cons; eauto.
        specialize (H Γ2 (eq_refl _)). apply wf_context_split in H. auto.
    + constructor.
      * now eapply H.
      * eapply binds_type_not_equal; eauto.
        now apply usub_all_lc in Hsub.
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
Qed.

Corollary narrowing_cons : forall Γ x A B e1 e2 C k
  , Γ, x : B ⊢ e1 <: e2 : C -> Γ ⊢ A <: B : ⧼k⧽
  -> Γ, x : A  ⊢ e1 <: e2 : C.
Proof.
  intros.
  replace (Γ, x : A) with (Γ , x : A ,, ctx_nil);
    eauto using narrowing.
Qed.

Hint Resolve notin_fv_open_var : fr.

Ltac solve_eq := 
  repeat
    match goal with 
    | H : eq ?e ?e -> _ |- _ => specialize (H (eq_refl e))
    end.

Lemma fresh_ctx_fresh_expr : forall Γ a A x,
    Γ ⊢ a : A -> x `notin` ctx_dom Γ -> x `notin` fv_expr a.
Proof.
  intros. generalize dependent x.
  dependent induction H; intros; auto 3; simpl; 
  try (inst_cofinites_with_new; solve_eq; inst_cofinites_with x; eauto with fr).
  - induction G.
    + inversion H0.
    + dependent destruction H0; simpl in H2.
      * auto.
      * dependent destruction H; auto.
Qed.

Lemma fresh_binded : forall Γ1 x A Γ2,
    ⊢ Γ1 , x : A ,, Γ2 -> x `notin` fv_expr A.
Proof.
  induction Γ2; simpl; intros.
  - inversion H. subst. eapply fresh_ctx_fresh_expr; eauto.
  - apply IHΓ2. now inversion H.
Qed.

Lemma notin_dom_bind_fresh : forall Γ x A x',
    x' `notin` ctx_dom Γ -> x :_ A ∈ Γ -> ⊢ Γ -> x' `notin` fv_expr A.
Proof.
  induction Γ; simpl; intros.
  - inversion H0.
  - dependent destruction H1. dependent destruction H0.
    + eapply fresh_ctx_fresh_expr; eauto. 
    + eauto. 
Qed.


Lemma reduction_subst : forall e1 e2 x v,
  lc_expr v → e1 ⟶ e2 → [v /_ x] e1 ⟶ [v /_ x] e2.
Proof.
  intros. induction H0.
  - simpl. constructor. apply subst_expr_lc_expr; auto. auto.
  - simpl. replace ([v /_ x] e1 ^^ e2) with (([v /_ x] e1) ^^ ([v /_ x]e2)).
    + constructor. apply subst_expr_lc_expr; auto. admit. admit. apply subst_expr_lc_expr; auto.
    + apply eq_sym. apply subst_expr_open_expr_wrt_expr. auto.
  - simpl. replace ([v /_ x] e1 ^^ e) with (([v /_ x] e1) ^^ ([v /_ x]e)). eapply r_inst;  admit. admit.
  - simpl. eauto.
  - simpl. replace ([v /_ x] e1 ^^ e) with (([v /_ x] e1) ^^ ([v /_ x]e)). eapply r_cast_inst; admit. admit.
  - simpl. constructor; apply subst_expr_lc_expr; auto.
Admitted.


Lemma binds_subst : forall Γ1 Γ2 x x' A B e,
  ⊢ Γ1, x' : B,, Γ2 ->
  x :_ A ∈ Γ1, x' : B,, Γ2 -> x <> x' -> lc_expr e -> x :_ [e /_ x'] A ∈ Γ1 ,, ⟦ e /_ x'⟧  Γ2.
Proof.
  induction Γ2; simpl; intros.
  - dependent destruction H. inversion H2; subst.
    + contradiction.
    + assert (x' `notin` fv_expr A) by (eapply notin_dom_bind_fresh; eauto).
      rewrite subst_expr_fresh_eq; auto.
  - dependent destruction H. dependent destruction H2.
    + constructor. eauto. 
      apply lc_split in H2. destruct_conjs. inversion H2.
      apply lc_app; eauto. eapply subst_context_lc_context; auto. 
      apply subst_expr_lc_expr; auto.
    + econstructor. apply subst_expr_lc_expr; auto. eauto.
Qed.

Hint Resolve binds_subst : subst_.

Ltac subst_rewrite := 
  match goal with 
  | _ : _ |- (?Γ1,, ⟦ ?v /_ ?x ⟧ ?Γ2, ?x' : [?v /_ ?x] ?A) ⊢ _ _ : _ => replace (Γ1,, ⟦ v /_ x ⟧ Γ2, x' : [v /_ x] A ) with (Γ1,, ⟦ v /_ x ⟧ (Γ2, x' : A) ) by auto
  | _ : _ |- usub _ (open_expr_wrt_expr (subst_expr ?v1 ?x ?B1) (e_var_f ?x0)) _ _ => 
    replace (open_expr_wrt_expr (subst_expr v1 x B1) (e_var_f x0)) with  (open_expr_wrt_expr (subst_expr v1 x B1) (subst_expr v1 x (e_var_f x0)))
  | _ : _ |- usub _ _ (open_expr_wrt_expr (subst_expr ?v1 ?x ?B1) (e_var_f ?x0)) _ => 
  replace (open_expr_wrt_expr (subst_expr v1 x B1) (e_var_f x0)) with  (open_expr_wrt_expr (subst_expr v1 x B1) (subst_expr v1 x (e_var_f x0)))
  (* | _ : _ |- usub _ _ (open_expr_wrt_expr (subst_expr ?v1 ?x ?B1) (e_var_f ?x0)) _ => assert (1 = 1) *)
  end.

(* Theorem equiv_subst : forall Γ1 Γ2 x A e1 e2 B
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
    + subst. assert (A0=A) by now eapply binds_type_equal; eauto. subst.
      assert (x `notin` fv_expr A) by (eapply fresh_binded; eauto). 
      replace ([v1 /_ x] A) with A by (apply eq_sym; apply subst_expr_fresh_eq; eauto). 
      replace (Γ1,, ⟦ v1 /_ x ⟧ Γ2) with (Γ1,, ⟦ v1 /_ x ⟧ Γ2,, ctx_nil) by auto; split; apply weakening; simpl; eauto.
    + assert (lc_expr v1 /\ lc_expr v2) by (apply usub_all_lc in H1; intuition). destruct_conjs. 
      split; eauto with subst_. 
  - eauto 6.
  - eauto 6.
  - eauto 6.
  - split.
    + eapply s_bot with (k:=k); destruct k; simpl in *; try eapply H0; eauto; try eapply H1; eauto. 
    + eapply s_sub with (A := [v1 /_ x] A2) (k:=k). eapply s_sub with (A := [v2 /_ x] A1) (k:=k).
      eapply s_bot with (k:=k); destruct k; simpl in *; try eapply H0; eauto; try eapply H1; eauto.
      * destruct k; simpl in *; eapply H0; eauto.
      * apply refl_l in H2. destruct k; simpl in *; eapply H1; eauto.
  - split.
    + eapply s_abs with (k1:=k1) (k2:=k2) (L:=L `union` singleton x).
      destruct k1; simpl in *; eapply H0; eauto.
      destruct k2; simpl in *; eapply H1; eauto.
      all : intros; inst_cofinites_with x0; destruct k2; simpl in *.
      (* * subst_rewrite. subst_rewrite. subst_rewrite. *)
       replace (([v1 /_ x] B1) ^^ ` x0) with ([v1 /_ x] B1 ^^ ` x0). admit. rewrite subst_expr_open_expr_wrt_expr. simpl.
       unfold eq_dec. destruct (EqDec_eq_of_X x0 x).  
       ([v1 /_ x] B1) ^^ ` ([v1 /_ x] / x0) 
        replace (([v2 /_ x] B2) ^^ ` x0) with ([v2 /_ x] B2 ^^ ` x0) by admit.
        replace (Γ1,, ⟦ v1 /_ x ⟧ Γ2, x0 : [v1 /_ x] A1 ) with (Γ1,, ⟦ v1 /_ x ⟧ (Γ2, x0 : A1) ) by auto.
        eapply H2; eauto.
      all : admit.
      *  admit. * admit. * admit. *  admit. * admit. * admit. *  admit. * admit. * admit. 
    + apply s_sub with (e_pi ([v1 /_ x] A2) ([v2 /_ x] B1)) k2.
      apply s_sub with (e_pi ([v2 /_ x] A1) ([v2 /_ x] B1)) k2.
      eapply s_abs with (L:=L `union` singleton x) (k1:=k1) (k2:=k2). eapply H0; eauto. eapply H1; eauto. 
      admit. admit. admit. admit. admit.
      * econstructor; admit.
      * econstructor.
Admitted. *)


Theorem refl_r : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> Γ ⊢ e2 : A.
Proof.
  intros. induction H; eauto 3.
  - eapply s_sub with (e_pi A2 B2) k2.
    + pick fresh x and apply s_abs; eauto using narrowing_cons.
    + pick fresh x and apply s_pi; eauto.
  - pose proof H4 as H5.
    pick fresh x; specialize (H5 x Fr);
      apply usub_context_is_wf in H5; inversion H5; subst; eauto.
  (* app, need equiv apply *)
  - eapply s_sub with (e_all A2 B2) k_star.
    + pick fresh x and apply s_bind; eauto using narrowing_cons.
    + pick fresh x and apply s_forall; eauto using narrowing_cons.
  - pick fresh x and apply s_forall; eauto using narrowing_cons.
Qed.

Lemma box_never_welltype : forall Γ A,
    ~ (Γ ⊢ ◻ : A).
Proof.
  intros. intro.
  dependent induction H; auto.
Qed.

Lemma star_type_inversion : forall Γ A,
    Γ ⊢ ⋆ : A -> A = ◻.
Proof.
  intros.
  dependent induction H.
  - auto.
  - assert (A = ◻) by auto. subst.
    apply refl_l in H0. apply box_never_welltype in H0. contradiction.
Qed.

Lemma star_type_inversion_l : forall Γ A B,
    Γ ⊢ A <: ⋆ : B -> B = ◻.
Proof.
  intros.
  apply star_type_inversion with Γ.
  now apply refl_r with A.
Qed.

Lemma star_type_inversion_r : forall Γ A B,
    Γ ⊢ ⋆ <: A : B -> B = ◻.
Proof.
  intros.
  apply star_type_inversion with Γ.
  now apply refl_l with A.
Qed.

Lemma star_sub_inversion_l : forall Γ A B,
    Γ ⊢ A <: ⋆ : B -> A = ⋆.
Proof.
  intros.
  dependent induction H; auto.
  - apply star_type_inversion_l in H2. discriminate.
Qed.


Lemma kind_sub_inversion_l : forall Γ ek kr k,
    Γ ⊢ ek <: e_kind kr : k -> ek = ⋆ /\ kr = k_star /\ k = ◻.
Proof.
  intros.
  dependent induction H.
  - auto.
  - edestruct IHusub3. reflexivity. destruct H6. discriminate.
  - edestruct IHusub1 as [E1 [E2 E3]]; auto.
    subst.
    apply refl_l in H0. now apply box_never_welltype in H0.
Qed.

Lemma not_eall_box : forall Γ B,
    ~ (Γ ⊢ e_all ◻ B : ⋆).
Proof.
  intros. intro.
  dependent induction H; auto.
  + apply box_never_welltype in H0. contradiction.
  + apply box_never_welltype in H. contradiction.
  + apply box_never_welltype in H. contradiction.
  + apply star_sub_inversion_l in H0. eauto.
Qed.


Lemma eall_open_var : forall Γ A B,
  Γ ⊢ e_all A B : ⋆ -> exists L, (forall x, x `notin` L -> Γ, x : A ⊢ B ^^ `x : ⋆ ).
Proof.
  intros.
  dependent induction H.
  - exists L. eauto. 
  - exists L. intros. specialize (H1 x H3). apply refl_r in H1. auto.
  - exists L. eauto.
  - eapply star_sub_inversion_l in H0. 
    apply (IHusub1 _ _ (eq_refl _) (eq_refl _) H0). 
Qed.


Theorem substitution : forall Γ1 Γ2 x A B e1 e2 e3,
  Γ1 , x : B ,, Γ2 ⊢ e1 <: e2 : A ->
  Γ1 ⊢ e3 : B -> mono_type e3 ->
  Γ1 ,, ⟦ e3 /_ x ⟧ Γ2 ⊢ [e3 /_ x] e1 <: [e3 /_ x] e2 : [e3 /_ x] A.
Proof.
Admitted.

Corollary substitution_cons : forall Γ x A B e1 e2 e3,
    Γ, x : B ⊢ e1 <: e2 : A ->
    Γ ⊢ e3 : B -> mono_type e3 ->
    Γ ⊢ [e3 /_ x] e1 <: [e3 /_ x] e2 : [e3 /_ x] A.
Proof.
  intros *.
  replace (Γ, x : B) with (Γ,, (ctx_nil, x:B),, ctx_nil) by auto.
  intros.
  replace Γ with (Γ,, ⟦ e3 /_ x ⟧ ctx_nil) by auto.
  eapply substitution; eauto.
Qed.

Lemma eall_open_mono : forall Γ x A B t k,
  Γ, x : A ⊢ B ^^ ` x : ⧼ k ⧽ -> x `notin` fv_expr B -> Γ ⊢ t : A -> mono_type t -> Γ ⊢ B ^^ t : ⧼ k ⧽.
Proof.
  intros.
  specialize (substitution_cons _ _ _ _ _ _ _ H H1 H2).
  simpl. intros.
  apply monotype_lc in H2.
  specialize (open_subst_eq _ _ _ H0 H2). intros.
  rewrite <- H4 in H3. destruct k; auto.
Qed.

Lemma ctx_type_correct : forall Γ x A,
    ⊢ Γ -> x :_ A ∈ Γ -> exists k, Γ ⊢ A : e_kind k.
Proof.
  intros * Wf.
  induction Wf; simpl; intros.
  - inversion H.
  - dependent destruction H1.
    + subst. exists k. eapply weakening_cons; eauto.
    + destruct (IHWf H2) as [k0 IH]. exists k0.
      eapply weakening_cons; eauto.
Qed.

Hint Resolve refl_l : tc.
Hint Resolve refl_r : tc.
Hint Resolve usub_context_is_wf : tc.

Theorem type_correctness : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> A = ◻ \/ exists k, Γ ⊢ A : e_kind k.
Proof.
  intros * Hsub.
  induction Hsub; eauto with tc.
  - eauto using ctx_type_correct.
  - right. exists k2. eauto 6 with tc.
  - destruct k2; eauto with tc. 
  - destruct IHHsub2 as [Hk | [k Hk]]. 
    inversion Hk. dependent induction Hk.
    + inst_cofinites_by (L `union` fv_expr B). right. exists k. eapply eall_open_mono; eauto.
    + eapply IHHk1; eauto.
      eapply kind_sub_inversion_l in Hk2; intuition; eauto.
Qed.