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


Lemma open_subst_eq : forall e x v, 
  x `notin` fv_expr e -> lc_expr v  ->
    e ^^ v = [v /_ x] e ^^ `x.
Proof.
  intros.  
  rewrite subst_expr_open_expr_wrt_expr. simpl.
  rewrite eq_dec_refl.
  rewrite subst_expr_fresh_eq.
  all : auto.
Qed. 

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
Proof.
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
    apply (IHusub1 _ _ (eq_refl (e_all A B)) (eq_refl (e_all A B)) H0). 
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
    + subst. exists k.  
      replace (G, x0 : A0) with (G,, (ctx_nil, x0 : A0),, ctx_nil) by auto.
      eapply weakening; simpl; eauto.
    + destruct (IHWf H2) as [k0 IH]. exists k0.
      replace (G, x0 : A0) with (G,, (ctx_nil, x0 : A0),, ctx_nil) by auto.
      eapply weakening; simpl; eauto.
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
  - destruct k2; eauto. right. exists k_box. eauto with tc.
  - destruct IHHsub2 as [Hk | [k Hk]]. 
    inversion Hk. dependent induction Hk.
    + inst_cofinites_by (L `union` fv_expr B). right. exists k. eapply eall_open_mono; eauto.
    + eapply IHHk1; eauto.
      eapply kind_sub_inversion_l in Hk2; intuition; eauto.
Qed.



