Require Import Program.Tactics.
Require Import Metalib.FSetWeakNotin.

Require Import decl.properties.
Require Import bidir.notations.
Require Import bidir.properties.
Require Import bidir.elaboration.
Require Import ln_utils.


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
       (mono_type e1 /\ mono_type e2 -> mono_btype e1' /\ mono_btype e2') /\ lc_bexpr e1' /\ lc_bexpr e2'.
Proof.
  intros.
  induction H; repeat split; destruct_conjs; intros; auto 4; try solve_trivial_mono; try solve_lc_bexpr.
  - destruct_mono. eapply bmono_lambda with (L:=L `union` (L0 `union` L1)). intuition. solve_lc_bexpr.
    intros. inst_cofinites_with x. intuition.
  - destruct_mono. eapply bmono_lambda with (L:=L `union` (L0 `union` L1)). intuition. solve_lc_bexpr.
    intros. inst_cofinites_with x. intuition.
  - destruct_mono. eapply bmono_pi with (L:=L `union` (L0 `union` L1)). intuition.
    intros. inst_cofinites_with x. intuition.
  - destruct_mono. eapply bmono_pi with (L:=L `union` (L0 `union` L1)). intuition.
    intros. inst_cofinites_with x. intuition.
  - destruct_mono. eapply bmono_bind with (L:=L `union` (L0 `union` L1)). intuition. solve_lc_bexpr.
    intros. inst_cofinites_with x. intuition.
  - destruct_mono. eapply bmono_bind with (L:=L `union` (L0 `union` L1)). intuition. solve_lc_bexpr.
    intros. inst_cofinites_with x. intuition.
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
  - generalize dependent n0. generalize dependent H0. pattern e.
    eapply bexpr_mut with
    (P0 := fun b =>
      match b with
      | bb_anno e A => forall n0,
          x `notin` ott.fv_eexpr (berase e) ->
          x `notin` ott.fv_eexpr (berase (open_bexpr_wrt_bexpr_rec n0 `'x' e))
      end
    ); intros; auto; try (simpl in *; auto; fail).
    + simpl. destruct (lt_eq_lt_dec n n0); simpl.
      * destruct s; simpl; auto.
      * auto.
    + destruct b; simpl in *; auto.
    + destruct b; simpl in *; auto.
  - generalize dependent n0. pattern e.
    eapply bexpr_mut with
    (P0 := fun b =>
      match b with
      | bb_anno e A => forall n0,
          x `notin` ott.fv_eexpr (berase (open_bexpr_wrt_bexpr_rec n0 `'x' e)) ->
          x `notin` ott.fv_eexpr (berase e)
      end
    ); intros; auto; try (simpl in *; eauto; fail).
    + destruct b; simpl in *. eauto.
    + destruct b; simpl in *. eauto.
Qed.

Ltac convert_to_open_expr_wrt_new_var :=
  match goal with
  | H : ?x `notin` ott.fv_eexpr (erase ?e) |- ?x `notin` ott.fv_eexpr (berase ?e') =>
      match goal with
      | H1 : ?x `notin` ott.fv_eexpr (erase (?e ^^ `?x0)) -> ?x `notin` ott.fv_eexpr (berase (?e' ^^' `' ?x0)) |- _ =>
        eapply open_expr_wrt_new_var_keeps_notin_erase with (x':=x0) (n0:=0) in H; eauto 3;
        specialize (H1 H); eapply open_bexpr_wrt_new_var_keeps_notin_berase with (n0:=0); eauto 3
      end
  end.

Lemma usub_elab_keeps_notin_fv_erase_helper : forall x x' e e',
  x <> x' ->
  x `notin` ott.fv_eexpr (erase e) ->
  (x `notin` ott.fv_eexpr (erase (e ^^ ` x')) -> x `notin` ott.fv_eexpr (berase (e' ^^' `' x'))) ->
  x `notin` ott.fv_eexpr (berase e').
Proof.
  intros.
  convert_to_open_expr_wrt_new_var.
Qed.

Lemma usub_elab_keeps_notin_fv_erase : forall Γ e1 e2 A Γ' e1' e2' A' x,
   usub_elab Γ e1 e2 A Γ' e1' e2' A' ->
      (x `notin` ott.fv_eexpr (erase e1) ->  x `notin` ott.fv_eexpr (berase e1')) /\
      (x `notin` ott.fv_eexpr (erase e2) ->  x `notin` ott.fv_eexpr (berase e2')).
Proof.
  intros.
  induction H; try (simpl in *; auto; fail); simpl in *; inst_cofinites_by (add x L); destruct_conjs; split; intros.
  - eapply usub_elab_keeps_notin_fv_erase_helper with (e:=e1) (x':=x0); eauto.
  - eapply usub_elab_keeps_notin_fv_erase_helper with (e:=e2) (x':=x0); eauto.
  - apply notin_union.
    + auto.
    + eapply usub_elab_keeps_notin_fv_erase_helper with (e:=B1) (x':=x0); eauto.
  - apply notin_union. auto.
    eapply usub_elab_keeps_notin_fv_erase_helper with (e:=B2) (x':=x0); eauto.
  - eapply usub_elab_keeps_notin_fv_erase_helper with (e:=e1) (x':=x0); eauto.
  - eapply usub_elab_keeps_notin_fv_erase_helper with (e:=e2) (x':=x0); eauto.
  - apply notin_union. auto. apply notin_union_2 in H12.
    eapply usub_elab_keeps_notin_fv_erase_helper with (e:=B) (x':=x0); eauto.
  - auto.
  - auto.
  - apply notin_union. auto.
    eapply usub_elab_keeps_notin_fv_erase_helper with (e:=C) (x':=x0); eauto.
  - apply notin_union. auto.
    eapply usub_elab_keeps_notin_fv_erase_helper with (e:=B) (x':=x0); eauto.
  - apply notin_union. auto.
    eapply usub_elab_keeps_notin_fv_erase_helper with (e:=C) (x':=x0); eauto.
Qed.

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
  - eauto.
  - eapply bs_abs; eauto 6...
  - eauto...
  - econstructor; eauto...
    + eapply usub_elab_keeps_mono; eauto.
    + constructor; eapply busub_all_lc; eauto.
  - eapply bs_bind with (L:=L) (A1:=A1'); eauto; intros;
    inst_cofinites_with x; eauto...
    eapply bs_sub; eauto. eapply bs_star_inf. eapply busub_context_is_wf; eauto.
    eapply bs_sub; eauto. eapply bs_star_inf. eapply busub_context_is_wf; eauto.
    eapply usub_elab_keeps_notin_fv_erase with (e1':=(e1'0 ^^' `' x)) (e2':=(e2'0 ^^' `' x)); eauto.
    eapply usub_elab_keeps_notin_fv_erase with (e1':=(e1'0 ^^' `' x)) (e2':=(e2'0 ^^' `' x)); eauto.
  - eapply bs_castup with (B:=B'); eauto. admit. admit. admit.
  - eapply bs_anno; eauto... admit.
  - eapply bs_forall_l with (t:=t'); eauto...
    + eapply usub_elab_keeps_mono; eauto.
  - econstructor; eauto.
  - eapply bs_forall; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
    + rewrite <- (wf_context_elab_same_dom Γ0 Γ'0); auto.
Admitted.


Lemma to_decl_open_expr_wrt_expr_distr_rec : forall e1 e2 n,
  to_decl (open_bexpr_wrt_bexpr_rec n e2 e1) = open_expr_wrt_expr_rec n (to_decl e2) (to_decl e1).
Proof.
  intro e1. pattern e1.
  eapply bexpr_mut with
  ( P0 := fun ( b : bbody ) =>
    forall e2 n, to_body (open_bbody_wrt_bexpr_rec n e2 b) = open_body_wrt_expr_rec n (to_decl e2) (to_body b)); intros; auto;
  try (simpl; rewrite <- H; auto; rewrite <- H0; auto; fail).
  - simpl. destruct (lt_eq_lt_dec n n0); simpl; auto.
    + destruct s; auto.
Qed.


Lemma to_decl_open_body_wrt_expr_distr_rec : forall b e n,
  to_body (open_bbody_wrt_bexpr_rec n e b) = open_body_wrt_expr_rec n (to_decl e) (to_body b).
Proof.
  intro b. pattern b.
  eapply bbody_mut with
    ( P := fun e1 =>
      forall e2 n, to_decl (open_bexpr_wrt_bexpr_rec n e2 e1) = open_expr_wrt_expr_rec n (to_decl e2) (to_decl e1))
    ( P0 := fun b =>
      forall e n, to_body (open_bbody_wrt_bexpr_rec n e b) = open_body_wrt_expr_rec n (to_decl e) (to_body b));
    intros; auto;
  try (simpl; rewrite <- H; auto; rewrite <- H0; auto; fail).
  - simpl. destruct (lt_eq_lt_dec n n0); simpl; auto.
    + destruct s; auto.
Qed.


Lemma to_decl_open_expr_wrt_expr_distr : forall e1 e2,
  to_decl (open_bexpr_wrt_bexpr e1 e2) = open_expr_wrt_expr (to_decl e1) (to_decl e2).
Proof.
  intros. unfold open_bexpr_wrt_bexpr. unfold open_expr_wrt_expr.
  rewrite to_decl_open_expr_wrt_expr_distr_rec. auto.
Qed.


Lemma to_decl_open_body_wrt_expr_distr : forall b1 e2,
  to_body (open_bbody_wrt_bexpr b1 e2) = open_body_wrt_expr (to_body b1) (to_decl e2).
Proof.
  intros. unfold open_bbody_wrt_bexpr. unfold open_body_wrt_expr.
  rewrite to_decl_open_body_wrt_expr_distr_rec. auto.
Qed.


Lemma to_decl_open_expr_wrt_var_distr : forall e1 x,
  to_decl (e1 ^^' `'x)  = to_decl e1 ^^ `x.
Proof.
  intros.
  replace (`x) with (to_decl `'x) by auto.
  eapply to_decl_open_expr_wrt_expr_distr.
Qed.


Ltac destruct_lc :=
  match goal with
  | H : lc_bexpr (?P ?e1) |- _ => dependent destruction H
  | H : lc_bexpr (?P ?e1 ?e2) |- _ => dependent destruction H
  end.


Lemma to_decl_keeps_lc : forall e,
  lc_bexpr e -> lc_expr (to_decl e).
Proof.
  intros.
  pattern e, H.
  eapply lc_bexpr_mut with
    ( P0 := fun b (_ : lc_bbody b) =>
        lc_body (to_body b)
    ); intros; simpl; auto.
  - constructor. auto.
    intros. replace (` x) with (to_decl (`' x)) by auto.
    rewrite <- to_decl_open_body_wrt_expr_distr. auto.
  - constructor; auto. intros.
    rewrite <- to_decl_open_expr_wrt_var_distr. auto.
  - econstructor; eauto. intros.
    intros. replace (` x) with (to_decl (`' x)) by auto.
    rewrite <- to_decl_open_body_wrt_expr_distr. auto.
  - constructor; auto. intros.
    rewrite <- to_decl_open_expr_wrt_var_distr. auto.
Qed.


Lemma to_decl_keeps_mono : forall t,
  mono_btype t -> mono_type (to_decl t).
Proof.
  intros.
  induction H; simpl; eauto.
  - econstructor; now eapply to_decl_keeps_lc.
  - eapply mono_pi with (L:=L); auto. intros.
    rewrite <- to_decl_open_expr_wrt_var_distr; auto.
  - eapply mono_lambda with (L:=L); auto.
    now eapply to_decl_keeps_lc.
    replace  (λ_ to_decl A, to_decl e : to_decl B) with (to_decl ((λ, A, e : B))) by auto. now eapply to_decl_keeps_lc.
    intros. replace (` x) with (to_decl (`' x)) by auto. rewrite <- to_decl_open_expr_wrt_expr_distr. auto.
  - eapply mono_bind with (L:=L); auto. intros.
    now eapply to_decl_keeps_lc.
    replace  (Λ to_decl A, to_decl e : to_decl B) with (to_decl (Λ, A, e : B)) by auto. now eapply to_decl_keeps_lc.
    intros. replace (` x) with (to_decl (`' x)) by auto. rewrite <- to_decl_open_expr_wrt_expr_distr. auto.
  - eapply mono_castup; auto.
    now eapply to_decl_keeps_lc.
Qed.


Hint Resolve to_decl_keeps_lc : lc.


Lemma to_decl_keeps_reduce : forall A B,
  breduce A B -> reduce (to_decl A) (to_decl B).
Proof.
  intros. induction H; simpl in *; eauto with lc.
  - rewrite to_decl_open_expr_wrt_expr_distr; econstructor; eauto with lc;
    replace (λ_ to_decl A, to_decl e1 : to_decl B) with (to_decl ((λ, A, e1 : B))) by auto; now apply to_decl_keeps_lc.
  - rewrite to_decl_open_expr_wrt_expr_distr. eapply r_inst;
    try replace (Λ to_decl A, to_decl e1 : to_decl B) with (to_decl ((Λ, A, e1 : B))) by auto; try now apply to_decl_keeps_lc.
    now apply to_decl_keeps_mono.
  - rewrite to_decl_open_expr_wrt_expr_distr. eapply r_cast_inst;
    try replace (Λ to_decl A, to_decl e1 : to_decl B) with (to_decl ((Λ, A, e1 : B))) by auto; try now apply to_decl_keeps_lc.
    now apply to_decl_keeps_mono.
Qed.


Lemma to_decl_context_keeps_lc_context : forall Γ,
  lc_bcontext Γ -> lc_context (to_decl_context Γ).
Proof.
  intros.
  induction Γ; auto.
  - dependent destruction H. simpl. constructor. auto.
    now apply to_decl_keeps_lc.
Qed.


Lemma to_decl_keeps_in_context : forall Γ x A ,
  in_bctx x A Γ -> x :_ (to_decl A) ∈ (to_decl_context Γ).
Proof.
  intros.
  dependent induction H.
  - simpl. apply in_here; auto.
    + now apply to_decl_context_keeps_lc_context.
    + now apply to_decl_keeps_lc.
  - econstructor. now apply to_decl_keeps_lc. auto.
Qed.


Lemma to_decl_context_ctx_dom_equiv : forall Γ,
  bctx_dom Γ = ctx_dom (to_decl_context Γ).
Proof.
  induction Γ; auto.
  simpl. rewrite IHΓ. auto.
Qed.


Lemma to_decl_keeps_notin_fv_expr : forall e x,
  x `notin` ott.fv_eexpr (berase e) -> x `notin` ott.fv_eexpr (erase (to_decl e)).
Proof.
  intros e x. pattern e.
  eapply bexpr_mut with
  (P0 := fun b =>
      match b with
      | bb_anno e A =>
          x `notin` ott.fv_eexpr (berase e) ->
          x `notin` ott.fv_eexpr (erase (to_decl e))
      end
    ); intros; try (simpl in *; auto; fail).
  - destruct k; auto.
  - destruct b. simpl in *. auto.
  - destruct b. simpl in *. auto.
Qed.


Hint Resolve to_decl_keeps_reduce : sound.
Hint Resolve to_decl_keeps_notin_fv_expr : sound.
Hint Resolve to_decl_keeps_mono : sound.


Lemma eall_sub_open_sub : forall Γ t A B C,
  Γ ⊢ e_all A B : ⋆ -> Γ ⊢ t : A -> mono_type t ->  Γ ⊢ B ^^ t <: C : ⋆ -> Γ ⊢ e_all A B <: C : ⋆.
Proof.
  intros.
  specialize (type_correctness_eall_param _ _ _ _ H H0). intros.
  specialize (eall_open_var _ _ _  H). intros.
  destruct H3 as [k]. destruct H4 as [L].
  eapply ott.s_forall_l with (t:=t); eauto.
Qed.

Corollary eall_sub_open : forall Γ t A B,
  Γ ⊢ e_all A B : ⋆ -> Γ ⊢ t : A -> mono_type t -> Γ ⊢ e_all A B <: B ^^ t : ⋆.
Proof.
  intros.
  eapply eall_sub_open_sub; eauto.
  eapply eall_open_mono; eauto.
Qed.


Theorem bidir_sound : forall Γ e1 e2 d A,
  busub Γ e1 e2 d A -> to_decl_context Γ ⊢ to_decl e1 <: to_decl e2 : to_decl A.
Proof with auto with sound.
  intros.
  pattern Γ, e1, e2, d, A, H.
  eapply busub_mut with
    ( P0 := fun Γ (_ : ⫦ Γ) => ⊢ to_decl_context Γ )
    ( P1 := fun Γ A F (_ : infer_app Γ A F) =>
      match F with
      | fun_pi B C =>
        match A with
        | be_pi _ _ => True
        | be_all _ _ => to_decl_context Γ ⊢ to_decl A : ⋆ ->
                        to_decl_context Γ ⊢ to_decl A <: e_pi (to_decl B) (to_decl C) : ⋆
        | _ => False
        end
      end
    )
    ( P2 := fun Γ A B (pf : Γ ⊢ A ⟼ B) =>
      to_decl_context Γ ⊢ to_decl A : ⋆ -> to_decl A ⟶ to_decl B \/
      exists C, to_decl_context Γ ⊢ to_decl A <: to_decl C : ⋆ /\ to_decl C ⟶ to_decl B
    );
    intros; try (constructor; auto; fail); simpl in *.
  - constructor; auto. now eapply to_decl_keeps_in_context.
  - eauto.
  - eapply ott.s_abs with (L:=L); eauto;
    intros; inst_cofinites_with x; repeat rewrite <- to_decl_open_expr_wrt_var_distr; eauto.
    + eapply narrowing_cons; eauto.
    + eapply narrowing_cons; eauto.
  - eapply ott.s_pi with (L:=L); eauto;
    intros; inst_cofinites_with x; repeat rewrite <- to_decl_open_expr_wrt_var_distr; eauto.
  -  dependent destruction i.
    + rewrite to_decl_open_expr_wrt_expr_distr.
      eapply ott.s_app with (A:=to_decl B); eauto...
    + simpl in H0. specialize (type_correctness_eall _ _ _ _ _ H0). intros. specialize (H3 H5).
      rewrite to_decl_open_expr_wrt_expr_distr.
      eapply ott.s_app with (A:=to_decl B); eauto...
  - eapply ott.s_bind with (L:=L); eauto;
    intros; repeat rewrite <- to_decl_open_expr_wrt_var_distr; eauto...
    + eapply narrowing_cons; eauto.
    + eapply narrowing_cons; eauto.
  - eapply ott.s_castup; eauto...
  - dependent destruction g.
    + eapply ott.s_castdn with (A:=to_decl e4); eauto...
    + simpl in H4. specialize (type_correctness_eall _ _ _ _ _ H4). intros.
      * destruct (H3 H5).
        -- eapply ott.s_castdn with (A:=to_decl (be_all A0 B)); eauto.
        -- destruct H6 as [D [Hsub Hred]]. eapply ott.s_castdn with (A:=to_decl D); eauto.
  - eapply ott.s_forall_l with (L:=L) (t:=to_decl t); eauto...
    + rewrite <- to_decl_open_expr_wrt_expr_distr. auto.
    + intros. inst_cofinites_with x. rewrite <- to_decl_open_expr_wrt_var_distr. auto.
  - eapply ott.s_forall_r with (L:=L); eauto.
    intros. inst_cofinites_with x. rewrite <- to_decl_open_expr_wrt_var_distr. auto.
  - eapply ott.s_forall with (L:=L); eauto.
    intros. inst_cofinites_with x. repeat rewrite <- to_decl_open_expr_wrt_var_distr. auto.
  - simpl in *; auto.
  - eauto.

  (* P0 *)
  - econstructor; eauto. now rewrite <- to_decl_context_ctx_dom_equiv.

  (* P1 *)
  - dependent destruction F. dependent destruction i; intros.
    + rewrite <- x in H4.
      replace (e_pi (to_decl A1) (to_decl B0)) with (to_decl (be_pi A1 B0)) by auto.
      rewrite x. rewrite to_decl_open_expr_wrt_expr_distr.
      eapply  eall_sub_open; eauto...
    + rewrite <- x in H3. rewrite x in H3.
      rewrite to_decl_open_expr_wrt_expr_distr in H3.
      assert (to_decl_context G ⊢ to_decl B ^^ to_decl t : ⧼ k_star ⧽) by (eapply eall_open_mono; eauto with sound).
      specialize (H3 H5).
      eapply eall_sub_open_sub; eauto...

  (* P2 *)
  - left. auto...
  - right. destruct H1.
    + rewrite to_decl_open_expr_wrt_expr_distr.
      simpl in H2. specialize (eall_open_var _ _ _ H2). intros.
      destruct H1 as [L]. inst_cofinites_by (L `union` fv_expr (to_decl B)).
      eapply eall_open_mono; eauto...
    + exists (B ^^' t). split; auto.
      rewrite to_decl_open_expr_wrt_expr_distr.
      eapply  eall_sub_open; eauto...
    + destruct H1 as [D [Hsub Hred]]. exists D. split; auto. simpl in *. rewrite to_decl_open_expr_wrt_expr_distr in Hsub.
      eapply eall_sub_open_sub; eauto...
Qed.

Print Assumptions bidir_sound.
