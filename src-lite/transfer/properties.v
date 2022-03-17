Require Import transfer.syntax.
Require Import lc.
Require Import Program.Equality.
Require Import list_properties.
Require Import ln_utils.

Hint Extern 2 (_ = _) => simpl; congruence : core.

Lemma inst_e_det : forall e' Θ e1,
  uniq Θ → Θ ⊩ e' ⇝ e1 → forall e2, Θ ⊩ e' ⇝ e2 → e1 = e2.
Proof.
  intros * Uniq H1.
  induction H1; intros e2 H2; inversion H2; subst; auto;
  (* solving all the binds with binds_unique in metalib *)
  try match goal with
  | H1 : binds ?x ?e1 ?c , H2 : binds ?x ?e2 ?c |- _ = _ =>
    let E := fresh "E" in
      assert (e1 = e2) as E by (eapply binds_unique; eauto);
      inversion E; now subst
  end;

  repeat match goal with
  (* basic inductive cases *)
  | H1 : _ ⊩ ?e ⇝ ?e1 , H2 : _ ⊩ ?e ⇝ ?e2 |- _ =>
      assert (e1 = e2) by auto; clear H1 H2
  (* inductive cases with locally nameless mess *)
  | H1 : forall x, x `notin` ?L1 → _ ⊩ _ ⇝ ?e1 ^`' x
  , H2 : forall x, x `notin` ?L2 → _ ⊩ _ ⇝ ?e2 ^`' x
    |- _ => pick fresh x for
      (L1 `union` L2 `union` fv_bexpr e1 `union` fv_bexpr e2);
         assert (e1 ^`' x = e2 ^`' x) by eauto;
         assert (e1 = e2) by (eapply open_bexpr_wrt_bexpr_inj; eauto)
  end;
  congruence.
Qed.

Lemma inst_wl_split : forall Γ1' Γ2' Γ Θ Θ'
  , Θ ⊩ Γ1' ⫢′ Γ2' ⟿ Γ ⫣ Θ'
  → exists Γ1 Γ2 Θ0
    , Γ = Γ1 ⫢ Γ2
    ∧ Θ  ⊩ Γ1' ⟿ Γ1 ⫣ Θ0
    ∧ Θ0 ⊩ Γ2' ⟿ Γ2 ⫣ Θ'.
Proof.
  induction Γ2'; simpl; intros.
  - exists Γ, dwl_nil, Θ'; simpl; eauto.
  - inversion H; subst.
    pose proof (IHΓ2' _ _ _ H3) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
    exists Γ1, (Γ2 ⊨ w0), Θ0. repeat split; eauto.
  - destruct b; inversion H; subst.
    + pose proof (IHΓ2' _ _ _ H4) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
      exists Γ1, (Γ2 ,′' x : A0), Θ0.
      subst. repeat split; auto.
    + pose proof (IHΓ2' _ _ _ H5) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
      exists Γ1, Γ2, Θ0.
      subst. repeat split; auto.
    + pose proof (IHΓ2' _ _ _ H3) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
      exists Γ1, Γ2, Θ0.
      subst. repeat split; auto.
Qed.

Scheme wl_mut   := Induction for worklist Sort Prop
  with work_mut := Induction for work     Sort Prop.

Lemma inst_wl_ss_extend : forall Θ Γ' Γ Θ'
  , Θ ⊩ Γ' ⟿ Γ ⫣ Θ'
  → exists Θ0, Θ ;; Θ0 = Θ'.
Proof.
  intros * H.
  pattern Θ, Γ', Γ, Θ', H.
  apply wlinst_mut with
    (P := fun Θ w' w Θ' (_ : Θ ⊩ w' ⇝′ w ⫣ Θ') => exists Θ0, Θ ;; Θ0 = Θ');
    intros.

  - now exists nil.
  - now exists nil.
  - pick fresh x. eauto.
  - pick fresh x. eauto.
  - pick fresh x. eauto.
  - now exists nil.

  - destruct H0. destruct H1. subst. now exists (x ;; x0).
  - destruct H0. subst. now exists (x0; x : A !).
  - destruct H0. subst. now exists (x0; x ≔ ⧼k⧽).
  - destruct H0. subst. now exists (x0; x : A ≔ e).
Qed.

Lemma inst_w_ss_extend : forall Θ w' w Θ'
  , Θ ⊩ w' ⇝′ w ⫣ Θ'
  → exists Θ0, Θ ;; Θ0 = Θ'.
Proof.
  induction 1; solve
    [now exists nil
    | pick fresh x; eauto using inst_wl_ss_extend].
Qed.

Lemma inst_e_weakening : forall Θ1 Θ2 e' e Θ'
  , Θ1 ;; Θ2 ⊩ e' ⇝ e → wf_ss (Θ1 ;; Θ' ;; Θ2)
  → Θ1 ;; Θ' ;; Θ2 ⊩ e' ⇝ e.
Proof.
  intros * H.
  dependent induction H; intros; eauto 4.
Qed.

#[local]
Hint Resolve inst_e_weakening : inst_weakening.

Lemma inst_e_weakening_app : forall Θ Θ' e' e
  , Θ       ⊩ e' ⇝ e → wf_ss (Θ ;; Θ')
  → Θ ;; Θ' ⊩ e' ⇝ e.
Proof.
  intros.
  replace (Θ ;; Θ') with (Θ ;; Θ' ;; nil) by auto.
  auto with inst_weakening.
Qed.

#[local]
Hint Resolve inst_e_weakening_app : inst_weakening.

Lemma inst_ob_weakening : forall Θ1 Θ2 Θ' ob' ob
  , Θ1 ;; Θ2 ⊩ ob' ⇝? ob → wf_ss (Θ1 ;; Θ' ;; Θ2)
  → Θ1 ;; Θ' ;; Θ2 ⊩ ob' ⇝? ob.
Proof.
  intros. dependent destruction H; eauto with inst_weakening.
Qed.

#[local]
Hint Resolve inst_ob_weakening : inst_weakening.

Lemma wf_ss_unapp : forall xs ys,
    wf_ss (xs ;; ys) → wf_ss xs.
Proof.
  induction ys; intros.
  - assumption.
  - inversion H; auto.
Qed.

Lemma wf_ss_uncons : forall xs x,
    wf_ss (x :: xs) → wf_ss xs.
Proof.
  destruct x; inversion 1; auto.
Qed.


Hint Immediate wf_ss_unapp wf_ss_uncons : inst_weakening.
Hint Immediate wf_ss_unapp wf_ss_uncons : wf_ss.

Ltac clear_app_suffix_impl :=
  match goal with
  | H : ?xs = ?ys ++ ?xs |- _ =>
      assert (ys = nil) as -> by
        now apply app_nil_invert in H
  | H : ?ys ++ ?xs = ?xs |- _ =>
      symmetry in H
  | H : ?ys ++ ?xs = ?zs ++ ?xs |- _ =>
      apply app_inj_l in H
  | H : ?ys1 ++ ?ys2 ++ ?xs = ?zs ++ ?xs |- _ =>
      rewrite <- (app_assoc _ ys1 ys2 xs) in H
  | H : ?zs ++ ?xs = ?ys1 ++ ?ys2 ++ ?xs |- _ =>
      symmetry in H; clear_app_suffix_impl
  | H : ?x :: ?ys ++ ?xs = ?zs ++ ?xs |- _ =>
      rewrite <- (cons_app_assoc _ x ys xs) in H;
      clear_app_suffix_impl
  | H : ?zs ++ ?xs = ?x :: ?ys ++ ?xs  |- _ =>
      symmetry in H; clear_app_suffix_impl
  end; simpl in *
.

Ltac clear_app_suffix :=
  repeat progress clear_app_suffix_impl.

Ltac simplify_list_eq :=
  repeat (subst || clear_app_suffix);
  repeat rewrite app_assoc in *;
  simpl in *.

Ltac conclude_ss_extend_impl :=
  let process t1 t2 tac :=
    let t3 := fresh "Θ" in
    let E  := fresh "E" in
    lazymatch t2 with
    (* t2 is already an extension of t1 *)
    | t1 ;; ?t => fail
    | _ =>
        lazymatch goal with
        (* the equality we want to conclude already exists *)
        | _ : t1 ;; ?t = t2 |- _ => fail
        (* doing actual stuff *)
        | _ => assert (exists t, t1 ;; t = t2) as [t3 E] by tac
        end
    end
  in
  match goal with
  | H : ?t1 ⊩ _ ⟿ _ ⫣ ?t2 |- _ =>
      process t1 t2 ltac:(eapply inst_wl_ss_extend; eassumption)
  | H : ?t1 ⊩ _ ⇝′ _ ⫣ ?t2 |- _ =>
      process t1 t2 ltac:(eapply inst_w_ss_extend; eassumption)
  end
.

Ltac conclude_ss_extend :=
  repeat conclude_ss_extend_impl.

Lemma inst_wl_weakening : forall Θ1 Θ2 Θ3 Γ' Γ
  , Θ1 ;; Θ2 ⊩ Γ' ⟿ Γ ⫣ Θ1 ;; Θ2 ;; Θ3
  → forall Θ', wf_ss (Θ1 ;; Θ' ;; Θ2 ;; Θ3)
  → Θ1 ;; Θ' ;; Θ2 ⊩ Γ' ⟿ Γ ⫣ Θ1 ;; Θ' ;; Θ2 ;; Θ3.
Proof.
  intros * H.
  (* manual dependent mutual induction *)
  remember (Θ1 ;; Θ2 ;; Θ3) as Θ'.
  remember (Θ1 ;; Θ2) as Θ.
  generalize dependent Θ3;
  generalize dependent Θ2;
  generalize dependent Θ1.
  pattern Θ, Γ', Γ, Θ', H.
  apply wlinst_mut with
    (P := fun Θ w' w Θ0 (_ : Θ ⊩ w' ⇝′ w ⫣ Θ0) =>
      forall Θ1 Θ2 Θ3 Θ', Θ = Θ1 ;; Θ2 → Θ0 = Θ1 ;; Θ2 ;; Θ3
      → wf_ss (Θ1 ;; Θ' ;; Θ2 ;; Θ3)
      → Θ1 ;; Θ' ;; Θ2 ⊩ w' ⇝′ w ⫣ Θ1 ;; Θ' ;; Θ2 ;; Θ3);
    intros; subst.

  (* inst_w *)
  - clear_app_suffix; eauto 6 with inst_weakening.
  - clear_app_suffix; eauto 6 with inst_weakening.
  - eauto with inst_weakening.
  - eauto with inst_weakening. admit.
  - eauto with inst_weakening.

  (* inst_wl *)
  - clear_app_suffix. auto.
  - conclude_ss_extend. simplify_list_eq.
    eapply instwl_cons.
    + eauto with inst_weakening.
    + replace (Θ1;; Θ'1;; Θ2;; Θ0;; Θ5) with
        (Θ1;; Θ'1;; (Θ2;; Θ0);; Θ5) by
        now repeat rewrite <- app_assoc.
    rewrite <- (app_assoc _ Θ0 Θ2 (Θ1 ;; Θ'1)).
    apply H1; eauto 4; repeat rewrite app_assoc; auto.
  - conclude_ss_extend; simplify_list_eq.
    inversion H1; subst; constructor; auto.
    + rewrite <- app_assoc; apply inst_e_weakening;
      now rewrite app_assoc.
  - conclude_ss_extend; simplify_list_eq.
    inversion H1; subst. constructor; auto.
  - conclude_ss_extend; simplify_list_eq.
    inversion H1; subst. constructor; auto.
    + rewrite <- app_assoc; apply inst_e_weakening;
       now rewrite app_assoc.
Admitted.

Hint Resolve inst_wl_weakening : inst_weakening.

Lemma inst_w_weakening : forall Θ1 Θ2 Θ3 w' w
  , Θ1 ;; Θ2 ⊩ w' ⇝′ w ⫣ Θ1 ;; Θ2 ;; Θ3
  → forall Θ', wf_ss (Θ1;; Θ';; Θ2 ;; Θ3)
  → Θ1 ;; Θ' ;; Θ2 ⊩ w' ⇝′ w ⫣ Θ1 ;; Θ' ;; Θ2 ;; Θ3.
Proof.
  intros * H.
  dependent induction H; intros;
    clear_app_suffix; eauto 6 with inst_weakening.
  admit.
Admitted.

Lemma bexpr_subst_open_comm : forall x v1 e v2
  , lc_bexpr v1 → x `notin` fv_bexpr v2
  → ([v1 /' x] e) ^^' v2 = [v1 /' x] e ^^' v2.
Proof.
  intros.
  rewrite subst_bexpr_open_bexpr_wrt_bexpr.
  rewrite (subst_bexpr_fresh_eq v2).
  all: easy.
Qed.

Lemma aexpr_subst_open_comm : forall x v1 e v2
  , lc_aexpr v1 → x `notin` fv_aexpr v2
  → ([v1 /′ x] e) ^^′ v2 = [v1 /′ x] e ^^′ v2.
Proof.
  intros.
  rewrite subst_aexpr_open_aexpr_wrt_aexpr.
  rewrite (subst_aexpr_fresh_eq v2).
  all: easy.
Qed.

Lemma worklist_subst_open_comm : forall x v1 Γ v2
  , lc_aexpr v1 → x `notin` fv_aexpr v2
  → subst_worklist v1 x Γ $′ v2 = subst_worklist v1 x (Γ $′ v2).
Proof.
  intros.
  rewrite subst_worklist_open_worklist_wrt_aexpr.
  rewrite (subst_aexpr_fresh_eq v2).
  all: easy.
Qed.

Lemma dworklist_subst_open_comm : forall x v1 Γ v2
  , lc_bexpr v1 → x `notin` fv_bexpr v2
  → subst_dworklist v1 x Γ $ v2 = subst_dworklist v1 x (Γ $ v2).
Proof.
  intros.
  rewrite subst_dworklist_open_dworklist_wrt_bexpr.
  rewrite (subst_bexpr_fresh_eq v2).
  all: easy.
Qed.


Lemma bexpr_subst_open_var_comm : forall x1 x2 v e
  , lc_bexpr v → x1 <> x2
  → ([v /' x1] e) ^`' x2 = [v /' x1] e ^`' x2.
Proof.
  intros. rewrite bexpr_subst_open_comm; auto.
Qed.

Hint Rewrite bexpr_subst_open_comm aexpr_subst_open_comm : ln.
Hint Rewrite worklist_subst_open_comm dworklist_subst_open_comm : ln.
Hint Extern 4 => progress autorewrite with ln : ln.

Lemma notin_ss_sse : forall e x x' s,
  x `notin` fv_ss s → binds x' e s → x `notin` fv_sse e.
Proof.
  induction s; intros.
  - inversion H0.
  - destruct H0.
    + subst. simpl in H. auto.
    + eapply IHs. destruct a; simpl in H. auto. auto.
Qed.

Lemma bind_notin_inst : forall x ex A e Θ,
    ex : A ≔ e ∈ Θ → x `notin` fv_ss_inst Θ → x `notin` fv_bexpr e.
Proof.
  induction Θ; intros.
  - inversion H.
  - destruct a.
    destruct s; unfold fv_ss_inst in H0; simpl in H0;
      inversion H; try inversion H1; subst; auto.
Qed.

Hint Resolve bind_notin_inst : atoms.

Lemma inst_e_rename : forall Θ e' e x x'
  , Θ ⊩ e' ⇝ e → x `notin` fv_ss_inst Θ
  → Θ ⊩ [`′ x' /′ x] e' ⇝ [`' x' /' x] e.
Proof.
  intros; induction H; simpl; auto.
  - unfold eq_dec. destruct (EqDec_eq_of_X x0 x); auto.
  - rewrite subst_bexpr_fresh_eq; eauto with atoms.
  - apply inste_abs  with (add x L); eauto with ln.
  - apply inste_bind with (add x L); eauto with ln.
  - apply inste_pi   with (add x L); eauto with ln.
  - apply inste_all  with (add x L); eauto with ln.
Qed.

Hint Resolve inst_e_rename : ln.

Lemma inst_ob_rename : forall Θ ob' ob x x'
  , Θ ⊩ ob' ⇝? ob → x `notin` fv_ss_inst Θ
  → Θ ⊩ subst_obind (`′ x') x ob' ⇝? subst_obindd (`' x') x ob.
Proof.
  intros.
  destruct H; simpl; eauto with ln.
Qed.

Hint Resolve inst_ob_rename : ln.

Lemma inst_eq_ex_in : forall Θ1 Θ2 x A e,
  x : A ≔ e ∈ Θ1 → inst_set Θ1 = inst_set Θ2 → exists A', x : A' ≔ e ∈ Θ2.
Proof.
  induction Θ1; simpl; intros.
  - inversion H.
  - destruct H; destruct a; destruct s; try (inversion H; subst).
    + induction Θ2.
      * inversion H0.
      * destruct a. simpl in H0. destruct s.
        -- destruct IHΘ2; eauto.
        -- inversion H0; eauto.
        -- inversion H0.
    + eauto.
    + induction Θ2.
      * inversion H0.
      * destruct a0. simpl in H0. destruct s.
        -- destruct IHΘ2; eauto.
        -- inversion H0; edestruct IHΘ1; eauto.
        -- inversion H0.
    + induction Θ2.
      * inversion H0.
      * destruct a0. simpl in H0. destruct s.
        -- destruct IHΘ2; eauto.
        -- inversion H0.
        -- inversion H0; edestruct IHΘ1; eauto.
Qed.

Lemma inst_eq_k_in : forall Θ1 Θ2 x k,
  x ≔ ⧼ k ⧽ ∈ Θ1 → inst_set Θ1 = inst_set Θ2 → x ≔ ⧼ k ⧽ ∈ Θ2.
Proof.
  induction Θ1; simpl; intros.
  - inversion H.
  - destruct H; destruct a; destruct s; try (inversion H; subst).
    + induction Θ2.
      * inversion H0.
      * destruct a. simpl in H0. destruct s.
        -- auto.
        -- inversion H0.
        -- inversion H0. auto.
    + auto.
    + induction Θ2.
      * inversion H0.
      * destruct a0. simpl in H0. destruct s.
        -- auto.
        -- inversion H0. auto.
        -- inversion H0.
    + induction Θ2.
      * inversion H0.
      * destruct a0. simpl in H0. destruct s.
        -- auto.
        -- inversion H0.
        -- inversion H0. auto.
Qed.

Lemma inst_eq_inst_e : forall Θ1 e' e
  , Θ1 ⊩ e' ⇝ e → forall Θ2
  , wf_ss Θ2 → inst_set Θ1 = inst_set Θ2
  → Θ2 ⊩ e' ⇝ e.
Proof.
  induction 1; simpl; intros; eauto 4.
  - apply inst_eq_ex_in with (Θ2 := Θ2) in H0; auto.
    destruct H0. eauto.
  - apply inst_eq_k_in with (Θ2 := Θ2) in H0; auto.
Qed.

#[local]
Hint Resolve inst_eq_inst_e : inst_eq.

Lemma inst_eq_inst_ob : forall Θ1 ob' ob
  , Θ1 ⊩ ob' ⇝? ob → forall Θ2
  , wf_ss Θ2 → inst_set Θ1 = inst_set Θ2
  → Θ2 ⊩ ob' ⇝? ob.
Proof.
  destruct 1; simpl; intros; eauto with inst_eq.
Qed.

#[local]
Hint Resolve inst_eq_inst_ob : inst_eq.

Lemma inst_set_app_distr : forall Θ2 Θ1,
    inst_set (Θ1 ;; Θ2) = inst_set Θ1 ;; inst_set Θ2.
Proof.
  env induction Θ2; simpl; intros.
  - reflexivity.
  - destruct a; auto.
Qed.

Lemma subst_ss_app_distr : forall Θ2 Θ1 x e,
  subst_ss e x (Θ1 ;; Θ2) = subst_ss e x Θ1 ;; subst_ss e x Θ2.
Proof.
  env induction Θ2; simpl; intros; auto.
Qed.

Lemma inst_eq_app : forall Θ1 Θ2 Θ3 Θ4
  , inst_set Θ1 = inst_set Θ2 → inst_set Θ3 = inst_set Θ4
  → inst_set (Θ1 ;; Θ3) = inst_set (Θ2 ;; Θ4).
Proof.
  intros.
  repeat rewrite inst_set_app_distr. congruence.
Qed.

#[local]
Hint Resolve inst_eq_app : inst_eq.

Lemma fv_ss_inst_app_union : forall Θ1 Θ2,
    fv_inst_set (Θ1 ;; Θ2) [=] fv_inst_set Θ1 `union` fv_inst_set Θ2.
Proof.
  intros. env induction Θ2; simpl; fsetdec.
Qed.

Lemma notin_equal : forall (s1 s2 : atoms) x,
    s1 [=] s2 → x `notin` s1 → x `notin` s2.
Proof.
  fsetdec.
Qed.

Lemma notin_inst_set_app : forall Θ1 Θ2 x
  , x `notin` fv_inst_set (Θ1 ;; Θ2)
  → x `notin` fv_inst_set Θ1 ∧ x `notin` fv_inst_set Θ2.
Proof.
  split.
  - eapply notin_union_1, notin_equal.
    apply fv_ss_inst_app_union. auto.
  - eapply notin_union_2, notin_equal.
    apply fv_ss_inst_app_union. auto.
Qed.

Lemma notin_ss_inst_app : forall Θ1 Θ2 x
  , x `notin` fv_ss_inst (Θ1 ;; Θ2)
  → x `notin` fv_ss_inst Θ1 ∧ x `notin` fv_ss_inst Θ2.
Proof.
  unfold fv_ss_inst.
  intros. rewrite inst_set_app_distr in H.
  auto using notin_inst_set_app.
Qed.

Import AtomSetProperties.

Lemma fv_inst_set_app_notin : forall Θ1 Θ2 x
  , x `notin` fv_inst_set Θ1 → x `notin` fv_inst_set Θ2
  → x `notin` fv_inst_set (Θ1 ;; Θ2).
Proof.
  intros.
  eapply notin_equal. apply equal_sym.
  apply fv_ss_inst_app_union.
  auto.
Qed.

Lemma fv_ss_inst_app_notin : forall Θ1 Θ2 x
  , x `notin` fv_ss_inst Θ1 → x `notin` fv_ss_inst Θ2
  → x `notin` fv_ss_inst (Θ1 ;; Θ2).
Proof.
  unfold fv_ss_inst. intros.
  rewrite inst_set_app_distr.
  auto using fv_inst_set_app_notin.
Qed.

Lemma fv_ss_inst_app_notin' : forall Θ1 Θ2 x
  , x `notin` fv_inst_set (inst_set Θ1)
  → x `notin` fv_inst_set (inst_set Θ2)
  → x `notin` fv_inst_set (inst_set (Θ1 ;; Θ2)).
Proof.
  apply fv_ss_inst_app_notin.
Qed.

Lemma dom_app_union : forall A (Θ1 Θ2 : list (var * A)),
    dom (Θ1 ;; Θ2) [=] dom Θ1 `union` dom Θ2.
Proof.
  env induction Θ2; simpl; fsetdec.
Qed.

Hint Resolve fv_ss_inst_app_notin fv_ss_inst_app_notin' : inst_notin.

Lemma notin_dom_app : forall A (Θ1 Θ2 : list (var * A)) x,
    x `notin` dom (Θ1 ;; Θ2) → x `notin` dom Θ1 ∧ x `notin` dom Θ2.
Proof.
  intros. apply (notin_equal _ (dom Θ1 `union` dom Θ2)) in H.
  - fsetdec.
  - apply dom_app_union.
Qed.

Lemma dom_app_notin : forall A (Θ1 Θ2 : list (var * A)) x,
    x `notin` dom Θ1 → x `notin` dom Θ2 → x `notin` dom (Θ1 ;; Θ2).
Proof.
  intros. eapply notin_equal.
  - apply equal_sym. apply dom_app_union.
  - auto.
Qed.

Hint Resolve dom_app_notin : inst_notin.

Lemma dom_subst_equal : forall e x Θ,
    dom Θ [=] dom (subst_ss e x Θ).
Proof.
  env induction Θ; simpl; fsetdec.
Qed.

Lemma notin_dom_subst : forall e x Θ x',
    x' `notin` dom Θ <-> x' `notin` dom (subst_ss e x Θ).
Proof.
  split; intros.
  - eapply notin_equal. apply dom_subst_equal. assumption.
  - eapply notin_equal. apply equal_sym, dom_subst_equal. eassumption.
Qed.

#[local]
Hint Resolve notin_dom_subst : inst_notin.

Lemma fv_ss_notin : forall Θ1 Θ2 x,
    x `notin` fv_ss Θ1 → x `notin` fv_ss Θ2 → x `notin` fv_ss (Θ1 ;; Θ2).
Proof.
  env induction Θ2; simpl; intros.
  - fsetdec.
  - apply notin_union; auto.
Qed.

#[local]
Hint Resolve fv_ss_notin : inst_notin.

Ltac destruct_notin_ext_impl :=
  destruct_notin;
  let F1 := fresh "Fr" in
  let F2 := fresh "Fr" in
  match goal with
  | H : _ `notin` fv_ss_inst (_ ;; _) |- _ =>
      apply notin_ss_inst_app in H as [F1 F2]
  | H : _ `notin` fv_inst_set (inst_set (_ ;; _)) |- _ =>
      apply notin_ss_inst_app in H as [F1 F2]
  | H : _ `notin` dom (_ ;; _) |- _ =>
      apply notin_dom_app in H as [F1 F2]
  | H : _ `notin` dom (subst_ss _ _ _) |- _ =>
      apply notin_dom_subst in H
  end
.

Ltac destruct_notin_ext :=
  repeat progress destruct_notin_ext_impl.

Lemma notin_ss_prefix : forall Θ1 Θ2 x,
    x `notin` fv_ss (Θ1 ;; Θ2) → x `notin` fv_ss Θ1.
Proof.
  induction Θ2; simpl; intros; auto.
  destruct a; auto.
Qed.

#[local]
Hint Resolve notin_ss_prefix : inst_notin.

#[local]
 Hint Extern 4 (_ `notin` fv_ss_inst _) =>
  inst_cofinites_with_new; conclude_ss_extend; simplify_list_eq;
  destruct_notin_ext; eauto with inst_notin : rename_impl.


Ltac rev_subst_gather_atoms :=
  let L0 := gather_atoms_with (fun x : atom => {{ x }}) in
  let L1 := gather_atoms_with (fun x : atoms => x) in
  let L2 := gather_atoms_with (fun x : bexpr => fv_bexpr x) in
  let L3 := gather_atoms_with (fun x : aexpr => fv_aexpr x) in
  let L4 := gather_atoms_with (fun x : subst_set => fv_ss x) in
  let L5 := gather_atoms_with (fun x : dworklist => fv_dworklist x) in
  let L6 := gather_atoms_with (fun x : worklist => fv_worklist x) in
  constr:(L0 `union` L1 `union` L2 `union` L3 `union` L4 `union` L5 `union` L6).

Tactic Notation "pick" "fresh" ident(x) "for" "all" :=
  let L  := rev_subst_gather_atoms in
  pick fresh x for L.

Lemma open_aexpr_fresh_rec : forall e n x v
  , x `notin` fv_aexpr (open_aexpr_wrt_aexpr_rec n v e)
  → x `notin` fv_aexpr e.
Proof.
  induction e; simpl; intros; eauto 4.
Qed.

Lemma open_aexpr_fresh : forall e x v,
  x `notin` fv_aexpr (e ^^′ v) → x `notin` fv_aexpr e.
Proof.
  intros. eauto using open_aexpr_fresh_rec.
Qed.

Lemma open_bexpr_fresh_rec : forall e n x v
  , x `notin` fv_bexpr (open_bexpr_wrt_bexpr_rec n v e)
  → x `notin` fv_bexpr e.
Proof.
  induction e; simpl; intros; eauto 4.
Qed.

Lemma open_bexpr_fresh : forall e x v,
  x `notin` fv_bexpr (e ^^' v) → x `notin` fv_bexpr e.
Proof.
  intros. eauto using open_bexpr_fresh_rec.
Qed.

Lemma fresh_open_aexpr_rec : forall e n x v
  , x `notin` fv_aexpr e → x `notin` fv_aexpr v
  → x `notin` fv_aexpr (open_aexpr_wrt_aexpr_rec n v e).
Proof.
  induction e; simpl; intros; eauto 4.
  - destruct (lt_eq_lt_dec n n0); try destruct s; auto.
Qed.

Lemma fresh_open_aexpr : forall e x v
  , x `notin` fv_aexpr e → x `notin` fv_aexpr v
  → x `notin` fv_aexpr (e ^^′ v).
Proof.
  intros. eauto using fresh_open_aexpr_rec.
Qed.

Lemma fresh_open_bexpr_rec : forall e n x v
  , x `notin` fv_bexpr e → x `notin` fv_bexpr v
  → x `notin` fv_bexpr (open_bexpr_wrt_bexpr_rec n v e).
Proof.
  induction e; simpl; intros; eauto 4.
  - destruct (lt_eq_lt_dec n n0); try destruct s; auto.
Qed.

Lemma fresh_open_bexpr : forall e x v
  , x `notin` fv_bexpr e → x `notin` fv_bexpr v
  → x `notin` fv_bexpr (e ^^' v).
Proof.
  intros. eauto using fresh_open_bexpr_rec.
Qed.

Lemma inst_e_fresh : forall Θ e' e x,
    Θ ⊩ e' ⇝ e → x `notin` fv_bexpr e → x `notin` fv_aexpr e'.
Proof.
  induction 1; simpl; intros;
    solve [ eauto 3
          | pick fresh x' for all;
            eauto 6 using open_aexpr_fresh, fresh_open_bexpr].
Qed.

Lemma fresh_inst_e : forall Θ e' e x,
    Θ ⊩ e' ⇝ e → x `notin` fv_aexpr e' → x `notin` fv_bexpr e.
Proof.
Admitted.

Lemma inst_wl_rename : forall Θ Θ' Γ' Γ x x'
  , Θ ⊩ Γ' ⟿ Γ ⫣ Θ' → x `notin` fv_ss_inst Θ'
    → Θ ⊩ subst_worklist (`′ x') x Γ' ⟿ subst_dworklist (`' x') x Γ ⫣
        Θ'.
Proof.
  intros * H.
  pattern Θ, Γ', Γ, Θ', H.
  apply wlinst_mut with
    (P := fun Θ w' w Θ' (_ : Θ ⊩ w' ⇝′ w ⫣ Θ')
      => x `notin` fv_ss_inst Θ' →
      Θ ⊩ subst_work (`′ x') x w' ⇝′ subst_dwork (`' x') x w ⫣ Θ');
    simpl; intros; eauto 6 with ln.
  - apply instw_infer with (add x L); eauto with rename_impl ln.
  - apply instw_iapp  with (add x L); eauto with rename_impl ln.
  - apply instw_red   with (add x L); eauto with rename_impl ln.
  - eauto with rename_impl.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma notin_open_bexpr_rec : forall x v e n
  , x `notin` fv_bexpr v → x `notin` fv_bexpr e
  → x `notin` fv_bexpr (open_bexpr_wrt_bexpr_rec n v e).
Proof.
  induction e; simpl; intros; auto.
  - destruct (lt_eq_lt_dec n n0); auto.
    destruct s; auto.
Qed.

Lemma notin_open_bexpr : forall x v e
  , x `notin` fv_bexpr v → x `notin` fv_bexpr e
  → x `notin` fv_bexpr (e ^^' v).
Proof.
  intros. now eapply notin_open_bexpr_rec.
Qed.

Lemma notin_close_bexpr_rec : forall x e n,
    x `notin` fv_bexpr (close_bexpr_wrt_bexpr_rec n x e).
Proof.
  induction e; simpl; intros; auto.
  - destruct (lt_ge_dec n n0); auto.
  - unfold eq_dec. destruct EqDec_eq_of_X; auto.
Qed.

Lemma notin_close_bexpr : forall x e,
    x `notin` fv_bexpr (close_bexpr_wrt_bexpr x e).
Proof.
  intros. apply notin_close_bexpr_rec.
Qed.

Hint Resolve notin_close_bexpr : atoms.
Hint Resolve notin_open_bexpr : atoms.

Hint Resolve inst_ae_lc : lc.
Hint Resolve inst_e_lc : lc.

Hint Rewrite close_bexpr_wrt_bexpr_open_bexpr_wrt_bexpr : ln.
Hint Rewrite <- subst_bexpr_close_bexpr_wrt_bexpr : ln.
Hint Rewrite open_bexpr_wrt_bexpr_close_bexpr_wrt_bexpr : ln.

Ltac e_rev_subst_apply_ih :=
  match goal with
  | IH : forall _ _ _, _ → _ ⊩ [?v /′ ?x] ?e ^`′ _ ⇝ _ → _
  , H  : _ ⊩ ([?v /′ ?x] ?e) ^`′ _ ⇝ ?e1 ^`' _ |- _ =>
    let e1' := fresh e1 in
    let E := fresh "E" in
    let H' := fresh "H" in
    rewrite aexpr_subst_open_comm in H; eauto 3 with lc;
    apply IH in H as (e1' & E & H'); auto with atoms
  | IH : forall _ _, _ → _ ⊩ [?v /′ ?x] ?e ⇝ _ → _
  , H  : _ ⊩ [?v /′ ?x] ?e ⇝ ?e1 |- _ =>
    let e1' := fresh e1 in
    let E := fresh "E" in
    let H' := fresh "H" in
    apply IH in H as (e1' & E & H'); auto with atoms
  end
.


Lemma bexpr_open_r_close_l : forall e1 e2 x,
    x `notin` fv_bexpr e2 → e1 = e2 ^`' x → e1 \`' x = e2.
Proof.
  intros * Fr H.
  assert (e1 \`' x = e2 ^`' x \`' x) by now rewrite H.
  now rewrite close_bexpr_wrt_bexpr_open_bexpr_wrt_bexpr in H0.
Qed.

Ltac pick_different x :=
  match goal with
  | x2 : atom |- _ =>
      lazymatch x2 with
      | x => fail
      | _ => constr:(x2)
      end
  end.

Ltac prepare_rename_impl :=
  match goal with
  | |- context [?e ^`' ?x] =>
      lazymatch goal with
      (* don't rename if it's wrapped inside other open or subst *)
      | |- context [e ^`' x ^`' ?x'] => fail
      | |- context [[`' ?x' /' x] e ^`' x] => fail
      | _ => let x1 := pick_different x in
            rewrite (subst_bexpr_intro x1)
      end
  | |- context [?e ^`′ ?x] =>
      lazymatch goal with
      | |- context [e ^`′ x ^`′ ?x'] => fail
      | |- context [[`′ ?x' /′ x] e ^`′ x] => fail
      | _ => let x1 := pick_different x in
            rewrite (subst_aexpr_intro x1)
      end
  end; auto 2 with atoms
.

Ltac prepare_rename := repeat prepare_rename_impl.

Lemma inst_e_rev_subst' : forall v' v x e'
  , lc_aexpr e' → forall e0 Θ,
      x `notin` (fv_aexpr v' `union` fv_ss_inst Θ)
  → Θ ⊩ [v' /′ x] e' ⇝ e0 → Θ ⊩ v' ⇝ v
  → exists e, [v /' x] e = e0 ∧ Θ ⊩ e' ⇝ e.
Proof.
  intros * Lc.
  induction Lc; simpl; intros * Fr He Hv;
    lazymatch type of He with
      (* only if it's a variable it doesn't invert the hypo *)
    | _ ⊩ (if _ then _ else _) ⇝ _ => idtac
    | _ ⊩ ⧼ ?k ⧽′ ⇝ _ => destruct k; inversion He; subst
    | _ => inversion He; subst; simpl in Fr;
          (* instantiate cofinite for those with binders *)
          inst_cofinites_by rev_subst_gather_atoms;
          repeat e_rev_subst_apply_ih
    end.
  - exists (`' x0). simpl.
    unfold eq_dec in *. destruct (EqDec_eq_of_X x0 x).
    + assert (v = e0) by (eapply inst_e_det with (Θ := Θ); eauto).
      eauto.
    + inversion He. now subst.
  - exists ⋆'; eauto.
  - exists ◻'; eauto.
  - exists ⧼ k ⧽'; eauto.
  - exists e0. eauto 4 with lngen atoms.
  - exists (be_num n); eauto.
  - exists be_int; eauto.
  - exists be_bot; eauto.
  - exists (be_app f0 a0); subst; auto.
  - exists (be_abs (e0 \`' x0)). split.
    + simpl. f_equal.
      rewrite subst_bexpr_close_bexpr_wrt_bexpr; eauto with lc.
      apply bexpr_open_r_close_l; auto.
    + apply inste_abs with L; intros.
      prepare_rename.
      apply inst_e_rename; autorewrite with ln; auto.
      admit.
  - exists (be_pi A1 (B1 \`' x0)). split.
    + simpl. f_equal. assumption.
      rewrite subst_bexpr_close_bexpr_wrt_bexpr; eauto with lc.
      apply bexpr_open_r_close_l; auto.
    + apply inste_pi with L; intros; auto.
      prepare_rename; apply inst_e_rename;
        autorewrite with ln; auto.
      admit.
  - exists (be_bind (e0 \`' x0)). split.
    + simpl. f_equal.
      rewrite subst_bexpr_close_bexpr_wrt_bexpr; eauto with lc.
      apply bexpr_open_r_close_l; auto.
    + apply inste_bind with L; intros; auto.
      prepare_rename. apply inst_e_rename; autorewrite with ln; auto.
      admit.
  - exists (be_all A1 (B1 \`' x0)). split.
    + simpl. f_equal. assumption.
      rewrite subst_bexpr_close_bexpr_wrt_bexpr; eauto with lc.
      apply bexpr_open_r_close_l; auto.
    + apply inste_all with L; intros; auto.
      prepare_rename; apply inst_e_rename;
        autorewrite with ln; auto.
      admit.
  - exists (be_castup e0); subst; auto.
  - exists (be_castdn e0); subst; auto.
  - exists (e0 ::' A1); subst; auto.
Admitted.

Lemma inst_e_rev_subst : forall e0 Θ v' v x e'
  , x `notin` (fv_aexpr v' `union` fv_ss_inst Θ)
  → Θ ⊩ v' ⇝ v → Θ ⊩ [v' /′ x] e' ⇝ e0
  → exists e, [v /' x] e = e0 ∧ Θ ⊩ e' ⇝ e.
Proof.
Admitted.

Scheme wl_lc_mut := Induction for lc_worklist Sort Prop
  with  w_lc_mut := Induction for lc_work Sort Prop.

Lemma inst_eq_inst_wl : forall Θ1 Θ' Γ' Γ
  , Θ1 ⊩ Γ' ⟿ Γ ⫣ Θ1 ;; Θ' → forall Θ2
  , wf_ss (Θ2 ;; Θ') → inst_set Θ1 = inst_set Θ2
  → Θ2 ⊩ Γ' ⟿ Γ ⫣ Θ2 ;; Θ'.
Proof.
  intros * H.
  remember (Θ1 ;; Θ') as Θ1'.
  generalize dependent Θ'.
  pattern Θ1, Γ', Γ, Θ1', H.
  apply wlinst_mut with
    (P := fun Θ1 w' w Θ1' (_ : Θ1 ⊩ w' ⇝′ w ⫣ Θ1') =>
      forall Θ', Θ1' = Θ1 ;; Θ' → forall Θ2
      , wf_ss (Θ2 ;; Θ') → inst_set Θ1 = inst_set Θ2
        → Θ2 ⊩ w' ⇝′ w ⫣ Θ2 ;; Θ'); intros; subst.
  - simplify_list_eq. eauto 6 with inst_eq.
  - simplify_list_eq. eauto with inst_eq.
  - eauto with wf_ss inst_eq.
  - eauto with wf_ss inst_eq. admit.
  - eauto with wf_ss inst_eq.

  - simplify_list_eq. auto.
  - conclude_ss_extend. simplify_list_eq.
    eauto with wf_ss inst_eq.
  - conclude_ss_extend. simplify_list_eq.
    inversion H1; subst.
    eauto with inst_eq.
  - conclude_ss_extend. simplify_list_eq.
    inversion H1; subst.
    constructor; eauto.
  - conclude_ss_extend. simplify_list_eq.
    inversion H1; subst.
    eauto with inst_eq.
Admitted.

Hint Resolve inst_eq_inst_wl : inst_eq.

Lemma inst_eq_inst_w : forall Θ1 Θ' w' w
  , Θ1 ⊩ w' ⇝′ w ⫣ Θ1 ;; Θ' → forall Θ2
  , wf_ss (Θ2 ;; Θ') → inst_set Θ1 = inst_set Θ2
  → Θ2 ⊩ w' ⇝′ w ⫣ Θ2 ;; Θ'.
Proof.
  intros * H.
  dependent induction H; simpl; intros.
  - simplify_list_eq. eauto 6 with inst_eq.
  - simplify_list_eq. eauto with inst_eq.
  - eauto 6 with wf_ss inst_eq.
  - eauto 6 with wf_ss inst_eq. admit.
  - eauto 6 with wf_ss inst_eq.
Admitted.

Lemma subst_ss_fresh_equal : forall e x Θ,
    x `notin` fv_ss_inst Θ → inst_set (subst_ss e x Θ) = inst_set Θ.
Proof.
  induction Θ; simpl; intros.
  - auto.
  - unfold fv_ss_inst in H. destruct a. destruct s; simpl in *;
    rewrite <- IHΘ; auto.
    rewrite subst_bexpr_fresh_eq; auto.
Qed.

Hint Rewrite subst_ss_fresh_equal : inst_notin.

Ltac simplify_inst_notin :=
  unfold fv_ss_inst in *; simpl in *;
  destruct_notin_ext;
  autorewrite with inst_notin in *.

Lemma inst_wl_rev_subst : forall Γ' e' e
  , lc_worklist Γ' → forall Γ0 x Θ Θ',
      x `notin` (fv_aexpr e' `union` fv_ss_inst (Θ ;; Θ'))
  → Θ ⊩ subst_worklist e' x Γ' ⟿ Γ0 ⫣ Θ ;; Θ'
  → Θ ⊩ e' ⇝ e
  → exists Γ Θ''
    , subst_dworklist e x Γ = Γ0
    ∧ subst_ss e x Θ'' = Θ'
    /\ x `notin` fv_ss_inst Θ''
    ∧ Θ ⊩ Γ' ⟿ Γ ⫣ Θ ;; Θ''.
Proof.
  intros * H.
  pattern Γ', H.
  apply wl_lc_mut with
    (P0 := fun w' (_ : lc_work w') =>
      forall x w0 Θ Θ'
      , x `notin` (fv_aexpr e' `union` fv_ss_inst (Θ ;; Θ'))
      → Θ ⊩ subst_work e' x w' ⇝′ w0 ⫣ Θ ;; Θ'
      → Θ ⊩ e' ⇝ e
      → exists w Θ''
        , subst_dwork e x w = w0
        ∧ subst_ss e x Θ'' = Θ'
        /\ x `notin` fv_ss_inst Θ''
        ∧ Θ ⊩ w' ⇝′ w ⫣ Θ ;; Θ''); simpl; intros.
  - dependent destruction H1. exists dwl_nil, nil; repeat split; auto.
    now simplify_list_eq.
  - dependent destruction H3.
    conclude_ss_extend; simplify_list_eq.
    apply H1 in H4 as (w0' & Θ1' & E' & E & Fr1 & H4); auto.
    apply H0 in H3 as (Γ0 & Θ0' & E1 & E2 & Fr2 & H3); auto; subst.
    + exists (Γ0 ⊨ w0'), (Θ0' ;; Θ1'); simpl; repeat split; eauto.
      * apply subst_ss_app_distr.
      * simplify_inst_notin; auto with inst_notin.
      * econstructor. eassumption.
        rewrite app_assoc.
        eapply inst_eq_inst_w; eauto 3.
        -- admit.
        -- repeat rewrite inst_set_app_distr.
           autorewrite with inst_notin; auto.
    + simplify_inst_notin; auto with inst_notin.
    + eauto with wf_ss inst_weakening.
  - destruct b; simpl in H2; inversion H2; subst.
    + conclude_ss_extend; simplify_list_eq.
      apply H0 in H10 as (Γ1 & Θ' & <- & <- & Fr & H10); simpl in H1; auto.
      assert (exists A0', [e /' x] A0' = A0 /\ Θ ;; Θ' ⊩ A ⇝ A0') as (A0' & E & ?).
      apply inst_e_rev_subst with e'; auto.
      * simplify_inst_notin. auto with inst_notin.
      * eauto with inst_weakening.
      * eapply inst_eq_inst_e.
        -- eassumption.
        -- eauto with wf_ss.
        -- repeat rewrite inst_set_app_distr.
           autorewrite with inst_notin; auto.
      * subst.
      exists (Γ1 ,′' x0 : A0'), (Θ'; x0 : A0'!); simpl; repeat split; auto.
        constructor; auto.
        simplify_inst_notin. auto with inst_notin.

    + conclude_ss_extend; simplify_list_eq.

      apply H0 in H11 as (Γ0' & Θ' & <- & <- & Fr & H11); simpl in H1; auto;
      simplify_inst_notin.
      assert (exists A0', [e /' x] A0' = A0 /\ Θ ;; Θ' ⊩ A ⇝ A0') as (A0' & E & ?).
      apply inst_e_rev_subst with e'; auto.
      * auto with inst_notin.
      * eauto with inst_weakening.
      * eapply inst_eq_inst_e; eauto with wf_ss.
        -- repeat rewrite inst_set_app_distr.
           autorewrite with inst_notin; auto.
      * subst.
        exists Γ0', (Θ'; ex : A0' ≔ e0); simpl; repeat split.
        -- rewrite (subst_bexpr_fresh_eq e0); auto.
        -- auto with inst_notin.
        -- constructor; auto.
      * auto with inst_notin.
    + conclude_ss_extend; simplify_list_eq.
      apply H0 in H9 as (Γ0' & Θ' & <- & <- & Fr & H9); simpl in H1; auto;
        simplify_inst_notin.
      * exists Γ0', (Θ'; kx ≔ ⧼ k ⧽); simpl; repeat split; auto.
      * auto with inst_notin.

  - dependent destruction H1.
    simplify_list_eq.
    eapply inst_e_rev_subst in H2 as (A' & <- & H2); eauto.
    eapply inst_e_rev_subst in H3 as (e1' & <- & H3); eauto.
    eapply inst_e_rev_subst in H4 as (e2' & <- & H4); eauto.
    destruct ob; dependent destruction H1.
    + exists (e1' <: e2' ⇐ A'), nil; repeat split; auto.
    + eapply inst_e_rev_subst in H1 as (A2' & <- & H1); eauto.
      exists (x1 :? A2' ⊢? e1' <: e2' ⇐ A'), nil; repeat split; auto.
  - dependent destruction H2.
    simplify_inst_notin.
    eapply inst_e_rev_subst in H2 as (e0' & <- & H2); eauto with inst_notin.
    eapply inst_e_rev_subst in H3 as (e3' & <- & H3); eauto with inst_notin.
    pick fresh x' for all. inst_cofinites_with x'.
    rewrite worklist_subst_open_comm in H4; eauto with lc.
    eapply H0 in H4 as (c' & Θ'' & E1 & <- & Fr2 & H4).
    exists (e0' <: e3' ⇒ close_dworklist_wrt_bexpr x' c'), Θ''; simpl; repeat split.
    + replace c with (subst_dworklist e x (close_dworklist_wrt_bexpr x' c')). auto.
      rewrite subst_dworklist_close_dworklist_wrt_bexpr; eauto with lc.
      rewrite E1, close_dworklist_wrt_bexpr_open_dworklist_wrt_bexpr;
        eauto.
    + assumption.
    + pick fresh x'' and apply instw_infer; eauto.
      rewrite (subst_worklist_intro x').
      rewrite (subst_dworklist_intro x').
      apply inst_wl_rename. rewrite open_dworklist_wrt_bexpr_close_dworklist_wrt_bexpr.

      * auto.
      * admit.
      * admit.
      * auto.
    + auto with inst_notin.
    + auto.
  - dependent destruction H2.
    simplify_inst_notin.
     eapply inst_e_rev_subst in H2 as (e1' & E1 & H2); eauto with inst_notin.
    eapply inst_e_rev_subst in H3 as (e2' & E2 & H3); eauto with inst_notin.
    admit.
  - dependent destruction H2.
    simplify_inst_notin.
    eapply inst_e_rev_subst in H2 as (A' & <- & H2); eauto with inst_notin.
    pick fresh x' for all. inst_cofinites_with x'.
    rewrite worklist_subst_open_comm in H3; eauto with lc.
    eapply H0 in H3 as (c' & Θ'' & E1 & <- & Fr2 & H3); auto with inst_notin.
    exists (A' ⟼ close_dworklist_wrt_bexpr x' c'), Θ''; simpl; repeat split.
    + replace c with (subst_dworklist e x (close_dworklist_wrt_bexpr x' c')). auto.
      rewrite subst_dworklist_close_dworklist_wrt_bexpr; eauto with lc.
      rewrite E1, close_dworklist_wrt_bexpr_open_dworklist_wrt_bexpr;
        eauto.
    + auto.
    + pick fresh x'' and apply instw_red; eauto. intros.
      rewrite (subst_worklist_intro x').
      rewrite (subst_dworklist_intro x').
      apply inst_wl_rename. rewrite open_dworklist_wrt_bexpr_close_dworklist_wrt_bexpr.
      auto. all: admit.

  - dependent destruction H1. simplify_list_eq.
    eapply inst_e_rev_subst in H1 as (A0' & <- & H1); eauto.
    eapply inst_e_rev_subst in H2 as (B0' & <- & H2); eauto.
    exists (A0' ≲ B0'), nil; repeat split; auto.
Admitted.
