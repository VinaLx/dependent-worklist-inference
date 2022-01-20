Require Import transfer.syntax.
Require Import lc.
Require Import Program.Equality.
Require Import list_properties.

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
  - exists Γ, dwl_nil, Θ'; simpl; auto.
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

Scheme winst_mut   := Induction for inst_work Sort Prop
  with wlinst_mut := Induction for inst_wl   Sort Prop.

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

Lemma inst_ob_weakening : forall Θ1 Θ2 Θ' ob' ob,
  Θ1 ;; Θ2 ⊩ ob' ⇝? ob → Θ1 ;; Θ' ;; Θ2 ⊩ ob' ⇝? ob.
Proof.
  induction 1; eauto.
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
      rewrite (app_assoc ys1 ys2 xs) in H
  | H : ?zs ++ ?xs = ?ys1 ++ ?ys2 ++ ?xs |- _ =>
      symmetry in H
  | H : ?x :: ?ys ++ ?xs = ?zs ++ ?xs |- _ =>
      rewrite <- (cons_app_assoc _ x ys xs) in H;
      clear_app_suffix_impl
  end; simpl in *
.

Ltac clear_app_suffix :=
  repeat progress clear_app_suffix_impl.

Ltac simplify_list_eq :=
  repeat (subst || clear_app_suffix);
  repeat rewrite <- app_assoc in *;
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
  - eauto with inst_weakening.
  - eauto with inst_weakening.

  (* inst_wl *)
  - clear_app_suffix. auto.
  - conclude_ss_extend. simplify_list_eq.
    eapply instwl_cons.
    + eauto with inst_weakening.
    + replace (Θ1;; Θ'1;; Θ2;; Θ0;; Θ4) with
        (Θ1;; Θ'1;; (Θ2;; Θ0);; Θ4) by
        now repeat rewrite <- app_assoc.
    rewrite (app_assoc Θ0 Θ2 (Θ1 ;; Θ'1)).
    apply H1; eauto 4; rewrite <- app_assoc; auto.
  - conclude_ss_extend; simplify_list_eq.
    inversion H1; subst; constructor; auto.
    + rewrite app_assoc; apply inst_e_weakening;
      now rewrite <- app_assoc.
  - conclude_ss_extend; simplify_list_eq.
    inversion H1; subst. constructor; auto.
  - conclude_ss_extend; simplify_list_eq.
    inversion H1; subst. constructor; auto.
    + rewrite app_assoc; apply inst_e_weakening;
       now rewrite <- app_assoc.
Qed.

Hint Resolve inst_wl_weakening : inst_weakening.

Lemma inst_w_weakening : forall Θ1 Θ2 Θ3 w' w
  , Θ1 ;; Θ2 ⊩ w' ⇝′ w ⫣ Θ1 ;; Θ2 ;; Θ3
  → forall Θ', wf_ss (Θ1;; Θ';; Θ2 ;; Θ3)
  → Θ1 ;; Θ' ;; Θ2 ⊩ w' ⇝′ w ⫣ Θ1 ;; Θ' ;; Θ2 ;; Θ3.
Proof.
  intros * H.
  dependent induction H; intros;
    clear_app_suffix; eauto 6 with inst_weakening.
Qed.

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


Lemma bexpr_subst_open_var_comm : forall x1 x2 v e
  , lc_bexpr v → x1 <> x2
  → ([v /' x1] e) ^`' x2 = [v /' x1] e ^`' x2.
Proof.
  intros. rewrite bexpr_subst_open_comm; auto.
Qed.

Hint Rewrite bexpr_subst_open_comm aexpr_subst_open_comm : ln.
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

Lemma inst_e_rename : forall Θ e' e x x'
  , Θ ⊩ e' ⇝ e → x `notin` fv_ss Θ
  → Θ ⊩ [`′ x' /′ x] e' ⇝ [`' x' /' x] e.
Proof.
  intros; induction H; simpl; auto.
  - unfold eq_dec. destruct (EqDec_eq_of_X x0 x); auto.
  - rewrite subst_bexpr_fresh_eq.
    + eauto.
    + eapply notin_ss_sse with (e := sse_ex A e) in H0;
        simpl in *; eauto.
  - apply inste_abs  with (add x L); eauto with ln.
  - apply inste_bind with (add x L); eauto with ln.
  - apply inste_pi   with (add x L); eauto with ln.
  - apply inste_all  with (add x L); eauto with ln.
Qed.

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

Ltac rev_subst_gather_atoms :=
  let L0 := gather_atoms_with (fun x : atom => {{ x }}) in
  let L1 := gather_atoms_with (fun x : atoms => x) in
  let L2 := gather_atoms_with (fun x : bexpr => fv_bexpr x) in
  let L3 := gather_atoms_with (fun x : aexpr => fv_aexpr x) in
  let L4 := gather_atoms_with (fun x : subst_set => fv_ss x) in
  constr:(L0 `union` L1 `union` L2 `union` L3 `union` L4).

Tactic Notation "pick" "fresh" ident(x) "for" "all" :=
  let L  := rev_subst_gather_atoms in
  pick fresh x for L.

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

Ltac inst_cofinite_impl H x :=
  match type of H with
  | forall x, x `notin` ?L -> _ =>
      let Fr := fresh "Fr" in
      assert (x `notin` L) as Fr by auto;
      specialize (H x Fr); clear Fr
  end
.

Ltac inst_cofinites_with x :=
  repeat
    match goal with
    | H : forall x0, x0 `notin` ?L → _ |- _ =>
      inst_cofinite_impl H x
    end
.

Ltac inst_cofinites :=
  match goal with
  | x : atom |- _ => inst_cofinites_with x
  end.

Ltac inst_cofinites_with_new :=
  let x := fresh "x" in
  pick fresh x; inst_cofinites_with x.

Ltac inst_cofinites_by F :=
  let L := F in
  let x := fresh "x" in
  pick fresh x for L; inst_cofinites_with x.


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

Lemma inst_e_rev_subst : forall v' v x e'
  , lc_aexpr e' → forall e0 Θ, x `notin` fv_bexpr e0
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
  - exists e0. eauto with lngen.
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
  - exists (be_pi A1 (B1 \`' x0)). split.
    + simpl. f_equal. assumption.
      rewrite subst_bexpr_close_bexpr_wrt_bexpr; eauto with lc.
      apply bexpr_open_r_close_l; auto.
    + apply inste_pi with L; intros; auto.
      prepare_rename; apply inst_e_rename;
        autorewrite with ln; auto.
  - exists (be_bind (e0 \`' x0)). split.
    + simpl. f_equal.
      rewrite subst_bexpr_close_bexpr_wrt_bexpr; eauto with lc.
      apply bexpr_open_r_close_l; auto.
    + apply inste_bind with L; intros; auto.
      prepare_rename. apply inst_e_rename; autorewrite with ln; auto.
  - exists (be_all A1 (B1 \`' x0)). split.
    + simpl. f_equal. assumption.
      rewrite subst_bexpr_close_bexpr_wrt_bexpr; eauto with lc.
      apply bexpr_open_r_close_l; auto.
    + apply inste_all with L; intros; auto.
      prepare_rename; apply inst_e_rename;
        autorewrite with ln; auto.
  - exists (be_castup e0); subst; auto.
  - exists (be_castdn e0); subst; auto.
  - exists (e0 ::' A1); subst; auto.
Qed.

Scheme wl_lc_mut := Induction for lc_worklist Sort Prop
  with  w_lc_mut := Induction for lc_work Sort Prop.

Lemma inst_wl_rev_subst : forall Γ' x e' e
  , lc_worklist Γ' → forall Γ0 Θ Θ', x `notin` fv_dworklist Γ0
  → Θ ⊩ subst_worklist e' x Γ' ⟿ Γ0 ⫣ Θ'
  → Θ ⊩ e' ⇝ e
  → exists Γ
    , subst_dworklist e x Γ = Γ0
    ∧ Θ ⊩ Γ' ⟿ Γ ⫣ Θ'.
Proof.
  intros * H.
  pattern Γ', H.
  apply wl_lc_mut with
    (P0 := fun w' (_ : lc_work w') =>
      forall x w0 Θ Θ'
      , x `notin` fv_dwork w0
      → Θ ⊩ subst_work e' x w' ⇝′ w0 ⫣ Θ'
      → Θ ⊩ e' ⇝ e
      → exists w, subst_dwork e x w = w0 ∧ Θ ⊩ w' ⇝′ w ⫣ Θ'); simpl; intros.
  - inversion H1; subst. exists dwl_nil; simpl; split; auto.
  - inversion H3; subst. simpl in H2.
    apply H0 in H8; auto. apply H1 in H11; auto.
(*
  simpl; intros.
  - inversion H; subst.
    exists dwl_nil; simpl; repeat split; auto.
  - simpl in H1. inversion H1; subst. admit.
  - destruct b; inversion H0; subst; simpl in *; admit.
  - admit.
  -
*)
Admitted.
