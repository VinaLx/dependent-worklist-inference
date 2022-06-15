Require Import Program.Tactics.
Require Import Program.Equality.

Require Import decl.notations.
Require Export bidir.notations.
Require Import bidir.elaboration.
Require Import ln_utils.


Lemma busub_context_is_wf : forall Γ e1 e2 d A,
    busub Γ e1 e2 d A -> wf_bcontext Γ.
Proof.
  intros; induction H; auto.
Qed.


Lemma ge_box_absurd : forall Γ A d B,
    ~ busub Γ ◻' A d B.
Proof.
  intros. intro.
  dependent induction H; auto.
Qed.

Lemma le_k_star : forall Γ e1 k d A,
  busub Γ e1 ⧼ k ⧽' d A → e1 = ⋆' /\ k = bk_star /\ A = ◻'.
Proof.
  intros.
  dependent induction H.
  - auto.
  - destruct IHbusub3 with k as (? & ? & ?); solve [auto | discriminate].
  - destruct (IHbusub1 k eq_refl) as (-> & -> & ->).
    apply ge_box_absurd in H0 as [].
Qed.

Inductive head_bk : bexpr → bkind → Prop :=
| hbk_k : forall k, head_bk ⧼ k ⧽' k
| hbk_pi  : forall k A B, head_bk B k → head_bk (be_pi A B) k
| hbk_all : forall k A B, head_bk B k → head_bk (be_all A B) k
.

Definition head_bbox (e : bexpr) := head_bk e bk_box.

#[local]
Hint Unfold head_bbox : core.

#[local]
Hint Constructors head_bk : core.

Lemma open_head_bk_rec : forall e1 e2 k n,
    head_bk e1 k → head_bk (open_bexpr_wrt_bexpr_rec n e2 e1) k.
Proof.
  induction e1; simpl; intros;
    solve [inversion H; eauto].
Qed.

Lemma open_head_bk : forall e1 e2 k,
    head_bk e1 k → head_bk (e1 ^^' e2) k.
Proof with eauto using open_head_bk_rec.
  idtac...
Qed.

#[local]
Hint Resolve open_head_bk : kind.

Lemma ge_head_box_absurd : forall Γ e1 e2 d A,
    busub Γ e1 e2 d A → head_bbox e1 → False.
Proof.
  induction 1; intro Absurd; inversion Absurd; subst;
    try solve [pick fresh x; eauto using open_head_bk].
Qed.

#[local]
Hint Resolve ge_head_box_absurd : kind.

Lemma le_head_box_absurd : forall Γ e1 e2 d A,
    busub Γ e1 e2 d A → head_bbox e2 → False.
Proof.
  induction 1; intro Absurd; inversion Absurd; subst;
    try solve [pick fresh x; eauto using open_head_bk].
Qed.

#[local]
Hint Resolve le_head_box_absurd : kind.

Lemma head_bk_open_rec : forall e1 e2 k n
  , head_bk (open_bexpr_wrt_bexpr_rec n e2 e1) k
  → head_bk e1 k ∨ head_bk e2 k.
Proof.
  induction e1; simpl; intros e2 k0 n0 HBK; try solve [inversion HBK | eauto].
  - destruct (lt_eq_lt_dec n n0) as [[|]|]; try solve [inversion HBK | eauto].
  - dependent destruction HBK.
    apply IHe1_2 in HBK as [|]; auto.
  - dependent destruction HBK.
    apply IHe1_2 in HBK as [|]; auto.
Qed.

Lemma head_bk_open : forall e1 e2 k,
    head_bk (e1 ^^' e2) k → head_bk e1 k ∨ head_bk e2 k.
Proof with eauto using head_bk_open_rec.
  idtac...
Qed.

#[local]
Hint Resolve head_bk_open : kind.

Lemma infer_app_head_box : forall Γ A B C,
    Γ ⊢ A ⇒Π B, C → head_bbox C → head_bbox A.
Proof.
  intros. dependent induction H.
  - auto.
  - apply IHinfer_app with (B1 := B) in H2; auto.
    apply head_bk_open in H2 as [|].
    + auto.
    + apply le_head_box_absurd in H0; [contradiction | auto].
Qed.


Lemma infer_head_box : forall Γ e1 e2 d A,
    busub Γ e1 e2 d A → head_bk A bk_box → A = ◻'.
Proof.
  induction 1; intros Box;
    try solve
      [inversion Box; subst;
       solve [auto 3
             | exfalso; eauto 2 with kind]].
  - induction H0; dependent destruction H;
      solve [auto | exfalso; eauto with kind].
  - inst_cofinites_with_new. dependent destruction Box.
    exfalso. eauto with kind.
  - pose proof (H' := H1). apply infer_app_head_box in H1.
    + apply IHbusub1 in H1 as ->. inversion H'.
    + apply head_bk_open in Box as [|]; auto.
      exfalso. eauto using le_head_box_absurd.
  - inst_cofinites_with_new. dependent destruction Box.
    exfalso. eauto with kind.
Qed.

Lemma check_k_infer : forall Γ e1 e2 k,
    Γ ⊢ e1 <: e2 ⇐ ⧼k⧽' → Γ ⊢ e1 <: e2 ⇒ ⧼k⧽'.
Proof.
  intros.
  dependent induction H.
  - auto.
  - eauto.
  - now apply le_k_star in H0 as (-> & -> & E).
Qed.

#[export]
Hint Immediate check_k_infer : core.

Lemma bctx_app_cons : forall Γ1 Γ2 x A,
    Γ1 ,,' Γ2 ,' x : A = Γ1 ,,' (Γ2 ,' x : A).
Proof.
  auto.
Qed.

Hint Rewrite bctx_app_cons : bctx.

Lemma weakening_auto_helper : forall Γ1 Γ2 x A,
    ⊢ Γ1 ,, Γ2 , x : A -> ⊢ Γ1 ,, (Γ2 , x : A).
Proof.
  auto.
Qed.


Lemma check_sub_invert : forall Γ e1 e2 A,
  Γ ⊢ e1 <: e2 ⇐ A ->
  A = ◻' \/ exists B k, Γ ⊢ B <: A ⇒ ⧼ k ⧽' /\ Γ ⊢ e1 <: e2 ⇒ B.
Proof.
  intros. dependent induction H; eauto.
Admitted.


Scheme  bwf_context_lc_mut     := Induction for wf_bcontext Sort Prop
  with  busub_bwf_lc_mut       := Induction for busub       Sort Prop
  with  infer_app_bwf_lc_mut   := Induction for infer_app   Sort Prop.


Lemma bwf_lc : forall Γ',
  ⫦ Γ' -> lc_bcontext Γ'.
Proof.
  intros.
  pattern Γ', H.
  eapply bwf_context_lc_mut with
  (P0 := fun Γ' e1' e2' d A' (_ : busub Γ' e1' e2' d A') =>
    lc_bexpr e1' /\ lc_bexpr e2' /\ lc_bexpr A'
  )
  (P1 := fun Γ' A' F' (_ : infer_app Γ' A' F') =>
    match F' with
    | fun_pi B C => forall x, lc_bexpr (C ^^' `'x)
    end
  );
  intros; try (intuition; fail); repeat split; auto; try solve_lc_bexpr.
  - induction i; auto. dependent destruction H0. dependent destruction w. auto.
  - intuition.
  - intuition.
  - dependent destruction l0. auto.
Qed.

Scheme  busub_lc_mut           := Induction for busub       Sort Prop
  with  infer_app_busub_lc_mut := Induction for infer_app   Sort Prop.

Lemma busub_all_lc : forall Γ' e1' e2' d' A',
  busub Γ' e1' e2' d' A' -> lc_bcontext Γ' /\ lc_bexpr e1' /\ lc_bexpr e2' /\ lc_bexpr A'.
Proof.
  intros.
  pattern Γ', e1', e2', d', A', H.
  eapply busub_lc_mut with
  (P0 := fun Γ' A' F' (_ : infer_app Γ' A' F') =>
    match F' with
    | fun_pi B C => forall x, lc_bexpr (C ^^' `'x)
    end
  );
  try (intuition; fail); repeat split; auto; try solve_lc_bexpr; intuition.
  + eapply bwf_lc; eauto.
  + induction i; auto. dependent destruction w.  auto.
  + eapply bwf_lc; eauto.
  + eapply bwf_lc; eauto.
  + eapply bwf_lc; eauto.
  + dependent destruction l0. auto.
Qed.

Scheme busub_refl_mut := Induction for busub     Sort Prop
  with  iapp_refl_mut := Induction for infer_app Sort Prop.


Theorem bidir_refl_l : forall Γ e1 e2 d A,
  busub Γ e1 e2 d A -> busub Γ e1 e1 d A.
Proof.
  intros; induction H; eauto.
Qed.

Hint Resolve bidir_refl_l : bidir.


Lemma lc_binsert_middle : forall Γ1 Γ2 Γ3,
    lc_bcontext Γ2 -> lc_bcontext (Γ1,,'Γ3) -> lc_bcontext (Γ1,,'Γ2,,'Γ3).
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

Lemma lc_bmiddle : forall Γ1 Γ2 Γ3,
    lc_bcontext (Γ1,,'Γ2,,'Γ3) -> lc_bcontext Γ2.
Proof.
  intros.
  induction Γ3.
  - induction Γ2; simpl in *. auto.
    inversion H. constructor; auto.
  - inversion H. auto.
Qed.

Lemma in_bctx_weakening : forall Γ1 Γ2 Γ3 x A,
    lc_bcontext Γ2 -> in_bctx x A (Γ1 ,,' Γ3) -> in_bctx x A (Γ1 ,,' Γ2 ,,' Γ3).
Proof.
  intros.
  induction Γ3.
  - induction Γ2.
    + auto.
    + inversion H. simpl in *. econstructor; auto.
  - simpl in *. inversion H0. subst.
    + apply inb_here. 2: auto. apply lc_binsert_middle; auto.
    + apply inb_there. auto. apply IHΓ3. auto.
Qed.

Scheme  busub_weakening_mut     := Induction for busub       Sort Prop
  with  greduce_weakening_mut   := Induction for greduce     Sort Prop
  with  infer_app_weakening_mut := Induction for infer_app   Sort Prop.

Ltac weakening_auto :=
  match goal with
  | x : atom |- _ =>
    repeat
    match goal with
    | H : x `notin` union ?L ?dom |- _ =>
      match goal with
      | H1 : forall x, x `notin` ?L ->
              forall Γ4 Γ2 Γ5, _ -> bctx_cons (?Γ1 ,,' ?Γ3) x ?A = Γ5 ,,' Γ4 -> _ |- _ =>
        match goal with
        | H2 : ⫦ ?Γ1,,' ?Γ2,,' ?Γ3 |- _ =>
        assert (⫦ Γ1,,' Γ2,,' Γ3,' x:A) as Hwfx by eauto;
        apply notin_union_1 in H as HnotinL;
        specialize (H1 x HnotinL (Γ3,'x:A) Γ2 Γ1 Hwfx (eq_refl (Γ1,,'Γ3,'x:A)));
        eauto 3;
        clear HnotinL; clear Hwfx
        end
      end
    end
  end.

Theorem bidir_weakening : forall Γ1 Γ2 Γ3 e1 e2 d A,
  busub (Γ1,,'       Γ3) e1 e2 d A -> ⫦ Γ1 ,,' Γ2 ,,' Γ3 ->
  busub (Γ1,,' Γ2,,' Γ3) e1 e2 d A.
Proof.
  intros. remember (Γ1,,' Γ3) as Γ.
  generalize dependent HeqΓ. generalize dependent Γ1. generalize dependent Γ2. generalize dependent Γ3.
  pattern Γ, e1, e2, d, A, H.

  eapply busub_weakening_mut with
  (P0 := fun Γ A B (_ : Γ ⊢ A ⟼ B) =>
    forall Γ1 Γ2 Γ3,
    ⫦ Γ1,,' Γ2,,' Γ3 -> Γ = Γ1,,' Γ3 ->
    Γ1,,' Γ3 ⊢ A ⟼ B ->
    Γ1,,' Γ2,,' Γ3 ⊢ A ⟼ B
  )
  (P1 := fun Γ A F (_ : infer_app Γ A F) =>
    forall Γ1 Γ2 Γ3,
    ⫦ Γ1,,' Γ2,,' Γ3 -> Γ = Γ1,,' Γ3 ->
    infer_app (Γ1,,'Γ3) A F ->
    infer_app (Γ1,,'Γ2,,'Γ3) A F
  ); intros; auto; subst.

  (** busub **)
  - constructor. auto. eapply in_bctx_weakening; auto.
    eapply lc_bmiddle. apply bwf_lc. eauto.
  - econstructor; eauto.
  - eapply bs_abs with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros; weakening_auto. admit. admit. admit.
  - eapply bs_pi with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros.
    + weakening_auto.
    + specialize (H1 Γ3 Γ2 Γ1 H4). apply bidir_refl_l in H1. weakening_auto. auto.
  - eauto.
  - eapply bs_bind with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros; weakening_auto. admit. admit. admit.
  - eauto.
  - eauto.
  - eapply bs_forall_l with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros; weakening_auto.
  - eapply bs_forall_r with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros; weakening_auto.
  - eapply bs_forall with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros.
    specialize (H0 Γ3 Γ2 Γ1 H3 (eq_refl (Γ1,,'Γ3))). apply bidir_refl_l in H0.
    weakening_auto.
  - eauto.
  - eauto.

  (** greduce **)
  - dependent destruction H2.
    + apply gr_reduce; auto. apply bwf_lc. auto.
    + econstructor. apply bwf_lc. auto. auto.
  - eapply gr_all with (t:=t); auto.

  (** infer_app **)
  - econstructor; eauto. apply bwf_lc. eauto.
  - dependent destruction H4.
    intros. eapply iapp_all with (t:=t); eauto.
Admitted.

Corollary bidir_weakening_cons : forall Γ x A e1 e2 d B,
    busub Γ e1 e2 d B → ⫦ Γ,' x : A → busub (Γ,' x : A) e1 e2 d B.
Proof.
  intros.
  replace (Γ,' x : A) with (Γ ,,' (bctx_nil ,' x : A) ,,' bctx_nil)
    by now simpl.
  now apply bidir_weakening.
Qed.


Lemma infer_k_check : forall Γ e1 e2 k,
    Γ ⊢ e1 <: e2 ⇒ ⧼k⧽' → Γ ⊢ e1 <: e2 ⇐ ⧼k⧽'.
Proof.
  intros.
  dependent induction H; eauto 4.
  - induction H0; inversion H; subst; eauto using bidir_weakening_cons.
  - apply le_k_star in H0 as (-> & -> & ?). eauto.
  - destruct k.
    + rewrite <- x.
      eapply bs_sub with (A := C ^^' t).
      eauto. rewrite x. eauto using busub_context_is_wf.
    + assert (head_bbox (C ^^' t)). rewrite x. eauto.
      apply head_bk_open in H3 as [|].
      * pose proof (H' := H1).
        apply infer_app_head_box in H1; try assumption.
        apply infer_head_box in H0; try assumption; subst.
        inversion H'.
      * exfalso; eauto with kind.
  - apply le_k_star in H0 as (-> & -> & ?). eauto.
  - eauto using busub_context_is_wf.
  - eauto using busub_context_is_wf.
  - eauto using busub_context_is_wf.
  - apply le_k_star in H1 as (-> & -> & ?). eauto.
Qed.

#[export]
Hint Immediate infer_k_check : core.

Theorem bidir_weakening' : forall Γ1 Γ2 Γ3 e1 e2 d A,
  busub (Γ1,,'       Γ3) e1 e2 d A -> ⫦ Γ1 ,,' Γ2 ,,' Γ3 ->
  busub (Γ1,,' Γ2,,' Γ3) e1 e2 d A.
Proof with autorewrite with bctx; eauto.
  intros. remember (Γ1,,' Γ3) as Γ.
  generalize dependent HeqΓ. generalize dependent Γ3.
  pattern Γ, e1, e2, d, A, H.

  eapply busub_weakening_mut with
  (P0 := fun Γ A B (_ : Γ ⊢ A ⟼ B) =>
    forall Γ3,
    Γ = Γ1,,' Γ3 ->
    Γ1,,' Γ2,,' Γ3 ⊢ A ⟼ B
  )
  (P1 := fun Γ A F (_ : infer_app Γ A F) =>
    forall Γ3,
    Γ = Γ1,,' Γ3 ->
    infer_app (Γ1,,'Γ2,,'Γ3) A F
  ); intros; auto; subst.

  (** busub **)
  - constructor. auto. eapply in_bctx_weakening; auto.
    eapply lc_bmiddle. apply bwf_lc. eauto.
  - econstructor; eauto.
  - eapply bs_abs with (L:=L); eauto; intros; inst_cofinites_with x. eauto... admit. admit. admit.
Admitted.


Lemma bctx_dom_narrowing_eq : forall Γ1 Γ2 x A B,
  bctx_dom (Γ1,' x : A,,' Γ2) = bctx_dom (Γ1,' x : B,,' Γ2).
intros.
  induction Γ2.
  - auto.
  - simpl. rewrite IHΓ2. auto.
Qed.

Hint Rewrite bctx_dom_narrowing_eq : bctx.


Lemma bidir_narrowing_lc_helper : forall Γ1 Γ2 x A B k,
  lc_bcontext (Γ1,' x : B,,' Γ2) ->
  Γ1 ⊢ A <: B ⇒ ⧼ k ⧽' ->
  lc_bcontext (Γ1,' x : A,,' Γ2).
Proof.
  intros.
  replace (Γ1,' x : B,,' Γ2) with (Γ1,' x : B,,' Γ2,,' bctx_nil) in H by auto.
  apply lc_bmiddle in H.
  replace (Γ1,' x : A,,' Γ2) with (Γ1,' x : A,,' Γ2,,' bctx_nil) by auto.
  apply lc_binsert_middle; apply busub_all_lc in H0; simpl; intuition.
Qed.

Scheme  busub_narrowing_mut       := Induction for busub       Sort Prop
  with  wf_bcontext_narrowing_mut := Induction for wf_bcontext Sort Prop
  with  greduce_narrowing_mut     := Induction for greduce     Sort Prop
  with  infer_app_narrowing_mut   := Induction for infer_app   Sort Prop.


(* Theorem bidir_narrowing : forall Γ1 x B Γ2 e1 e2 d C,
  busub (Γ1,' x : B,,' Γ2) e1 e2 d C ->
  forall A k, Γ1 ⊢ A <: B ⇒ ⧼ k ⧽' ->
  busub (Γ1,' x : A,,' Γ2) e1 e2 d C.
Proof with autorewrite with bctx; eauto.
  intros. remember (Γ1,' x : B,,' Γ2) as Γ.
  generalize dependent HeqΓ. generalize dependent Γ2.
  pattern Γ, e1, e2, d, C, H.

  eapply busub_narrowing_mut with
  (P := fun Γ e1 e2 d C (_ : busub Γ e1 e2 d C) =>
    forall Γ2,
     Γ = Γ1 ,' x : B ,,' Γ2 ->
     busub (Γ1 ,' x : A ,,' Γ2) e1 e2 d C
  )
  (P0 := fun Γ (_ : wf_bcontext Γ) =>
    forall Γ2,
      Γ = Γ1,' x : B,,' Γ2 ->
      ⫦ Γ1,' x : A,,' Γ2
  )
  (P1 := fun Γ C D (_ : Γ ⊢ C ⟼ D) =>
    forall Γ2,
      Γ = Γ1,' x:B,,' Γ2 ->
      Γ1,' x : A,,' Γ2 ⊢ C ⟼ D
  )
  (P2 := fun Γ C F (_ : infer_app Γ C F) =>
    forall Γ2,
      Γ = Γ1,' x:B,,' Γ2 ->
      infer_app (Γ1,' x : A,,' Γ2) C F
  )
  ; intros; auto; subst.
  - destruct (x==x0).
    + subst. assert (A0=B) by admit. subst. econstructor. admit. admit.
    + econstructor. admit. admit.
  - eauto.
  - eapply bs_abs with (L:=L); eauto; intros; inst_cofinites_with x0; eauto...
  - eapply bs_pi with (L:=L); eauto; intros; inst_cofinites_with x0; eauto...
  - eauto.
  - eapply bs_bind with (L:=L); eauto; intros; inst_cofinites_with x0; eauto...
  - eauto.
  - eauto.
  - eapply bs_forall_l with (L:=L); eauto; intros; inst_cofinites_with x0; eauto...
  - eapply bs_forall_r with (L:=L); eauto.
    intros. inst_cofinites_with x. eauto...
  - eapply bs_forall with (L:=L); eauto; intros.
    inst_cofinites_with x. eauto...
  - eauto.
  - eauto.

  (* P0 *)
  - destruct Γ2; inversion H1.
  - destruct Γ2.
    + dependent destruction H3. simpl. econstructor; auto.
      eapply bidir_refl_l in H0. eauto.
    + dependent destruction H3. simpl. econstructor; eauto.
      replace (bctx_dom (Γ1,' x : A,,' Γ2)) with (bctx_dom (Γ1,' x : B,,' Γ2)); auto.
      eapply bctx_dom_narrowing_eq.

  (* P1 *)
  - admit.
  (* dependent destruction b; econstructor; eauto; eapply bidir_narrowing_lc_helper; eauto. *)
  - eapply gr_all; eauto.

  (* P2 *)
  - econstructor; eauto. eapply bidir_narrowing_lc_helper; eauto.
  - econstructor; eauto.
Admitted.


Hint Resolve bidir_narrowing : bidir. *)
