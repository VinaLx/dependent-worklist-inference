Require Import transfer.syntax.
Require Import lc.
Require Import Program.Equality.
Require Import list_properties.
Require Import alg.ln_inf_extra.
Require Import bidir.ln_inf_extra.
Require Import ln_utils.

Hint Extern 2 (_ = _) => simpl; congruence : core.

Lemma fresh_dom_fresh_ctx : forall x Θ,
    x `notin` dom Θ → x `notin` bctx_dom ⌊ Θ ⌋′.
Proof.
  induction Θ; simpl; intros.
  - auto.
  - destruct a. destruct s; auto.
Qed.

Lemma inst_wl_ss_dom_notin_r : forall Θ Θ' Γ' Γ x
  , Θ ⊩ Γ' ⟿ Γ ⫣ Θ'
  → x `notin` dom Θ
  → x `notin` wl_dom Γ'
  → x `notin` dom Θ'.
Proof.
  induction 1; simpl; intros; auto.
Qed.

Hint Resolve inst_wl_ss_dom_notin_r : ss_dom.

Ltac gather_atoms_transfer :=
  let L0 := gather_atoms_with
              (fun x : atom => {{ x }}) in
  let L1 := gather_atoms_with
              (fun x : atoms => x) in
  let L2 := gather_atoms_with
              (fun x : bexpr => fv_bexpr x) in
  let L3 := gather_atoms_with
              (fun x : aexpr =>
                 fv_aexpr x `union` fex_aexpr x `union` fkv_aexpr x) in
  let L4 := gather_atoms_with
              (fun x : subst_set =>
                 fv_ss x `union` dom x) in
  let L5 := gather_atoms_with
              (fun x : dworklist =>
                 fv_dworklist x `union` dwl_dom x) in
  let L6 := gather_atoms_with
              (fun x : worklist =>
                 fv_worklist x `union` wl_dom x) in
  let L7 := gather_atoms_with
              (fun x : bbody => fv_bbody x) in
  let L8 := gather_atoms_with
              (fun x : abody => fv_abody x) in
  let L9 := gather_atoms_with
              (fun x : cont =>
                 fv_cont x `union` fex_cont x `union` fkv_cont x) in
  constr:(L0 `union` L1 `union` L2 `union` L3 `union` L4
            `union` L5 `union` L6 `union` L7 `union` L8
            `union` L9).

Tactic Notation "pick" "fresh" ident(x) "for" "all" :=
  let L  := gather_atoms_transfer in
  pick fresh x for L.

Local Ltac conclude_det_ih :=
  match goal with
  | H1 : _ ⊩ ?e ⇝ ?e1 , H2 : _ ⊩ ?e ⇝ ?e2 |- _ =>
     assert (e1 = e2) as -> by auto; clear H1 H2
  | H1 : forall x, _ → inst_body _ _ (open_bbody_wrt_bexpr ?b1 `'x)
  , H2 : forall x, _ → inst_body _ _ (open_bbody_wrt_bexpr ?b2 `'x)
    |- _ =>
      let x := fresh "x" in
      pick fresh x for all;
      assert (open_bbody_wrt_bexpr b1 `'x = open_bbody_wrt_bexpr b2 `'x) by auto;
      assert (b1 = b2) as -> by (eapply open_bbody_wrt_bexpr_inj; eauto);
      clear H1 H2
  | H1 : forall x, _ → _ ⊩ _ ⇝ ?e1 ^`' x
  , H2 : forall x, _ → _ ⊩ _ ⇝ ?e2 ^`' x
    |- _ =>
      let x := fresh "x" in
      pick fresh x for all;
      assert (e1 ^`' x = e2 ^`' x) by eauto;
      assert (e1 = e2) as -> by (eapply open_bexpr_wrt_bexpr_inj; eauto);
      clear H1 H2
  end
.

Local Ltac conclude_dets_ih := repeat conclude_det_ih.

Lemma inst_e_det : forall e' Θ e1,
  uniq Θ → Θ ⊩ e' ⇝ e1 → forall e2, Θ ⊩ e' ⇝ e2 → e1 = e2.
Proof.
  induction 2 using inste_mut with
    (P0 := fun Θ b' b1 _ => uniq Θ → forall b2, inst_body Θ b' b2 → b1 = b2);
  try (intros e2 H2; dependent destruction H2; auto);
  (* solving all the binds with binds_unique in metalib *)
  try match goal with
  | H1 : binds ?x ?e1 ?c , H2 : binds ?x ?e2 ?c |- _ = _ =>
    let E := fresh "E" in
      assert (e1 = e2) as E by (eapply binds_unique; eauto);
      inversion E; now subst
    end;
  conclude_dets_ih; auto.
Qed.

Lemma inst_wl_split : forall Γ1' Γ2' Γ Θ Θ'
  , Θ ⊩ Γ1' ⫢′ Γ2' ⟿ Γ ⫣ Θ'
  → exists Γ1 Γ2 Θ0
    , Γ = Γ1 ⫢ Γ2
    ∧ Θ  ⊩ Γ1' ⟿ Γ1 ⫣ Θ0
    ∧ Θ0 ⊩ Γ2' ⟿ Γ2 ⫣ Θ'.
Proof.
  induction Γ2'; simpl; intros.
  - exists Γ, dwl_nil, Θ'; simpl; eauto with inst_wf_ss.
  - inversion H; subst.
    pose proof (IHΓ2' _ _ _ H3) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
    exists Γ1, (Γ2 ⊨ w0), Θ0. repeat split; eauto.
  - destruct bd; inversion H; subst.
    + pose proof (IHΓ2' _ _ _ H3) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
      exists Γ1, (Γ2 ,′' x : A0), Θ0.
      subst. repeat split; eauto.
    + pose proof (IHΓ2' _ _ _ H4) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
      exists Γ1, Γ2, Θ0.
      subst. repeat split; eauto.
    + pose proof (IHΓ2' _ _ _ H3) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
      exists Γ1, Γ2, Θ0.
      subst. repeat split; eauto.
Qed.


Lemma inst_wl_ss_extend : forall Θ Γ' Γ Θ'
  , Θ ⊩ Γ' ⟿ Γ ⫣ Θ'
  → exists Θ0, Θ ;; Θ0 = Θ'.
Proof.
  induction 1;
    (* when ss doesn't change *)
    try solve [now exists nil];
    (* otherwise, extract the components of the tail *)
    destruct IHinst_wl as [Θ0 <-].
  - now exists Θ0.
  - now exists (Θ0; x : A!).
  - now exists (Θ0; x ≔ ⧼k⧽).
  - now exists (Θ0; x : A ≔ e).
Qed.

Lemma inst_e_weakening : forall Θ1 Θ2 e' e Θ'
  , Θ1 ;; Θ2 ⊩ e' ⇝ e → wf_ss (Θ1 ;; Θ' ;; Θ2)
  → Θ1 ;; Θ' ;; Θ2 ⊩ e' ⇝ e.
Proof.
  intros * H.
  remember (Θ1 ;; Θ2) as Θ.
  generalize dependent Θ2. generalize dependent Θ1.
  pattern Θ, e', e, H.
  apply inste_mut with
    (P0 := fun Θ b' b _ =>
        forall Θ1 Θ2, Θ = Θ1 ;; Θ2 → wf_ss (Θ1 ;; Θ' ;; Θ2)
            → inst_body (Θ1 ;; Θ' ;; Θ2) b' b);
    intros; subst; eauto 4. (* make use of `binds_weaken` *)
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

Lemma inst_e_weakening_cons : forall Θ sse e' e
  , Θ ⊩ e' ⇝ e → wf_ss (cons sse Θ)
  → cons sse Θ ⊩ e' ⇝ e.
Proof.
  intros.
  replace (cons sse Θ) with (Θ ;; one sse ;; nil) by auto.
  auto with inst_weakening.
Qed.

#[export]
Hint Resolve
  inst_e_weakening_app
  inst_e_weakening_cons
  inst_e_weakening : inst_weakening.

Lemma to_ctx_ignore_ex_k : forall Θ1 Θ2 x k
  , ⌊ Θ1 ; x ≔ ⧼ k ⧽ ;; Θ2 ⌋′ = ⌊ Θ1 ;; Θ2 ⌋′.
Proof.
  intros; induction Θ2; simpl.
  - reflexivity.
  - destruct a. destruct s; auto.
Qed.

Lemma dom_remove : forall A (Θ1 : list (atom * A)) Θ2 x e
  , dom (Θ2 ++ Θ1) [<=] dom (Θ2 ++ (cons (pair x e) Θ1)).
Proof.
  intros; induction Θ2; simpl.
  - fsetdec.
  - destruct a. fsetdec.
Qed.

Lemma ss_wf_strengthening_k : forall Θ1 Θ2 x k
  , wf_ss (Θ1 ; x ≔ ⧼ k ⧽ ;; Θ2)
  → wf_ss (Θ1 ;; Θ2).
Proof.
  intros *; induction Θ2; simpl; intros.
  - now inversion H.
  - destruct a. destruct s; dependent destruction H; econstructor;
      try solve
        [ auto
        | assert (dom (Θ1 ;; Θ2) [<=] dom (Θ1 ; x ≔ ⧼k⧽;; Θ2)) by
          apply dom_remove; fsetdec
        | rewrite to_ctx_ignore_ex_k in *; eassumption].
Qed.

#[export]
Hint Resolve ss_wf_strengthening_k : ss_strengthen.

Lemma in_strengthening : forall A (xs : list A) a ys b,
    In a (xs ++ b :: ys) → b <> a → In a (xs ++ ys).
Proof.
  intros *; induction xs; simpl; intros.
  - destruct H; easy.
  - destruct H; auto.
Qed.

#[export]
Hint Unfold binds : ss_strengthen.
#[export]
Hint Resolve in_strengthening : ss_strengthen.

Hint Extern 1 (_ <> _) => discriminate : core.

Lemma inst_e_strengthening_k : forall Θ1 Θ2 x k e' e
  , Θ1 ; x ≔ ⧼ k ⧽ ;; Θ2 ⊩ e' ⇝ e
  → x `notin` fkv_aexpr e'
  → Θ1 ;; Θ2 ⊩ e' ⇝ e.
Proof.
  intros * H.
  remember (Θ1; x ≔ ⧼ k ⧽ ;; Θ2) as Θ.
  generalize dependent Θ2.
  pattern Θ, e', e, H.
  eapply inste_mut with
    (P0 := fun Θ b' b _ => forall Θ2
      , Θ = Θ1; x ≔ ⧼ k ⧽;; Θ2
      → x `notin` fkv_abody b'
      → inst_body (Θ1 ;; Θ2) b' b)
  ; simpl in *; intros; subst;
    eauto 4 with ss_strengthen.
  - eauto with ss_strengthen.
  - eauto 8 with ss_strengthen.
  - pick fresh x' and apply inste_abs;
      eauto 3 with ss_strengthen lngen.
  - pick fresh x' and apply inste_bind;
      eauto 3 with ss_strengthen lngen.
  - pick fresh x' and apply inste_pi;
      eauto 3 with ss_strengthen lngen.
  - pick fresh x' and apply inste_all;
      eauto 3 with ss_strengthen lngen.
Qed.

Lemma inst_e_strengthening_k_cons : forall Θ x k e' e
  , Θ; x ≔ ⧼ k ⧽ ⊩ e' ⇝ e
  → x `notin` fkv_aexpr e'
  → Θ ⊩ e' ⇝ e.
Proof.
  intros *.
  replace (Θ; x ≔ ⧼ k ⧽) with (Θ ; x ≔ ⧼ k ⧽ ;; nil) by auto.
  apply inst_e_strengthening_k.
Qed.

#[export]
Hint Resolve
  inst_e_strengthening_k
  inst_e_strengthening_k_cons
  : ss_strengthen.

Lemma inst_c_strengthening_k : forall Θ1 Θ2 x k c' c
  , Θ1; x ≔ ⧼ k ⧽ ;; Θ2 ⊩ c' ⟿′ c
  → x `notin` fkv_cont c'
  → Θ1 ;; Θ2 ⊩ c' ⟿′ c.
Proof.
  intros * H.
  dependent induction H; simpl; intros; eauto with ss_strengthen.
Qed.

Lemma inst_c_strengthening_k_cons : forall Θ x k c' c
  , Θ; x ≔ ⧼ k ⧽ ⊩ c' ⟿′ c
  → x `notin` fkv_cont c'
  → Θ ⊩ c' ⟿′ c.
Proof.
  intros *.
  replace (Θ; x ≔ ⧼ k ⧽) with (Θ; x ≔ ⧼ k ⧽;; nil) by auto.
  apply inst_c_strengthening_k.
Qed.

#[export]
Hint Resolve
  inst_c_strengthening_k
  inst_c_strengthening_k_cons
  : ss_strengthen.

Ltac conclude_det :=
  match goal with
  | H1 : ?Θ ⊩ ?e ⇝ ?e1
  , H2 : ?Θ ⊩ ?e ⇝ ?e2 |- _ =>
      match e1 with
      | e2 => clear H1
      | _ => assert (e1 = e2) as -> by (eauto 4 using inst_e_det with inst_wf_ss)
      end
      ; clear H1
  | H1 : ?Θ ⊩ ?e ⇝ ?e1
  , H2 : ?Θ; ?x ≔ ⧼_⧽ ⊩ ?e ⇝ ?e2 |- _ =>
      apply inst_e_strengthening_k_cons in H2; auto
  end
.

Ltac conclude_dets := repeat conclude_det.

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
  end
.

Ltac conclude_ss_extend :=
  repeat conclude_ss_extend_impl.

(*
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
 *)

Hint Rewrite bexpr_subst_open_comm aexpr_subst_open_comm : ln.
Hint Rewrite bbody_subst_open_comm abody_subst_open_comm : ln.
(*
Hint Rewrite worklist_subst_open_comm dworklist_subst_open_comm : ln.
*)

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

Lemma fresh_dom_fresh_expr_l : forall x Γ e1 e2 d A
  , busub Γ e1 e2 d A
    → x `notin` bctx_dom Γ → x `notin` fv_bexpr e1.
Proof.
  induction 1; simpl; intros; auto 1.
Admitted.

Lemma notin_dom_notin_inst : forall x ex e Θ A,
    ex : A ≔ e ∈ Θ → x `notin` dom Θ → wf_ss Θ → x `notin` fv_bexpr e.
Proof.
  induction Θ; intros.
  - inversion H.
  - destruct a. destruct H.
    + inversion H; subst. simpl in *.
      inversion H1; subst.
      eauto using fresh_dom_fresh_expr_l, fresh_dom_fresh_ctx.
    + simpl in H0; inversion H1; eauto 2.
Qed.

Lemma notin_ss_notin_inst : forall x ex e Θ A,
    ex : A ≔ e ∈ Θ → x `notin` fv_ss Θ → x `notin` fv_bexpr e.
Proof.
  induction Θ; intros.
  - inversion H.
  - destruct a. destruct H.
    + inversion H; subst; simpl in *; auto.
    + simpl in H0; eauto.
Qed.



Lemma fresh_dom_r : forall x Θ1 Γ' Γ Θ2
  , Θ1 ⊩ Γ' ⟿ Γ ⫣ Θ2
  → x `notin` dom Θ1
  → x `notin` wl_dom Γ'
  → x `notin` dom Θ2.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma inst_e_rename : forall Θ e' e x x'
  , Θ ⊩ e' ⇝ e → x `notin` dom Θ
  → Θ ⊩ [`′ x' /′ x] e' ⇝ [`' x' /' x] e.
Proof.
  intros.
  induction H using inste_mut with
    (P0 := fun Θ b' b _ => x `notin` dom Θ
      → inst_body Θ (subst_abody `′x' x b') (subst_bbody`' x' x b));
    simpl; auto.
  - unfold eq_dec. destruct (EqDec_eq_of_X x0 x); auto.
  - rewrite subst_bexpr_fresh_eq; eauto using notin_dom_notin_inst.
  - apply inste_abs  with (add x L); eauto with ln.
  - apply inste_bind with (add x L); eauto with ln.
  - apply inste_pi   with (add x L); eauto with ln.
  - apply inste_all  with (add x L); eauto with ln.
Qed.

Hint Resolve inst_e_rename : ln.

Lemma inst_body_rename : forall Θ b' b x x'
  , inst_body Θ b' b → x `notin` dom Θ
  → inst_body Θ (subst_abody `′x' x b') (subst_bbody `'x' x b).
Proof.
  intros.
  induction H; simpl.
  eauto using inst_e_rename.
Qed.

Lemma inst_ob_rename : forall Θ ob' ob x x'
  , Θ ⊩ ob' ⇝? ob → x `notin` dom Θ
  → Θ ⊩ subst_obind (`′ x') x ob' ⇝? subst_obindd (`' x') x ob.
Proof.
  intros.
  destruct H; simpl; eauto with ln.
Qed.

Hint Resolve inst_ob_rename : ln.

Lemma inst_e_fresh : forall Θ e' e x,
    Θ ⊩ e' ⇝ e → x `notin` fv_bexpr e → x `notin` fv_aexpr e'.
Proof.
  (*induction 1; simpl; intros;
    try solve [ eauto 3
          | pick fresh x' for all;
            eauto 6 using open_aexpr_fv_aexpr_notin, fv_bexpr_open_bexpr_notin]. *)
  (* mut-ind with body *)
Admitted.

Lemma fresh_inst_e : forall Θ e' e x,
    Θ ⊩ e' ⇝ e → x `notin` fv_aexpr e' → x `notin` fv_bexpr e.
Proof.
  (* mut_ind with body *)
Admitted.

Hint Resolve fv_bexpr_open_bexpr_notin : atoms.
Hint Resolve close_bexpr_notin : atoms.
Hint Resolve bbody_close_notin : atoms.

Hint Resolve inst_ae_lc : lc.
Hint Resolve inst_e_lc : lc.

Hint Rewrite close_bexpr_wrt_bexpr_open_bexpr_wrt_bexpr : ln.
Hint Rewrite <- subst_bexpr_close_bexpr_wrt_bexpr : ln.
Hint Rewrite open_bexpr_wrt_bexpr_close_bexpr_wrt_bexpr : ln.

Hint Rewrite close_bbody_wrt_bexpr_open_bbody_wrt_bexpr : ln.
Hint Rewrite open_bbody_wrt_bexpr_close_bbody_wrt_bexpr : ln.

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
  | |- context [open_bbody_wrt_bexpr ?b `' ?x] =>
      lazymatch goal with
      | |- context [open_bbody_wrt_bexpr (open_bbody_wrt_bexpr b `'x) `'?x'] => fail
      | |- context [subst_bbody `'?x' x (open_bbody_wrt_bexpr b `'x)] => fail
      | _ => let x1 := pick_different x in rewrite (subst_bbody_intro x1)
      end
  | |- context [open_abody_wrt_aexpr ?b `′ ?x] =>
      lazymatch goal with
      | |- context [open_abody_wrt_aexpr (open_abody_wrt_aexpr b `′x) `′?x'] => fail
      | |- context [subst_abody `′?x' x (open_abody_wrt_aexpr b `′x)] => fail
      | _ => let x1 := pick_different x in rewrite (subst_abody_intro x1)
      end
  end; auto 2 with atoms
.

Ltac prepare_rename := repeat prepare_rename_impl.

Scheme aexpr_lc_mut := Induction for lc_aexpr Sort Prop
  with abody_lc_mut := Induction for lc_abody Sort Prop.

Ltac e_rev_subst_apply_ih :=
  match goal with
  | IH : forall _ (e0 : bexpr), _ ⊩ [?v /′ ?x] ?e ^`′ _ ⇝ _ → _
  , H  : _ ⊩ ([?v /′ ?x] ?e) ^`′ _ ⇝ ?e1 ^`' _ |- _ =>
    let e1' := fresh e1 in
    let E := fresh "E" in
    let H' := fresh "H" in
    rewrite aexpr_subst_open_comm in H; eauto 3 with lc;
    apply IH in H as (e1' & E & H'); auto with atoms
  | IH : forall _, _ ⊩ [?v /′ ?x] ?e ⇝ _ → _
  , H  : _ ⊩ [?v /′ ?x] ?e ⇝ ?e1 |- _ =>
    let e1' := fresh e1 in
    let E := fresh "E" in
    let H' := fresh "H" in
    apply IH in H as (e1' & E & H'); auto with atoms
  | IH : forall _ (b0 : bbody), inst_body _ (subst_abody ?v ?x (open_abody_wrt_aexpr ?b' _)) _ → _
  , H : inst_body _ (open_abody_wrt_aexpr (subst_abody ?v ?x ?b') _) (open_bbody_wrt_bexpr ?b1 _) |- _ =>
  let b1' := fresh b1 in
  let E := fresh "E" in
  let H' := fresh "H" in
  rewrite abody_subst_open_comm in H; eauto 3 with lc;
  apply IH in H as (b1' & E & H'); auto with atoms
  end
.

Lemma inst_e_rev_subst' : forall v' v x Θ e'
  , lc_aexpr e'
  → x `notin` (fv_aexpr v' `union` fv_ss Θ) → Θ ⊩ v' ⇝ v
  → forall e0
  , Θ ⊩ [v' /′ x] e' ⇝ e0
  → exists e, [v /' x] e = e0 ∧ Θ ⊩ e' ⇝ e.
Proof.
  intros * Lc Fr InstV.
  induction Lc using aexpr_lc_mut with
    (P0 := fun b' _ => forall b0
      , inst_body Θ (subst_abody v' x b') b0
      → exists b, subst_bbody v x b = b0 ∧ inst_body Θ b' b);

  intros * Inst; simpl in *
    ; lazymatch type of Inst with
      (* only if it's a variable it doesn't invert the hypo *)
    | _ ⊩ (if _ then _ else _) ⇝ _ => idtac
    | _ ⊩ ⧼ ?k ⧽′ ⇝ _ => destruct k; inversion Inst; subst
    | _ => inversion Inst; subst; simpl in Fr;
          (* instantiate cofinite for those with binders *)
          inst_cofinites_by gather_atoms_transfer;
          repeat e_rev_subst_apply_ih
    end; subst.
  - exists (`' x0). simpl.
    unfold eq_dec in *. destruct (EqDec_eq_of_X x0 x); subst.
    + assert (v = e0) by
        (eapply inst_e_det with (Θ := Θ); eauto with inst_wf_ss).
      eauto with inst_wf_ss.
    + inversion Inst. now subst.
  - exists ⋆'; eauto.
  - exists ◻'; eauto.
  - exists ⧼ k ⧽'; eauto.
  - exists e0. eauto 4 using notin_ss_notin_inst with lngen atoms.
  - exists (be_num n); eauto.
  - exists be_int; eauto.
  - exists (be_bot A1); eauto.
  - exists (be_app f0 a0); auto.
  - exists (be_abs A1 (close_bbody_wrt_bexpr x0 b1)). split.
    + simpl. f_equal.
      rewrite subst_bbody_close_bbody_wrt_bexpr; eauto with lc.
      apply bbody_open_r_close_l; auto.
    + apply inste_abs with L; intros; auto.
      * prepare_rename.
        apply inst_body_rename; autorewrite with ln; auto.
  - exists (be_pi A1 (B1 \`' x0)). split.
    + simpl. f_equal.
      rewrite subst_bexpr_close_bexpr_wrt_bexpr; eauto with lc.
      apply bexpr_open_r_close_l; auto.
    + apply inste_pi with L; intros; auto.
      prepare_rename; apply inst_e_rename;
        autorewrite with ln; auto.
  - exists (be_bind A1 (close_bbody_wrt_bexpr x0 b1)). split.
    + simpl. f_equal.
      rewrite subst_bbody_close_bbody_wrt_bexpr; eauto with lc.
      apply bbody_open_r_close_l; auto.
    + apply inste_bind with L; intros; auto.
      * prepare_rename.
        apply inst_body_rename; autorewrite with ln; auto.
  - exists (be_all A1 (B1 \`' x0)). split.
    + simpl. f_equal.
      rewrite subst_bexpr_close_bexpr_wrt_bexpr; eauto with lc.
      apply bexpr_open_r_close_l; auto.
    + apply inste_all with L; intros; auto.
      prepare_rename; apply inst_e_rename;
        autorewrite with ln; auto.
  - exists (be_castup A1 e0); subst; auto.
  - exists (be_castdn e0); subst; auto.
  - exists (e0 ::' A1); subst; auto.
  - exists (bb_anno e1 A1). subst. auto.
Qed.

Lemma inst_e_rev_subst : forall e0 Θ v' v x e'
  , x `notin` (fv_aexpr v' `union` fv_ss Θ)
  → Θ ⊩ v' ⇝ v → Θ ⊩ [v' /′ x] e' ⇝ e0
  → exists e, [v /' x] e = e0 ∧ Θ ⊩ e' ⇝ e.
Proof.
Admitted.

(*
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
*)
