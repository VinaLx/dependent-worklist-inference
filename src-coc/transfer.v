Require Import alg.worklist.
Require Import decl.worklist.
Require Import Program.Tactics.

Inductive inst_binding : Set :=
| ib_v : var → expr → inst_binding
| ib_x : var → kind → expr → inst_binding
| ib_k : var → kind → inst_binding
.

Definition inst_list := list inst_binding.

Notation "x :_ A " :=
  (ib_v x A)
    (at level 52, no associativity).

Notation "^ x :_ k = e" :=
  (ib_x x k e)
    (at level 52, x at level 0, k at level 0
      , no associativity).

Notation "⧼ ^ x ⧽= k" :=
  (ib_k x k)
    (at level 0, x at level 0, no associativity).

Notation "T ; b" :=
  (cons b T)
    (at level 58, left associativity).

Notation "T1 ;; T2" :=
  (app T2 T1)
    (at level 58, left associativity).

Reserved Notation "⌊ Θ ⌋_" (at level 0, Θ at level 58).
Fixpoint inst_list_to_ctx (Θ : inst_list) :=
  match Θ with
  | nil => ctx_nil
  | Θ' ; x :_ A => ⌊ Θ' ⌋_ , x : A
  | Θ' ; _ => ⌊ Θ' ⌋_
  end
where "⌊ Θ ⌋_" := (inst_list_to_ctx Θ) : context_scope.

Definition ib_dom (b : inst_binding) : atom :=
  match b with
  | ib_v x _ => x
  | ib_x x _ _ => x
  | ib_k x _ => x
  end
.

(* "il" represents "Instantiation List" *)
Fixpoint il_dom (Θ : inst_list) :=
  match Θ with
  | nil => empty
  | Θ' ; b => add (ib_dom b) (il_dom Θ' )
  end
.

Inductive wf_il : inst_list → Prop :=
| wfil_nil : wf_il nil
| wfil_var : forall x A Θ k
  , wf_il Θ → x `notin` il_dom Θ
  → ⌊ Θ ⌋_ ⊢ A : ⧼ k ⧽
  → wf_il (Θ ; x :_ A)
| wfil_k : forall Θ x k
  , wf_il Θ → x `notin` il_dom Θ
  → wf_il (Θ ; ⧼^x⧽= k )
| wfil_ex : forall Θ x k A
  , wf_il Θ → x `notin` il_dom Θ
  → ⌊ Θ ⌋_ ⊢ A : ⧼ k ⧽
  → wf_il (Θ ; ^x :_ k = A)
.

Hint Constructors wf_il : core.

Reserved Notation "Θ ⊢ k' ~> k"
  (at level 60, k' at next level, no associativity).
Inductive inst_kind : inst_list → akind → kind → Prop :=
| ik_star : forall Θ,
    wf_il Θ → Θ ⊢ ak_star ~> k_star
| ik_box : forall Θ,
    wf_il Θ → Θ ⊢ ak_box  ~> k_box
| ik_ex : forall Θ x k,
    wf_il Θ → In (⧼^x⧽= k) Θ → Θ ⊢ ak_ex x ~> k
where "Θ ⊢ k' ~> k" := (inst_kind Θ k' k) : type_scope
.

Hint Constructors inst_kind : core.

Reserved Notation "Θ ⊢ e' ⇝ e"
  (at level 60, e' at next level, no associativity).
Inductive inst_expr : inst_list → aexpr → expr → Prop :=
| ie_var : forall Θ x,
    wf_il Θ → Θ ⊢ `′ x ⇝ `x
| ie_kind : forall Θ k' k,
    Θ ⊢ k' ~> k → Θ ⊢ ⧼k'⧽′ ⇝ ⧼k⧽
| ie_num : forall Θ n,
    wf_il Θ → Θ ⊢ ae_num n ⇝ e_num n
| ie_int : forall Θ,
    wf_il Θ → Θ ⊢ ae_int ⇝ e_int
| ie_ex : forall Θ x k e,
    wf_il Θ → In (^x :_ k = e) Θ → Θ ⊢ `^x ⇝ e
| ie_app : forall Θ f' f e' e
  , Θ ⊢ f' ⇝ f
  → Θ ⊢ e' ⇝ e
  → Θ ⊢ ae_app f' e' ⇝ e_app f e
| ie_pi : forall L Θ A' A B' B
  , Θ ⊢ A' ⇝ A
  → (forall x, x `notin` L → Θ ⊢ B' ^`′ x ⇝ B ^` x)
  → Θ ⊢ ae_pi A' B' ⇝ e_pi A B
| ie_abs : forall L Θ e' e
  , (forall x, x `notin` L → Θ ⊢ e' ^`′ x ⇝ e ^` x)
  → Θ ⊢ ae_abs e' ⇝ e_abs e
where "Θ ⊢ e' ⇝ e" := (inst_expr Θ e' e) : type_scope.

Hint Constructors inst_expr : core.

Reserved Notation "Θ ⊢ c' ⟿′ c"
  (at level 60, c' at next level, no associativity).
Inductive inst_cont : inst_list → cont → dcont → Prop :=
| ic_done : forall Θ,
    wf_il Θ → Θ ⊢ c_done ⟿′ dc_done
| ic_check : forall Θ A' A
  , Θ ⊢ A' ⇝ A
  → Θ ⊢ __ ⧼~~⧽′ A' ⟿′ __ ⧼~~⧽ A
| ic_app : forall Θ c' c e1 e2 e
  , Θ ⊢ e1 ⇝ e
  → Θ ⊢ e2 ⇝ e
  → Θ ⊢ c' ⟿′ c
  → Θ ⊢ __ ⋅ e1 & e2 ⇒′ c' ⟿′ __ ⋅ e ⇒ c
where "Θ ⊢ c' ⟿′ c" := (inst_cont Θ c' c) : type_scope
.

Hint Constructors inst_cont : core.

Reserved Notation "Θ ⊢ Γ' ⟿′′ Γ"
  (at level 60, Γ' at next level, no associativity).
Inductive inst_ctx : inst_list → acontext → context → Prop :=
| ictx_nil : forall Θ,
    wf_il Θ → Θ ⊢ actx_nil ⟿′′ ctx_nil
| ictx_cons : forall Θ Γ' Γ x A' A
  , Θ ⊢ A' ⇝ A
  → Θ ⊢ Γ' ⟿′′ Γ
  → Θ ⊢ Γ' ,′′ x : A' ⟿′′ Γ , x : A
where "Θ ⊢ Γ' ⟿′′ Γ" := (inst_ctx Θ Γ' Γ)
.

Hint Constructors inst_ctx : core.

Reserved Notation "Θ ⊢ w' ⇝′ w"
  (at level 60, w' at next level, no associativity).
Inductive inst_work : inst_list → work → dwork → Prop :=
| iw_check : forall Θ Γ' Γ e1 e2 e A' A
  , Θ ⊢ Γ' ⟿′′ Γ
  → Θ ⊢ e1 ⇝ e
  → Θ ⊢ e2 ⇝ e
  → Θ ⊢ A' ⇝ A
  → Θ ⊢ (Γ' ⊢′ e1 ~~ e2 ⇐′ A') ⇝′ (Γ ⊢' e ⇐ A)
| iw_infer : forall Θ e1 e2 e c' c
  , Θ ⊢ e1 ⇝ e
  → Θ ⊢ e2 ⇝ e
  → Θ ⊢ c' ⟿′ c
  → Θ ⊢ (e1 ~~ e2 ⇒′ c') ⇝′ (e ⇒' c)
| iw_iapp : forall Θ A' A e1 e2 e c' c
  , Θ ⊢ e1 ⇝ e
  → Θ ⊢ e2 ⇝ e
  → Θ ⊢ A' ⇝ A
  → Θ ⊢ c' ⟿′ c
  → Θ ⊢ (A' ⋅ e1 & e2 ⇒′ c') ⇝′ (A ⋅ e ⇒ c)
| iw_capp : forall Θ c' c e' e
  , Θ ⊢ c' ⟿′ c
  → Θ ⊢ e' ⇝ e
  → Θ ⊢ c' $′ e' ⇝′ c $ e
| iw_comp : forall Θ A' A B' B
  , Θ ⊢ A' ⇝ A
  → Θ ⊢ B' ⇝ B
  → Θ ⊢ A' ⧼~~⧽′ B' ⇝′ A ⧼~~⧽ B
where "Θ ⊢ w' ⇝′ w" := (inst_work Θ w' w) : type_scope.

Hint Constructors inst_work : core.

Reserved Notation "Θ ⊢ Γ' ⟿ Γ ⊣ Θ'"
  (at level 60, Γ' at next level, Γ at next level, no associativity).

Inductive inst_wl : inst_list → worklist → dworklist → inst_list → Prop :=
| iwl_nil : forall Θ, wf_il Θ → Θ ⊢ wl_nil ⟿ dwl_nil ⊣ Θ
| iwl_cons : forall Θ1 Θ2 Γ' Γ w' w
  , Θ1 ⊢ Γ' ⟿ Γ ⊣ Θ2
  → Θ2 ⊢ w' ⇝′ w
  → Θ1 ⊢ Γ' ⊨′ w' ⟿ Γ ⊨ w ⊣ Θ2
| iwl_tag : forall Θ1 Θ2 Γ' Γ
  , Θ1 ⊢ Γ' ⟿ Γ ⊣ Θ2
  → Θ1 ⊢ Γ' ,′ ◁ ⟿ Γ ,' ◁ ⊣ Θ2
| iwl_var : forall Θ1 Θ2 Γ' Γ x A' A k
  , x `notin` il_dom Θ2
  → (⌊ Θ2 ⌋_ ⊢ A : ⧼ k ⧽)
  → Θ1 ⊢ Γ' ⟿ Γ ⊣ Θ2
  → Θ2 ⊢ A' ⇝ A
  → Θ1 ⊢ Γ' ,′ x :′ A' ⟿ Γ ,' x : A ⊣ Θ2; x :_ A
| iwl_kind : forall Θ1 Θ2 Γ' Γ x k
  , x `notin` il_dom Θ2
  → Θ1 ⊢ Γ' ⟿ Γ ⊣ Θ2
  → Θ1 ⊢ Γ' ,′ ⧼^x⧽ ⟿ Γ ⊣ Θ2; ⧼^x⧽= k
| iwl_ex : forall Θ1 Θ2 Γ' Γ x k' k e
  , x `notin` il_dom Θ2
  → ⌊ Θ2 ⌋_ ⊢ e : ⧼k⧽
  → Θ1 ⊢ Γ' ⟿ Γ ⊣ Θ2
  → Θ2 ⊢ k' ~> k
  → Θ1 ⊢ Γ' ,′ ^x :′ k' ⟿ Γ ⊣ (Θ2; ^x :_ k = e)
where "Θ ⊢ Γ' ⟿ Γ ⊣ Θ'" := (inst_wl Θ Γ' Γ Θ') : type_scope.

Hint Constructors inst_wl : core.

Reserved Notation "Θ ⊢ w' ⇝₂ w"
  (at level 60, w' at next level, no associativity).
Inductive inst_work_c : inst_list → work → dwork → Prop :=
| iw2_check : forall Θ Γ' Γ e1 e2 e A' A
  , Θ ⊢ Γ' ⟿′′ Γ
  → Θ ⊢ e1 ⇝ e
  → Θ ⊢ e2 ⇝ e
  → Θ ⊢ A' ⇝ A
  → Θ ⊢ (Γ' ⊢′ e1 ~~ e2 ⇐′ A') ⇝₂ (Γ ⊢' e ⇐ A)
| iw2_infer : forall Θ e1 e2 e c' c
  , Θ ⊢ e1 ⇝ e
  → Θ ⊢ e2 ⇝ e
  → Θ ⊢ c' ⟿′ c
  → Θ ⊢ (e1 ~~ e2 ⇒′ c') ⇝₂ (e ⇒' c)
| iw2_iapp : forall Θ A' A e1 e2 e c' c
  , Θ ⊢ e1 ⇝ e
  → Θ ⊢ e2 ⇝ e
  → Θ ⊢ A' ⇝ A
  → Θ ⊢ c' ⟿′ c
  → Θ ⊢ (A' ⋅ e1 & e2 ⇒′ c') ⇝₂ (A ⋅ e ⇒ c)
| iw2_capp : forall Θ c' c e' e
  , Θ ⊢ c' ⟿′ c
  → Θ ⊢ e' ⇝ e
  → Θ ⊢ c' $′ e' ⇝₂ c $ e
| iw2_comp : forall Θ A' A B' B
  , Θ ⊢ A' ⇝ A
  → Θ ⊢ B' ⇝ B
  → Θ ⊢ A' ⧼~~⧽′ B' ⇝₂ A ⧼~~⧽ B
where "Θ ⊢ w' ⇝₂ w" := (inst_work_c Θ w' w) : type_scope.

Hint Constructors inst_work_c : core.

Reserved Notation "Θ ⊢ Γ' ⟿₂ Γ ⊣ Θ'"
  (at level 60, Γ' at next level, Γ at next level, no associativity).

Inductive inst_wl_c : inst_list → worklist → dworklist → inst_list → Prop :=
| iwl2_nil : forall Θ, wf_il Θ → Θ ⊢ wl_nil ⟿₂ dwl_nil ⊣ Θ
| iwl2_cons : forall Θ1 Θ2 Γ' Γ w' w
  , Θ1 ⊢ Γ' ⟿₂ Γ ⊣ Θ2
  → Θ2 ⊢ w' ⇝₂ w
  → Θ1 ⊢ Γ' ⊨′ w' ⟿₂ Γ ⊨ w ⊣ Θ2
| iwl2_tag : forall Θ1 Θ2 Γ' Γ
  , Θ1 ⊢ Γ' ⟿₂ Γ ⊣ Θ2
  → Θ1 ⊢ Γ' ,′ ◁ ⟿₂ Γ ,' ◁ ⊣ Θ2
| iwl2_var : forall Θ1 Θ2 Γ' Γ x A' A k
  , x `notin` il_dom Θ2
  → ⌊ Θ2 ⌋_ ⊢ A : ⧼ k ⧽
  → Θ1 ⊢ Γ' ⟿₂ Γ ⊣ Θ2
  → Θ2 ⊢ A' ⇝ A
  → Θ1 ⊢ Γ' ,′ x :′ A' ⟿₂ Γ ,' x : A ⊣ Θ2; x :_ A
| iwl2_kind : forall Θ1 Θ2 Γ' Γ x k
  , x `notin` il_dom Θ2
  → Θ1 ⊢ Γ' ⟿₂ Γ ⊣ Θ2
  → Θ1 ⊢ Γ' ,′ ⧼^x⧽ ⟿₂ Γ ⊣ Θ2; ⧼^x⧽= k
| iwl2_ex : forall Θ1 Θ2 Γ' Γ x k' k e
  , x `notin` il_dom Θ2
  → ⌊ Θ2 ⌋_ ⊢ e : ⧼k⧽
  → Θ1 ⊢ Γ' ⟿₂ Γ ⊣ Θ2
  → Θ2 ⊢ k' ~> k
  → Θ1 ⊢ Γ' ,′ ^x :′ k' ⟿₂ Γ ⊣ (Θ2; ^x :_ k = e)
where "Θ ⊢ Γ' ⟿₂ Γ ⊣ Θ'" := (inst_wl_c Θ Γ' Γ Θ') : type_scope.

Hint Constructors inst_wl_c : core.

Lemma wf_il_uncons : forall Θ b,
    wf_il (Θ; b) → wf_il Θ.
Proof.
  intros. destruct b; inversion H; subst; auto.
Qed.

Hint Resolve wf_il_uncons : core.

Lemma inst_k_wf_il: forall Θ k' k,
    Θ ⊢ k' ~> k → wf_il Θ.
Proof.
  now induction 1.
Qed.

Hint Resolve inst_k_wf_il : wf_il.

Lemma inst_e_wf_il: forall Θ e' e,
    Θ ⊢ e' ⇝ e -> wf_il Θ.
Proof with eauto with wf_il.
  induction 1; pick fresh x'...
Qed.

Hint Resolve inst_e_wf_il : wf_il.

Lemma inst_w_wf_il : forall Θ w' w,
    Θ ⊢ w' ⇝′ w → wf_il Θ.
Proof with eauto with wf_il.
  induction 1...
Qed.

Hint Resolve inst_w_wf_il : wf_il.

Lemma inst_wl_wf_il : forall Θ Γ' Γ Θ',
    Θ ⊢ Γ' ⟿ Γ ⊣ Θ' → wf_il Θ ∧ wf_il Θ'.
Proof.
  induction 1; destruct_conjs; split; eauto 2 with wf_il.
Qed.

Lemma inst_wl_wf_ilₗ : forall Θ Γ' Γ Θ',
    Θ ⊢ Γ' ⟿ Γ ⊣ Θ' → wf_il Θ.
Proof.
  intros; edestruct inst_wl_wf_il; eauto.
Qed.

Lemma inst_wl_wf_ilᵣ : forall Θ Γ' Γ Θ',
    Θ ⊢ Γ' ⟿ Γ ⊣ Θ' → wf_il Θ'.
Proof.
  intros; edestruct inst_wl_wf_il; eauto.
Qed.

Hint Resolve inst_wl_wf_ilₗ inst_wl_wf_ilᵣ : wf_il.

Lemma wf_il_cons_dom_notin : forall Θ b,
    wf_il (Θ; b) → ib_dom b `notin` il_dom Θ.
Proof.
  destruct b; simpl; intros H; inversion H; auto.
Qed.

Lemma wf_il_in_absurd : forall Θ b1 b2
  , wf_il Θ
  → ib_dom b1 `notin` il_dom Θ
  → ib_dom b1 = ib_dom b2
  → In b2 Θ → False.
Proof.
  induction Θ; simpl; intros b1 b2 Wf Notin E I.
  - auto.
  - destruct I.
    + subst. rewrite E in Notin. auto.
    + eapply IHΘ; eauto.
Qed.

Lemma wf_il_inst_unique : forall Θ1 b1 Θ2 b2
  , In b2 (Θ1; b1;; Θ2)
  → ib_dom b1 = ib_dom b2
  → wf_il (Θ1; b1;; Θ2)
  → b1 = b2.
Proof.
  induction Θ2; simpl; intros.
  - destruct H.
    + trivial.
    + pose proof (wf_il_cons_dom_notin _ _ H1) as Notin.
      apply wf_il_uncons in H1.
      exfalso. eapply wf_il_in_absurd; eauto.
  - destruct H.
    + subst. exfalso.
      eapply (wf_il_in_absurd (Θ1; b1;; Θ2) b2 b1).
      * eauto.
      * now apply wf_il_cons_dom_notin.
      * auto.
      * apply in_elt.
    + eauto.
Qed.

Lemma wf_il_inst_unique_cons : forall Θ b1 b2
  , In b2 (Θ; b1)
  → ib_dom b1 = ib_dom b2
  → wf_il (Θ; b1)
  → b1 = b2.
Proof.
  intros. replace (Θ; b1) with (Θ; b1;; nil) in * by auto.
  eapply wf_il_inst_unique; eauto.
Qed.

Lemma wf_il_inst_unique_consₓ : forall Θ x k1 e1 k2 e2
  , In (^ x :_ k1 = e1) (Θ; ^ x :_ k2 = e2)
  → wf_il (Θ; ^ x :_ k2 = e2)
  → k1 = k2 ∧ e1 = e2.
Proof.
  intros * I Wf.
  apply wf_il_inst_unique_cons in I; auto.
  inversion I; auto.
Qed.

Lemma wf_il_inst_unique_consₖ : forall Θ x k1 k2
  , In (⧼^x⧽=k1) (Θ; ⧼^ x ⧽= k2)
  → wf_il (Θ; ⧼^ x ⧽= k2)
  → k1 = k2.
Proof.
  intros * I Wf.
  apply wf_il_inst_unique_cons in I; auto.
  inversion I; auto.
Qed.

Require Import Program.Equality.

Lemma inst_k_strengthenᵥ : forall Θ x A k' k,
    Θ; x :_ A ⊢ k' ~> k → Θ ⊢ k' ~> k.
Proof.
  intros. inversion H; subst; eauto.
  - destruct H1; [> inversion H1 | eauto].
Qed.

Lemma inst_k_strengthenₖ : forall Θ x k k1 k2
  , Θ; ⧼^x⧽= k ⊢ k1 ~> k2 → x `notin` fkv_akind k1
  → Θ ⊢ k1 ~> k2.
Proof.
  intros. inversion H; subst; eauto.
  - destruct H2.
    + inversion H2; subst. simpl in H0. exfalso. eauto.
    + eauto.
Qed.

Lemma inst_k_strengthenₓ : forall Θ x k' e k1 k2,
    Θ; ^x :_ k' = e ⊢ k1 ~> k2 → Θ ⊢ k1 ~> k2.
Proof.
  intros.
  dependent destruction H; eauto.
  - destruct H0; [> inversion H0 | eauto].
Qed.

#[export]
Hint Resolve
  inst_k_strengthenᵥ
  inst_k_strengthenₖ
  inst_k_strengthenₓ
  : inst_strengthen.

Lemma inst_e_strengthenᵥ : forall Θ x A e' e,
    Θ; x :_ A ⊢ e' ⇝ e → Θ ⊢ e' ⇝ e.
Proof.
  intros.
  dependent induction H; eauto with inst_strengthen.
  - destruct H0; [> inversion H0 | eauto].
Qed.

Lemma fkv_open_aexpr_notin_rec : forall x e2 e1 n
  , x `notin` fkv_aexpr e1
  → x `notin` fkv_aexpr e2
  → x `notin` fkv_aexpr (open_aexpr_wrt_aexpr_rec n e2 e1).
Proof.
  induction e1; simpl; intros; eauto.
  - destruct (lt_eq_lt_dec n n0). destruct s. all: auto.
Qed.

Lemma fkv_open_aexpr_notin : forall x e1 e2
  , x `notin` fkv_aexpr e1
  → x `notin` fkv_aexpr e2
  → x `notin` fkv_aexpr (e1 ^^′ e2).
Proof.
  intros.
  apply fkv_open_aexpr_notin_rec; auto.
Qed.

Lemma inst_e_strengthenₖ : forall Θ x k e' e
  , Θ; ⧼^x⧽= k ⊢ e' ⇝ e → x `notin` fkv_aexpr e'
  → Θ  ⊢ e' ⇝ e.
Proof.
  intros.
  dependent induction H; simpl in *; eauto 4 with inst_strengthen.
  - destruct H0; [> inversion H0 | eauto].
  - pick fresh x' and apply ie_pi;
      eauto using fkv_open_aexpr_notin.
  - pick fresh x' and apply ie_abs;
      eauto using fkv_open_aexpr_notin.
Qed.

Lemma fex_open_aexpr_notin_rec : forall x e2 e1 n
  , x `notin` fex_aexpr e1
  → x `notin` fex_aexpr e2
  → x `notin` fex_aexpr (open_aexpr_wrt_aexpr_rec n e2 e1).
Proof.
  induction e1; simpl; intros; eauto.
  - destruct (lt_eq_lt_dec n n0). destruct s. all: auto.
Qed.

Lemma fex_open_aexpr_notin : forall x e1 e2
  , x `notin` fex_aexpr e1
  → x `notin` fex_aexpr e2
  → x `notin` fex_aexpr (e1 ^^′ e2).
Proof.
  intros.
  apply fex_open_aexpr_notin_rec; auto.
Qed.

Lemma inst_e_strengthenₓ : forall Θ x k e e1 e2
  , Θ; ^x :_ k = e ⊢ e1 ⇝ e2
  → x `notin` fex_aexpr e1
  → Θ ⊢ e1 ⇝ e2.
Proof.
  intros * H.
  dependent induction H; intros; simpl in *;
    eauto 4 using inst_k_strengthenₓ.
  - destruct H0.
    + inversion H0. subst. exfalso. auto.
    + eauto.
  - pick fresh x' and apply ie_pi;
      eauto using fex_open_aexpr_notin.
  - pick fresh x' and apply ie_abs;
      eauto using fex_open_aexpr_notin.
Qed.


#[export]
Hint Resolve
  inst_e_strengthenᵥ
  inst_e_strengthenₖ
  inst_e_strengthenₓ
  : inst_strengthen.

Lemma inst_c_strengthenᵥ : forall Θ x A c' c,
    Θ; x :_ A ⊢ c' ⟿′ c → Θ ⊢ c' ⟿′ c.
Proof.
  intros.
  dependent induction H; eauto with inst_strengthen.
Qed.

Lemma inst_c_strengthenₖ : forall Θ x k c' c
  , Θ; ⧼^x⧽= k ⊢ c' ⟿′ c
  → x `notin` fkv_cont c'
  → Θ ⊢ c' ⟿′ c.
Proof.
  intros.
  dependent induction H; simpl in *;
    eauto with inst_strengthen.
Qed.

Lemma inst_c_strengthenₓ : forall Θ x k e c' c
  , Θ; ^x :_ k = e ⊢ c' ⟿′ c
  → x `notin` fex_cont c'
  → Θ ⊢ c' ⟿′ c.
Proof.
  intros.
  dependent induction H; simpl in *;
    eauto with inst_strengthen.
Qed.

#[export]
Hint Resolve
  inst_c_strengthenᵥ
  inst_c_strengthenₖ
  inst_c_strengthenₓ
  : inst_strengthen.


Lemma inst_e_subst: forall Θ e' e v v' x
  , Θ ⊢ e' ⇝ e
  → Θ ⊢ v' ⇝ v
  → x `notin` il_dom Θ
  → Θ ⊢ subst_aexpr v' x e' ⇝ subst_expr v x e.
Proof.
  induction 1; simpl; intros; eauto.
  - unfold eq_dec in *.
    destruct (EqDec_eq_of_X x0 x); auto.
  - admit.
  - pick fresh x' and apply ie_pi.
    + eauto.
    + rewrite subst_expr_open_expr_wrt_expr_var; eauto.
      rewrite subst_aexpr_open_aexpr_wrt_aexpr_var; eauto.
      admit. admit.
  - pick fresh x' and apply ie_abs.
    + rewrite subst_expr_open_expr_wrt_expr_var; eauto.
      rewrite subst_aexpr_open_aexpr_wrt_aexpr_var; eauto.
      admit. admit.
Admitted.

Lemma inst_e_rename : forall Θ e' e x x'
  , Θ ⊢ e' ⇝ e
  → x `notin` il_dom Θ
  → Θ ⊢ subst_aexpr (`′ x') x e' ⇝ subst_expr (` x') x e.
Proof.
  intros.
  apply inst_e_subst; eauto with wf_il.
  Unshelve. exact k_star.
Qed.

Lemma inst_e_rev_subst' : forall e', lc_aexpr e' → forall Θ x v' e0
  , Θ ⊢ subst_aexpr v' x e' ⇝ e0
  → exists e v
      , Θ ⊢ v' ⇝ v
      ∧ Θ ⊢ e' ⇝ e
      ∧ e0 = subst_expr v x e.
Proof.
  induction 1; simpl; intros.
  - destruct (x == x0).
    + subst.
      exists `x0, e0. repeat split.
      * auto.
      * eauto with wf_il.
      * simpl. admit.
    + admit.
Admitted.

Lemma inst_e_rev_subst : forall Θ e' x v' e0
  , Θ ⊢ subst_aexpr v' x e' ⇝ e0
  → exists e v
      , Θ ⊢ v' ⇝ v
      ∧ Θ ⊢ e' ⇝ e
      ∧ e0 = subst_expr v x e.
Proof.
Admitted.
