Require Import worklist.
Require Import decl_worklist.
Require simplified_ind.
Require Import lc.
Require Import Program.Equality.
Require Import list_properties.

(*
Inductive kind_iso : bkind → akind → Prop :=
| kiso_star : kind_iso bk_star ak_star
| kiso_box : kind_iso bk_box ak_box
.

Inductive expr_iso : expr → aexpr → Prop :=
| eiso_var  : forall x, expr_iso `x `′x
| eiso_kind : forall k k', kind_iso k k' → expr_iso ⧼k⧽ ⧼k'⧽′
| eiso_num : forall n, expr_iso (e_num n) (ae_num n)
| eiso_int : expr_iso e_int ae_int
| eiso_bot : forall A A', expr_iso A A' → expr_iso (e_bot A) (ae_bot A')
| eiso_app : forall f f' e e'
  , expr_iso f f' → expr_iso e e' → expr_iso (e_app f e) (ae_app f' e')
| eiso_abs : forall L A A' e e' B B'
  , expr_iso A A'
  → (forall x, x `notin` L → expr_iso (e ^` x) (e' ^`′ x))
  → (forall x, x `notin` L → expr_iso (B ^` x) (B' ^`′ x))
  → expr_iso (e_abs A (b_anno e B)) (ae_abs A' (ab_anno e' B'))
| eiso_pi : forall L A A' B B'
  , expr_iso A A'
  → (forall x, x `notin` L → expr_iso (B ^` x) (B' ^`′ x))
  → expr_iso (e_pi A B) (ae_pi A' B')
| eiso_bind : forall L A A' e e' B B'
  , expr_iso A A'
  → (forall x, x `notin` L → expr_iso (e ^` x) (e' ^`′ x))
  → (forall x, x `notin` L → expr_iso (B ^` x) (B' ^`′ x))
  → expr_iso (e_bind A (b_anno e B)) (ae_bind A' (ab_anno e' B'))
| eiso_all : forall L A A' B B'
  , expr_iso A A'
  → (forall x, x `notin` L → expr_iso (B ^` x) (B' ^`′ x))
  → expr_iso (e_all A B) (ae_all A' B')
| eiso_castup : forall A A' e e'
  , expr_iso A A' → expr_iso e e'
  → expr_iso (e_castup A e) (ae_castup A' e')
| eiso_castdn : forall e e'
  , expr_iso e e' → expr_iso (e_castdn e) (ae_castdn e')
.

Inductive obind_iso : obindd → obind → Prop :=
| obiso_none : obind_iso dob_none ob_none
| obiso_bind : forall x A A'
  , expr_iso A A' → obind_iso (x :? A) (x :?′ A')
.

Inductive work_iso : dwork → work → Prop :=
| wiso_check : forall ob ob' e1 e1' e2 e2' A A'
  , obind_iso ob ob' → expr_iso e1 e1'
  → expr_iso e2 e2' → expr_iso A A'
  → work_iso (ob ⊢? e1 <: e2 ⇐ A) (ob' ⊢? e1' <: e2' ⇐′ A')
| wiso_compact : forall A A' B B'
  , expr_iso A A' → expr_iso B B' → work_iso (A ≲ B) (A' ≲′ B')
| wiso_infer : forall L e1 e1' e2 e2' c c'
  , expr_iso e1 e1' → expr_iso e2 e2'
  → (forall x, x `notin` L → worklist_iso (c $ `x) (c' $′ `′x))
  → work_iso (e1 <: e2 ⇒ c) (e1' <: e2' ⇒′ c')
| wiso_iapp : forall L A A' e e1' e2' c c'
  , expr_iso A A' → expr_iso e e1' → expr_iso e e2'
  → (forall x, x `notin` L → worklist_iso (c $ `x) (c' $′ `′x))
  → work_iso (A ⋅ e ⇒ c) (A' ⋅ e1' & e2' ⇒′ c')
| wiso_reduce : forall L A A' c c'
  , expr_iso A A'
  → (forall x, x `notin` L → worklist_iso (c $ `x) (c' $′ `′x))
  → work_iso (A ⟼ c) (A' ⟼′ c')
with worklist_iso : dworklist → worklist → Prop :=
| wliso_nil : worklist_iso dwl_nil wl_nil
| wliso_work : forall Γ Γ' w w'
  , worklist_iso Γ Γ' → work_iso w w'
  → worklist_iso (Γ ⊨ w) (Γ' ⊨′ w')
| wliso_bind : forall Γ Γ' x A A'
  , worklist_iso Γ Γ' → expr_iso A A'
  → worklist_iso (Γ ,' x : A) (Γ' ,′ x :′ A')
.

#[export]
Hint Constructors work_iso worklist_iso obind_iso expr_iso kind_iso : core.

Reserved Notation "wl ⟿ dwl" (at level 65, no associativity).
Inductive transfer : worklist → dworklist → Prop :=
| trf_stop : forall Γ Γ', worklist_iso Γ Γ' → Γ' ⟿ Γ
| trf_ex : forall Γ Γ1 Γ1' Γ2' x A A' t t'
  , worklist_iso Γ1 Γ1' → expr_iso A A'
  → (to_ctx Γ1 ⊢ t <: t ⇐ A) → expr_iso t t' → mono_type t
  → Γ1'             ⫢′ ⟦t' /′ ^x⟧ Γ2' ⟿ Γ
  → Γ1' ,′ ^x :′ A' ⫢′            Γ2' ⟿ Γ
| trf_k : forall Γ Γ1 Γ1' Γ2' x k k'
  , worklist_iso Γ1 Γ1' → kind_iso k k'
  → Γ1'         ⫢′ ⟦k' /′ ⧼x⧽⟧ Γ2' ⟿ Γ
  → Γ1' ,′ ⧼^x⧽ ⫢′             Γ2' ⟿ Γ
where "wl ⟿ dwl" := (transfer wl dwl)
.

#[export]
Hint Constructors transfer : core.
 *)

Inductive ss_entry :=
| sse_v (A : bexpr)
| sse_ex (A : bexpr) (e : bexpr)
| sse_kv (k : bkind)
.

Inductive lc_sse : ss_entry → Prop :=
| lc_sse_v : forall A, lc_bexpr A → lc_sse (sse_v A)
| lc_sse_ex : forall A e, lc_bexpr A → lc_bexpr e → lc_sse (sse_ex A e)
| lc_sse_kv : forall k, lc_sse (sse_kv k)
.

Hint Constructors lc_sse : core.

Definition subst_set := list (var * ss_entry).

Notation ": A !" :=
  (sse_v A) (at level 52, A at level 50, no associativity).

Notation ": A ≔ e" :=
  (sse_ex A e) (at level 52, A at level 50, no associativity).
Notation " ≔ ⧼ k ⧽" :=
  (sse_kv k) (at level 52, no associativity).

Declare Scope subst_set_scope.
Delimit Scope subst_set_scope with subst.
Bind Scope subst_set_scope with subst_set.

Notation "s1 ;; s2" := (app s2 s1)
  (at level 58, left associativity) : subst_set_scope.

Notation "s ; x e" := (cons (pair x e) s)
  ( at level 58, x at level 0, e at level 52, left associativity) : subst_set_scope.

Notation "x e ∈ s" := (binds x e s)
  (at level 65, e at level 52, no associativity) : type_scope.

Open Scope subst_set_scope.


(* 'ss' is short for 'substitution set' *)
Fixpoint ss_to_ctx (s : subst_set) : bcontext :=
  match s with
  | nil => bctx_nil
  | s' ; x : A ! => ss_to_ctx s' ,' x : A
  | s' ; x : A ≔ e => ss_to_ctx s'
  | s' ; x ≔ ⧼k⧽ => ss_to_ctx s'
  end
.

(* syntactic well-formedness of substitution set *)
Inductive wf_ss : subst_set → Prop :=
| wf_ss_nil : wf_ss nil
| wf_ss_v  : forall x A Θ
  , wf_ss Θ → x `notin` dom Θ → lc_bexpr A
  → wf_ss (Θ; x : A !)
| wf_ss_kv : forall x k Θ
  , wf_ss Θ → x `notin` dom Θ
  → wf_ss (Θ; x ≔ ⧼k⧽)
| wf_ss_ex : forall x A e Θ
  , wf_ss Θ → x `notin` dom Θ
  → lc_bexpr A → mono_btype e
  → wf_ss (Θ; x : A ≔ e)
.

Lemma wf_uniq : forall Θ,
    wf_ss Θ → uniq Θ.
Proof.
  induction 1; eauto.
Qed.

#[export]
Hint Resolve wf_uniq : core.

Lemma wf_lc_sse : forall Θ x e,
  binds x e Θ → wf_ss Θ → lc_sse e.
Proof.
  induction 2; inversion H; subst;
    (* simplifying equality comes from binds *)
    try match goal with
    | E : _ = _ |- _ => inversion E
    end; eauto with lc.
Qed.

(* 'inst' is short for 'instantiate' *)
Reserved Notation "T ⊩ e1 ⇝ e2" (at level 65, e1 at level 58, no associativity).
Inductive inst_expr : subst_set → aexpr → bexpr → Prop :=
| inste_var : forall Θ x,     wf_ss Θ → inst_expr Θ `′x `'x
| inste_ex  : forall Θ x A e, wf_ss Θ → x : A ≔ e ∈ Θ → inst_expr Θ  `^x  e
| inste_k   : forall Θ x k,   wf_ss Θ → x ≔ ⧼k⧽ ∈ Θ → inst_expr Θ ⧼`^x⧽ ⧼k⧽'
| inste_star: forall Θ, wf_ss Θ → inst_expr Θ ⋆′ ⋆'
| inste_box : forall Θ, wf_ss Θ → inst_expr Θ ◻′ ◻'
| inste_num : forall Θ n,     wf_ss Θ → inst_expr Θ (ae_num n) (be_num n)
| inste_int : forall Θ, wf_ss Θ → inst_expr Θ ae_int be_int
| inste_bot : forall Θ, wf_ss Θ → inst_expr Θ ae_bot be_bot
| inste_app : forall Θ f' f a' a
  , inst_expr Θ f' f → inst_expr Θ a' a
  → inst_expr Θ (ae_app f' a') (be_app f a)
| inste_castup : forall Θ e' e
  , inst_expr Θ e' e → inst_expr Θ (ae_castup e') (be_castup e)
| inste_castdn : forall Θ e' e,
    inst_expr Θ e' e → inst_expr Θ (ae_castdn e') (be_castdn e)
| inste_abs : forall L Θ e' e
  , (forall x, x `notin` L → inst_expr Θ (e' ^`′ x) (e ^`' x))
  → inst_expr Θ (ae_abs e') (be_abs e)
| inste_bind : forall L Θ e' e
  , (forall x, x `notin` L → inst_expr Θ (e' ^`′ x) (e ^`' x))
  → inst_expr Θ (ae_bind e') (be_bind e)
| inste_pi : forall L Θ A' A B' B
  , inst_expr Θ A' A
  → (forall x, x `notin` L → inst_expr Θ (B' ^`′ x) (B ^`' x))
  → inst_expr Θ (ae_pi A' B') (be_pi A B)
| inst_all : forall L Θ A' A B' B
  , inst_expr Θ A' A
  → (forall x, x `notin` L → inst_expr Θ (B' ^`′ x) (B ^`' x))
  → inst_expr Θ (ae_all A' B') (be_all A B)
| inst_anno : forall Θ e' e A' A
  , inst_expr Θ e' e → inst_expr Θ A' A
  → inst_expr Θ (e' ::′ A') (e ::' A)
where "T ⊩ e1 ⇝ e2" := (inst_expr T e1 e2) : type_scope
.

Lemma inst_e_wf_ss : forall Θ e' e,
    Θ ⊩ e' ⇝ e → wf_ss Θ.
Proof.
  induction 1; pick fresh x'; eauto.
Qed.

#[export]
Hint Resolve inst_e_wf_ss : core.

Require Import Program.Tactics.

Hint Resolve lc_ae_abs_exists : lc.
Hint Resolve lc_ae_bind_exists : lc.
Hint Resolve lc_be_abs_exists : lc.
Hint Resolve lc_be_bind_exists : lc.

Lemma inst_ae_lc : forall Θ e' e,
  Θ ⊩ e' ⇝ e → lc_aexpr e'.
Proof.
  induction 1;
    solve [auto | pick fresh x; eauto 6 with lc].
Qed.


Lemma inst_e_lc : forall Θ e' e,
    Θ ⊩ e' ⇝ e → lc_bexpr e.
Proof.
  induction 1; try solve [auto | pick fresh x; eauto 6 with lc].
  - apply wf_lc_sse in H0.
    + now inversion H0.
    + assumption.
Qed.

Reserved Notation "T ⊩ ob ⇝? dob" (at level 65, ob at level 58, no associativity).
Inductive inst_obind : subst_set → obind → obindd → Prop :=
| instob_none : forall Θ, inst_obind Θ ob_none dob_none
| instob_bind : forall Θ x A' A, inst_obind Θ (x :?′ A') (x :? A)
where "T ⊩ ob ⇝? dob" := (inst_obind T ob dob) : type_scope
.

Reserved Notation "T1 ⊩ w1 ⇝′ w2 ⫣ T2" (at level 65, w1 at level 58).
Reserved Notation "T1 ⊩ G1 ⟿ G2 ⫣ T2" (at level 65, G1 at level 58, G2 at level 58).
Inductive inst_work : subst_set → work → dwork → subst_set → Prop :=
| instw_check : forall Θ ob ob' e1 e1' e2 e2' A A'
  , inst_obind Θ ob' ob → inst_expr Θ A' A
  → inst_expr Θ e1' e1 → inst_expr Θ e2' e2
  → inst_work Θ (ob' ⊢? e1' <: e2' ⇐′ A') (ob ⊢? e1 <: e2 ⇐ A) Θ
| instw_cpct  : forall Θ A A' B B'
  , inst_expr Θ A' A → inst_expr Θ B' B
  → inst_work Θ (A' ≲′ B') (A ≲ B) Θ
| instw_infer : forall L Θ Θ' e1 e1' e2 e2' c c'
  , inst_expr Θ e1' e1 → inst_expr Θ e2' e2
  → (forall x, x `notin` L → inst_wl Θ (c' $′ `′x) (c $ `'x) Θ')
  → inst_work Θ (e1' <: e2' ⇒′ c') (e1 <: e2 ⇒ c) Θ'
| instw_iapp : forall L Θ Θ' A A' e e1' e2' c c'
  , inst_expr Θ e1' e → inst_expr Θ e2' e
  → (forall x, x `notin` L → inst_wl Θ (c' $′ `′x) (c $ `'x) Θ')
  → inst_work Θ (A' ⋅ e1' & e2' ⇒′ c') (A ⋅ e ⇒ c) Θ'
| instw_red : forall L Θ Θ' A A' c c'
  , inst_expr Θ A' A
  → (forall x, x `notin` L → inst_wl Θ (c' $′ `′x) (c $ `'x) Θ')
  → inst_work Θ (A' ⟼′ c') (A ⟼ c) Θ'
where "T1 ⊩ w1 ⇝′ w2 ⫣ T2" := (inst_work T1 w1 w2 T2) : type_scope
with inst_wl  : subst_set → worklist → dworklist → subst_set → Prop :=
| instwl_nil  : forall Θ, inst_wl Θ wl_nil dwl_nil Θ
| instwl_cons : forall Θ Θ' Θ'' Γ Γ' w w'
  , inst_wl Θ Γ' Γ Θ' → inst_work Θ' w' w Θ''
  → inst_wl Θ (Γ' ⊨′ w') (Γ ⊨ w) Θ''
| instwl_var  : forall Θ Θ' Γ Γ' x A A'
  , inst_wl Θ Γ' Γ Θ' → x `notin` dom Θ' → inst_expr Θ' A' A
  → inst_wl Θ (Γ' ,′ x :′ A') (Γ ,′' x : A) (Θ'; x : A!)
| instwl_kv : forall Θ Θ' Γ Γ' x k
  , inst_wl Θ Γ' Γ Θ' → x `notin` dom Θ'
  → inst_wl Θ (Γ' ,′ ⧼^x⧽) Γ (Θ'; x ≔ ⧼k⧽)
| instwl_ex : forall Θ Θ' Γ Γ' x A' A e
  , mono_btype e
  → inst_wl Θ Γ' Γ Θ' → x `notin` dom Θ' → inst_expr Θ' A' A
  → inst_wl Θ (Γ' ,′ ^x :′ A') Γ (Θ'; x : A ≔ e)
where "T1 ⊩ G1 ⟿ G2 ⫣ T2" := (inst_wl T1 G1 G2 T2) : type_scope
.

#[export]
Hint Constructors inst_expr inst_obind inst_work inst_wl : core.


Definition transfer' (Γ' : worklist) (Γ : dworklist) : Prop :=
  exists Θ, inst_wl nil Γ' Γ Θ.

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


Lemma inst_e_rev_subst : forall v' v x e'
  , lc_aexpr e' → forall e0 Θ, x `notin` fv_bexpr e0
  → Θ ⊩ [v' /′ x] e' ⇝ e0 → Θ ⊩ v' ⇝ v
  → exists e, [v /' x] e = e0 ∧ Θ ⊩ e' ⇝ e.
Proof.
  intros * Lc.
  induction Lc; simpl; intros * Fr He Hv.
  - exists (`' x0). simpl.
    unfold eq_dec in *. destruct (EqDec_eq_of_X x0 x).
    + assert (v = e0) by (eapply inst_e_det with (Θ := Θ); eauto).
      eauto.
    + inversion He. now subst.
  - destruct k; inversion He; subst.
    + exists ⋆'; eauto.
    + exists ◻'; eauto.
    + exists ⧼ k ⧽'; eauto.
  - inversion He. subst.
    exists e0. eauto with lngen.
  - inversion He. subst.
    exists (be_num n); eauto.
  - inversion He. subst.
    exists be_int; eauto.
  - inversion He; subst.
    exists be_bot; eauto.
  - inversion He. subst. simpl in Fr.
    edestruct (IHLc1 f) as (e1' & E1 & Trans1); eauto.
    edestruct (IHLc2 a) as (e2' & E2 & Trans2); eauto.
    exists (be_app e1' e2'). simpl. split. congruence.
    eauto.
  - inversion He. subst. simpl in Fr.
    pick fresh x' for (add x L).
    assert (Θ ⊩ ([v' /′ x] e) ^`′ x' ⇝ e1 ^`' x').
    eapply H3. auto.
    assert (([v' /′ x] e) ^`′ x' = [v' /′ x] e ^`′ x') by admit.
    rewrite H2 in H1.
    destruct (H0 x' (e1 ^`' x') Θ) as (e1' & E & Trans).
    admit. auto. auto.
    exists (be_abs (close_bexpr_wrt_bexpr x' e1')). split.
    simpl. admit.
    econstructor. intros. admit.
  - admit.
Admitted.

Lemma inst_wl_rev_subst : forall Γ' x e' e Γ0 Θ Θ'
  , Θ ⊩ subst_worklist e' x Γ' ⟿ Γ0 ⫣ Θ'
  → Θ ⊩ e' ⇝ e
  → exists Γ
    , subst_dworklist e x Γ = Γ0
    ∧ Θ ⊩ Γ' ⟿ Γ ⫣ Θ'.
Proof.
  intro Γ'.
  pattern Γ'.
  apply wl_mut with
    (P0 := fun w' =>
      forall x e' e w0 Θ
      , Θ ⊩ subst_work e' x w' ⇝′ w0
        → Θ ⊩ e' ⇝ e
        → exists w, subst_dwork e x w = w0 ∧ Θ ⊩ w' ⇝′ w); simpl; intros.
  - inversion H; subst.
    exists dwl_nil; simpl; repeat split; auto.
  - simpl in H1. inversion H1; subst. admit.
  - destruct b; inversion H0; subst; simpl in *; admit.
  - admit.
  -
Admitted.
