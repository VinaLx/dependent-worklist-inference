Require Import worklist.
Require Import decl_worklist.
Require simplified_ind.


Inductive kind_iso : kind → akind → Prop :=
| kiso_star : kind_iso k_star ak_star
| kiso_box : kind_iso k_box ak_box
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

Inductive ss_entry :=
| sse_v (A : expr)
| sse_ex (A : expr) (e : expr)
| sse_kv (k : kind)
.

Inductive lc_sse : ss_entry → Prop :=
| lc_sse_v : forall A, lc_expr A → lc_sse (sse_v A)
| lc_sse_ex : forall A e, lc_expr A → lc_expr e → lc_sse (sse_ex A e)
| lc_sse_kv : forall k, lc_sse (sse_kv k)
.

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
Fixpoint ss_to_ctx (s : subst_set) : context :=
  match s with
  | nil => ctx_nil
  | s' ; x : A ! => ss_to_ctx s' , x : A
  | s' ; x : A ≔ e => ss_to_ctx s'
  | s' ; x ≔ ⧼k⧽ => ss_to_ctx s'
  end
.

(* syntactic well-formedness of substitution set *)
Inductive wf_ss : subst_set → Prop :=
| wf_ss_nil : wf_ss nil
| wf_ss_v  : forall x A Θ
  , wf_ss Θ → x `notin` dom Θ → lc_expr A
  → wf_ss (Θ; x : A !)
| wf_ss_kv : forall x k Θ
  , wf_ss Θ → x `notin` dom Θ
  → wf_ss (Θ; x ≔ ⧼k⧽)
| wf_ss_ex : forall x A e Θ
  , wf_ss Θ
  → x `notin` dom Θ → mono_type e
  → wf_ss (Θ; x : A ≔ e)
.

Lemma wf_lc_sse : forall Θ x e,
  binds x e Θ → wf_ss Θ → lc_sse e.
Proof.
Admitted.

(* 'inst' is short for 'instantiate' *)
Reserved Notation "T ⊩ e1 ⇝ e2" (at level 65, e1 at level 58, no associativity).
Inductive inst_expr : subst_set → aexpr → expr → Prop :=
| inste_var : forall Θ x,     wf_ss Θ → inst_expr Θ `′x `x
| inste_ex  : forall Θ x A e, wf_ss Θ → x : A ≔ e ∈ Θ → inst_expr Θ  `^x  e
| inste_k   : forall Θ x k,   wf_ss Θ → x ≔ ⧼k⧽ ∈ Θ → inst_expr Θ ⧼`^x⧽ ⧼k⧽
| inste_num : forall Θ n,     wf_ss Θ → inst_expr Θ (ae_num n) (e_num n)
| inste_int : forall Θ,       wf_ss Θ → inst_expr Θ ae_int e_int
| inste_bot : forall Θ A' A,
    inst_expr Θ A' A → inst_expr Θ (ae_bot A') (e_bot A)
| inste_app : forall Θ f' f a' a
  , inst_expr Θ f' f → inst_expr Θ a' a
  → inst_expr Θ (ae_app f' a') (e_app f a)
| inste_castup : forall Θ A' A e' e
  , inst_expr Θ A' A → inst_expr Θ e' e
  → inst_expr Θ (ae_castup A' e') (e_castup A e)
| inste_castdn : forall Θ e' e,
    inst_expr Θ e' e → inst_expr Θ (ae_castdn e') (e_castdn e)
| inste_abs : forall L Θ A' A e' e B' B
  , inst_expr Θ A' A
  → (forall x, x `notin` L → inst_expr Θ (e' ^`′ x) (e ^` x))
  → (forall x, x `notin` L → inst_expr Θ (B' ^`′ x) (B ^` x))
  → inst_expr Θ (λ′ A', e' : B') (λ_ A, e : B)
| inste_bind : forall L Θ A' A e' e B' B
  , inst_expr Θ A' A
  → (forall x, x `notin` L → inst_expr Θ (e' ^`′ x) (e ^` x))
  → (forall x, x `notin` L → inst_expr Θ (B' ^`′ x) (B ^` x))
  → inst_expr Θ (Λ′ A', e' : B') (Λ A, e : B)
| inste_pi : forall L Θ A' A B' B
  , inst_expr Θ A' A
  → (forall x, x `notin` L → inst_expr Θ (B' ^`′ x) (B ^` x))
  → inst_expr Θ (ae_pi A' B') (e_pi A B)
| inst_all : forall L Θ A' A B' B
  , inst_expr Θ A' A
  → (forall x, x `notin` L → inst_expr Θ (B' ^`′ x) (B ^` x))
  → inst_expr Θ (ae_all A' B') (e_all A B)
where "T ⊩ e1 ⇝ e2" := (inst_expr T e1 e2) : type_scope
.

Lemma inst_e_wf_ss : forall Θ e' e,
  Θ ⊩ e' ⇝ e → wf_ss Θ.
Proof with induction 1; auto.
  idtac...
Qed.

Require Import Program.Tactics.

Scheme lc_ae_body_mut := Induction for lc_aexpr Sort Prop
  with lc_body_ae_mut := Induction for lc_abody Sort Prop.

Hint Extern 2 =>
  match goal with
  | |- context [open_body_wrt_expr _ _] =>
    unfold open_body_wrt_expr; simpl
  | |- context [open_abody_wrt_aexpr _ _] =>
    unfold open_abody_wrt_aexpr; simpl
end : lc
.

Hint Resolve lc_ae_abs_exists : lc.
Hint Resolve lc_ae_bind_exists : lc.
Hint Resolve lc_e_abs_exists : lc.
Hint Resolve lc_e_bind_exists : lc.

Lemma inst_ae_lc : forall Θ e' e,
  Θ ⊩ e' ⇝ e → lc_aexpr e'.
Proof.
  induction 1;
    solve [auto | pick fresh x; eauto 6 with lc].
Qed.


Lemma inst_e_lc : forall Θ e' e,
    Θ ⊩ e' ⇝ e → lc_expr e.
Proof.
  induction 1; try solve [auto | pick fresh x; eauto 6 with lc].
Admitted.


#[export]
Hint Resolve inst_e_wf_ss : core.

Reserved Notation "T ⊩ ob ⇝? dob" (at level 65, ob at level 58, no associativity).
Inductive inst_obind : subst_set → obind → obindd → Prop :=
| instob_none : forall Θ, inst_obind Θ ob_none dob_none
| instob_bind : forall Θ x A' A, inst_obind Θ (x :?′ A') (x :? A)
where "T ⊩ ob ⇝? dob" := (inst_obind T ob dob) : type_scope
.

Reserved Notation "T ⊩ w1 ⇝′ w2" (at level 65, w1 at level 58).
Reserved Notation "T1 ⊩ G1 ⟿ G2 ⫣ T2" (at level 65, G1 at level 58, G2 at level 58).
Inductive inst_work : subst_set → work → dwork → Prop :=
| instw_check : forall Θ ob ob' e1 e1' e2 e2' A A'
  , inst_obind Θ ob' ob → inst_expr Θ A' A
  → inst_expr Θ e1' e1 → inst_expr Θ e2' e2
  → inst_work Θ (ob' ⊢? e1' <: e2' ⇐′ A') (ob ⊢? e1 <: e2 ⇐ A)
| instw_cpct  : forall Θ A A' B B'
  , inst_expr Θ A' A → inst_expr Θ B' B
  → inst_work Θ (A' ≲′ B') (A ≲ B)
| instw_infer : forall L Θ Θ' e1 e1' e2 e2' c c'
  , inst_expr Θ e1' e1 → inst_expr Θ e2' e2
  → (forall x, x `notin` L → inst_wl Θ (c' $′ `′x) (c $ `x) Θ')
  → inst_work Θ (e1' <: e2' ⇒′ c') (e1 <: e2 ⇒ c)
| instw_iapp : forall L Θ Θ' A A' e e1' e2' c c'
  , inst_expr Θ e1' e → inst_expr Θ e2' e
  → (forall x, x `notin` L → inst_wl Θ (c' $′ `′x) (c $ `x) Θ')
  → inst_work Θ (A' ⋅ e1' & e2' ⇒′ c') (A ⋅ e ⇒ c)
| instw_red : forall L Θ Θ' A A' c c'
  , inst_expr Θ A' A
  → (forall x, x `notin` L → inst_wl Θ (c' $′ `′x) (c $ `x) Θ')
  → inst_work Θ (A' ⟼′ c') (A ⟼ c)
where "T ⊩ w1 ⇝′ w2" := (inst_work T w1 w2) : type_scope
with inst_wl  : subst_set → worklist → dworklist → subst_set → Prop :=
| instwl_nil  : forall Θ, inst_wl Θ wl_nil dwl_nil Θ
| instwl_cons : forall Θ Θ' Γ Γ' w w'
  , inst_wl Θ Γ' Γ Θ' → inst_work Θ' w' w
  → inst_wl Θ (Γ' ⊨′ w') (Γ ⊨ w) Θ'
| instwl_var  : forall Θ Θ' Γ Γ' x A A'
  , inst_wl Θ Γ' Γ Θ' → x `notin` dom Θ → inst_expr Θ' A' A
  → inst_wl Θ (Γ' ,′ x :′ A') (Γ ,' x : A) (Θ'; x : A!)
| instwl_kv : forall Θ Θ' Γ Γ' x k
  , inst_wl Θ Γ' Γ Θ' → x `notin` dom Θ
  → inst_wl Θ (Γ' ,′ ⧼^x⧽) Γ (Θ'; x ≔ ⧼k⧽)
| instwl_ex : forall Θ Θ' Γ Γ' x A' A e
  , mono_type e
  → inst_wl Θ Γ' Γ Θ' → x `notin` dom Θ → inst_expr Θ' A' A
  → inst_wl Θ (Γ' ,′ ^x :′ A') Γ (Θ'; x : A ≔ e)
where "T1 ⊩ G1 ⟿ G2 ⫣ T2" := (inst_wl T1 G1 G2 T2) : type_scope
.

#[export]
Hint Constructors inst_expr inst_obind inst_work inst_wl : core.


Definition transfer' (Γ' : worklist) (Γ : dworklist) : Prop :=
  exists Θ, inst_wl nil Γ' Γ Θ.

Hint Extern 2 (_ = _) => simpl; congruence : core.

Lemma inst_e_det : forall e' Θ e1 e2,
  uniq Θ → Θ ⊩ e' ⇝ e1 → Θ ⊩ e' ⇝ e2 → e1 = e2.
Proof.
Admitted.



Lemma inst_wl_split : forall Γ1' Γ2' Γ Θ Θ'
  , Θ ⊩ Γ1' ⫢′ Γ2' ⟿ Γ ⫣ Θ'
  → exists Γ1 Γ2 Θ0
    , Γ = Γ1 ⫢ Γ2
    ∧ Θ  ⊩ Γ1' ⟿ Γ1 ⫣ Θ0
    ∧ Θ0 ⊩ Γ2' ⟿ Γ2 ⫣ Θ'.
Proof.
  induction Γ2'; simpl; intros.
  - exists Γ, dwl_nil, Θ'; simpl; solve [auto].
  - inversion H; subst.
    pose proof (IHΓ2' _ _ _ H3) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
    exists Γ1, (Γ2 ⊨ w0), Θ0. auto.
  - destruct b.
    + inversion H; subst.
      pose proof (IHΓ2' _ _ _ H4) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
      exists Γ1, (Γ2 ,' x : A0), Θ0. admit.
    + inversion H; subst.
      pose proof (IHΓ2' _ _ _ H5) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
      exists Γ1, Γ2, Θ0. admit.
    + inversion H; subst.
      pose proof (IHΓ2' _ _ _ H3) as (Γ1 & Γ2 & Θ0 & E & Inst1 & Inst2).
      exists Γ1, Γ2, Θ0. admit.
Admitted.

Scheme wl_mut   := Induction for worklist Sort Prop
  with work_mut := Induction for work     Sort Prop.

Scheme wins_mut   := Induction for inst_work Sort Prop
  with wlinst_mut := Induction for inst_wl   Sort Prop.

Lemma inst_wl_ss_expand : forall Θ Γ' Γ Θ'
  , Θ ⊩ Γ' ⟿ Γ ⫣ Θ'
  → exists Θ0, Θ ;; Θ0 = Θ'.
Proof.
  induction 1; try pose proof IHinst_wl as (Θ0 & <-).
  - now exists nil.
  - assumption.
  - now exists (Θ0; x : A !).
  - now exists (Θ0; x ≔ ⧼k⧽).
  - now exists (Θ0; x : A ≔ e).
Qed.

Lemma inst_e_weakening : forall Θ e' e Θ',
  Θ ⊩ e' ⇝ e → Θ ;; Θ' ⊩ e' ⇝ e.
Proof.
  induction 1; eauto.
Admitted.

#[local]
Hint Resolve inst_e_weakening : inst_weakening.

Lemma inst_ob_weakening : forall Θ Θ' ob' ob,
  Θ ⊩ ob' ⇝? ob → Θ ;; Θ' ⊩ ob' ⇝? ob.
Proof.
  induction 1; eauto.
Qed.

#[local]
Hint Resolve inst_ob_weakening : inst_weakening.

(* doable *)
Lemma inst_w_weakening : forall Θ w' w Θ',
  Θ ⊩ w' ⇝′ w → Θ ;; Θ' ⊩ w' ⇝′ w.
Proof.
  intros.
  pattern Θ, w', w, H.
  apply wins_mut with
      (P0 := fun Θ Γ' Γ Θ1 (_ : Θ ⊩ Γ' ⟿ Γ ⫣ Θ1) =>
               forall Θ0, Θ1 = Θ ;; Θ0 → Θ ⊩ Γ' ⟿ Γ ⫣ Θ ;; Θ0 → Θ ;; Θ' ⊩ Γ' ⟿ Γ ⫣ Θ ;; Θ' ;; Θ0);
    intros.
Admitted.

Lemma inst_e_rev_subst : forall v' v x e' e0 Θ
  , Θ ⊩ [v' /′ x] e' ⇝ e0 → Θ ⊩ v' ⇝ v
  → exists e, [v /' x] e = e0 ∧ Θ ⊩ e' ⇝ e.
Proof.
  intros * H.
  assert (lc_aexpr e') by admit.
  generalize dependent e0. generalize dependent Θ.
  induction H0; simpl; intros.
  - exists (` x0). simpl. destruct (x0 == x).
    + admit.
    + admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
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
