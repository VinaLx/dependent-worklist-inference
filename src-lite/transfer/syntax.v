Require Export worklist.
Require Export decl_worklist.
Require Import lc.
Require Import ln_utils.


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

(* 'ss' is short for 'substitution set' *)
Inductive ss_entry :=
| sse_ex (e : bexpr)
| sse_kv (k : bkind)
.

Inductive lc_sse : ss_entry → Prop :=
| lc_sse_ex : forall e, lc_bexpr e → lc_sse (sse_ex e)
| lc_sse_kv : forall k, lc_sse (sse_kv k)
.

Definition fv_sse (e : ss_entry) : atoms :=
  match e with
  | sse_ex e => fv_bexpr e
  | sse_kv k => {}
  end
.

Definition subst_sse (v : bexpr) (x : var) (sse : ss_entry) :=
  match sse with
  | sse_ex e => sse_ex ([v /' x] e)
  | sse_kv k => sse_kv k
  end
.

Hint Constructors lc_sse : core.

Definition subst_set := list (var * ss_entry).

(*
Notation ": A !" :=
  (sse_v A) (at level 52, A at level 50, no associativity).
*)

Notation " ≔ e" :=
  (sse_ex e) (at level 52, no associativity).
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

Definition subst_ss (v : bexpr) (x : var) : subst_set → subst_set :=
  map (subst_sse v x).

Fixpoint fv_ss (s : subst_set) : atoms :=
  match s with
  | nil => {}
  | pair x e :: s' => fv_sse e `union` fv_ss s'
  end
.

(*
Fixpoint ss_to_ctx (s : subst_set) : bcontext :=
  match s with
  | nil => bctx_nil
  | s' ; x : A ! => ss_to_ctx s' ,' x : A
  | s' ; x : A ≔ e => ss_to_ctx s'
  | s' ; x ≔ ⧼k⧽ => ss_to_ctx s'
  end
.
*)

(* syntactic well-formedness of substitution set *)
Inductive wf_ss : subst_set → Prop :=
| wf_ss_nil : wf_ss nil
| wf_ss_kv : forall x k Θ
  , wf_ss Θ → x `notin` dom Θ
  → wf_ss (Θ; x ≔ ⧼k⧽)
| wf_ss_ex : forall x e Θ
  , wf_ss Θ → x `notin` dom Θ
  → mono_btype e
  → wf_ss (Θ; x ≔ e)
.

#[export]
Hint Constructors wf_ss : core.

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
| inste_ex  : forall Θ x e, wf_ss Θ → x ≔ e ∈ Θ → inst_expr Θ  `^x  e
| inste_k   : forall Θ x k,   wf_ss Θ → x ≔ ⧼k⧽ ∈ Θ → inst_expr Θ ⧼`^x⧽ ⧼k⧽'
| inste_star: forall Θ, wf_ss Θ → inst_expr Θ ⋆′ ⋆'
| inste_box : forall Θ, wf_ss Θ → inst_expr Θ ◻′ ◻'
| inste_num : forall Θ n,     wf_ss Θ → inst_expr Θ (ae_num n) (be_num n)
| inste_int : forall Θ, wf_ss Θ → inst_expr Θ ae_int be_int
| inste_bot : forall Θ A' A
  , inst_expr Θ A' A
  → inst_expr Θ (ae_bot A') (be_bot A)
| inste_app : forall Θ f' f a' a
  , inst_expr Θ f' f → inst_expr Θ a' a
  → inst_expr Θ (ae_app f' a') (be_app f a)
| inste_castup : forall Θ e' e A' A
  , inst_expr Θ e' e → inst_expr Θ A' A
  → inst_expr Θ (ae_castup A' e') (be_castup A e)
| inste_castdn : forall Θ e' e,
    inst_expr Θ e' e → inst_expr Θ (ae_castdn e') (be_castdn e)
| inste_abs : forall L Θ e' e b' b
  , (forall x, x `notin` L → inst_expr Θ (e' ^`′ x) (e ^`' x))
  → (forall x, x `notin` L → inst_body Θ
      (open_abody_wrt_aexpr b' `′x) (open_bbody_wrt_bexpr b `' x))
  → inst_expr Θ (ae_abs e' b') (be_abs e b)
| inste_bind : forall L Θ e' e b' b
  , (forall x, x `notin` L → inst_expr Θ (e' ^`′ x) (e ^`' x))
  → (forall x, x `notin` L → inst_body Θ
      (open_abody_wrt_aexpr b' `′x) (open_bbody_wrt_bexpr b `' x))
  → inst_expr Θ (ae_bind e' b') (be_bind e b)
| inste_pi : forall L Θ A' A B' B
  , inst_expr Θ A' A
  → (forall x, x `notin` L → inst_expr Θ (B' ^`′ x) (B ^`' x))
  → inst_expr Θ (ae_pi A' B') (be_pi A B)
| inste_all : forall L Θ A' A B' B
  , inst_expr Θ A' A
  → (forall x, x `notin` L → inst_expr Θ (B' ^`′ x) (B ^`' x))
  → inst_expr Θ (ae_all A' B') (be_all A B)
| inste_anno : forall Θ e' e A' A
  , inst_expr Θ e' e → inst_expr Θ A' A
    → inst_expr Θ (e' ::′ A') (e ::' A)
with inst_body : subst_set → abody → bbody → Prop :=
| instb_anno : forall Θ e' e A' A
  , inst_expr Θ e' e → inst_expr Θ A' A
  → inst_body Θ (ab_anno e' A') (bb_anno e A)
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
    try solve [auto | pick fresh x; eauto 6 with lc].
  (* body cases *)
Admitted.


Lemma inst_e_lc : forall Θ e' e,
    Θ ⊩ e' ⇝ e → lc_bexpr e.
Proof.
  induction 1; try solve [auto | pick fresh x; eauto 6 with lc].
  - apply wf_lc_sse in H0.
    + now inversion H0.
    + assumption.
  - admit.
  - admit.
  (* body cases *)
Admitted.

#[export]
Hint Resolve inst_ae_lc inst_e_lc : core.

Reserved Notation "T ⊩ ob ⇝? dob" (at level 65, ob at level 58, no associativity).
Inductive inst_obind : subst_set → obind → obindd → Prop :=
| instob_none : forall Θ, inst_obind Θ ob_none dob_none
| instob_bind : forall Θ x A' A,
    inst_expr Θ A' A → inst_obind Θ (x :?′ A') (x :? A)
where "T ⊩ ob ⇝? dob" := (inst_obind T ob dob) : type_scope
.

Reserved Notation "T ⊩ c1 ⟿′ c2 " (at level 65, c1 at level 58).
Inductive inst_cont : subst_set → cont → dcont → Prop :=
| instc_done : forall Θ, wf_ss Θ → Θ ⊩ c_done ⟿′ dc_done
| instc_app : forall Θ e1 e2 e1' e2' c c'
  , Θ ⊩ e1' ⇝ e1
  → Θ ⊩ e2' ⇝ e2
  → Θ ⊩ c' ⟿′ c
  → Θ ⊩ c_app e1' e2' c' ⟿′ dc_app e1 e2 c
| instc_reduce : forall Θ c' c
  , Θ ⊩ c' ⟿′ c
  → Θ ⊩ c_reduce c' ⟿′ dc_reduce c
| instc_check : forall Θ A A'
  , Θ ⊩ A' ⇝ A
  → Θ ⊩ c_check A' ⟿′ dc_check A
| instc_inst : forall Θ A A' c c'
  , Θ ⊩ A' ⇝ A
  → Θ ⊩ c' ⟿′ c
  → Θ ⊩ c_inst A' c' ⟿′ dc_inst A c
where "T ⊩ c1 ⟿′ c2" := (inst_cont T c1 c2) : type_scope
.

Reserved Notation "T1 ⊩ w1 ⇝′ w2" (at level 65, w1 at level 58).
Inductive inst_work : subst_set → work → dwork → Prop :=
| instw_check : forall Θ ob ob' e1 e1' e2 e2' A A'
  , inst_obind Θ ob' ob → inst_expr Θ A' A
  → inst_expr Θ e1' e1 → inst_expr Θ e2' e2
  → inst_work Θ (ob' ⊢? e1' <: e2' ⇐′ A') (ob ⊢? e1 <: e2 ⇐ A)
| instw_cpct  : forall Θ A A' B B'
  , inst_expr Θ A' A → inst_expr Θ B' B
  → inst_work Θ (A' ≲′ B') (A ≲ B)
| instw_infer : forall Θ e1 e1' e2 e2' c c'
  , Θ ⊩ e1' ⇝ e1 → Θ ⊩ e2' ⇝ e2
  → inst_cont Θ c' c
  → inst_work Θ (e1' <: e2' ⇒′ c') (e1 <: e2 ⇒ c)
| instw_iapp : forall Θ A A' e1 e2 e1' e2' c c'
  , Θ ⊩ A' ⇝ A
  → Θ ⊩ e1' ⇝ e1
  → Θ ⊩ e2' ⇝ e2
  → inst_cont Θ c' c
  → Θ ⊩ A' ⋅ e1' & e2' ⇒′ c' ⇝′ A ⋅ e1 & e2 ⇒ c
| instw_red : forall Θ A A' c c'
  , inst_expr Θ A' A
  → inst_cont Θ c' c
  → inst_work Θ (A' ⟼′ c') (A ⟼ c)
| instw_appc : forall Θ e e' c c'
  , inst_expr Θ e' e → inst_cont Θ c' c
  → inst_work Θ (c' $′ e') (c $ e)
where "T1 ⊩ w1 ⇝′ w2" := (inst_work T1 w1 w2) : type_scope.

Reserved Notation "T1 ⊩ G1 ⟿ G2 ⫣ T2" (at level 65, G1 at level 58, G2 at level 58).
Inductive inst_wl  : subst_set → worklist → dworklist → subst_set → Prop :=
| instwl_nil  : forall Θ, wf_ss Θ → inst_wl Θ wl_nil dwl_nil Θ
| instwl_cons : forall Θ Θ' Γ Γ' w w'
  , inst_wl Θ Γ' Γ Θ' → inst_work Θ' w' w
  → inst_wl Θ (Γ' ⊨′ w') (Γ ⊨ w) Θ'
| instwl_var  : forall Θ Θ' Γ Γ' x A A'
  , inst_wl Θ Γ' Γ Θ' → x `notin` dom Θ' → inst_expr Θ' A' A
  → inst_wl Θ (Γ' ,′ x :′ A') (Γ ,′' x : A) Θ'
| instwl_kv : forall Θ Θ' Γ Γ' x k
  , inst_wl Θ Γ' Γ Θ' → x `notin` dom Θ'
  → inst_wl Θ (Γ' ,′ ⧼^x⧽) Γ (Θ'; x ≔ ⧼k⧽)
| instwl_ex : forall Θ Θ' Γ Γ' x A' A e
  , mono_btype e
  → inst_wl Θ Γ' Γ Θ' → x `notin` dom Θ' → inst_expr Θ' A' A
  → inst_wl Θ (Γ' ,′ ^x :′ A') Γ (Θ'; x ≔ e)
where "T1 ⊩ G1 ⟿ G2 ⫣ T2" := (inst_wl T1 G1 G2 T2) : type_scope
.

#[export]
Hint Constructors inst_expr inst_obind inst_work inst_wl : core.


Definition transfer' (Γ' : worklist) (Γ : dworklist) : Prop :=
  exists Θ, inst_wl nil Γ' Γ Θ.

Lemma inst_wl_ss_wf_l : forall Θ1 Θ2 Γ' Γ,
    Θ1 ⊩ Γ' ⟿ Γ ⫣ Θ2 → wf_ss Θ1.
Proof.
  induction 1; auto.
Qed.

Lemma inst_w_ss_wf_l : forall Θ1 w' w,
    Θ1 ⊩ w' ⇝′ w → wf_ss Θ1.
Proof.
  induction 1; eauto.
Qed.

Lemma inst_wl_ss_wf_r : forall Θ1 Γ' Γ Θ2,
    Θ1 ⊩ Γ' ⟿ Γ ⫣ Θ2 → wf_ss Θ2.
Proof.
  induction 1; eauto 3.
Qed.

#[export]
Hint Resolve inst_wl_ss_wf_l inst_w_ss_wf_l inst_wl_ss_wf_r : core.
