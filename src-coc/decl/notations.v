Require Export Unicode.Utf8.

Require Export decl.ln_inf.

Notation "G ⊢ e : A" :=
  (tp G e A)
    (at level 60, e at next level, no associativity) : type_scope.

Notation "⊢ G" :=
  (wf_context G)
    (at level 60, no associativity) : type_scope.

Notation "⊢₂ G" :=
  (wf_context2 G)
    (at level 60, no associativity) : type_scope.

Notation "G ⊢ e ⇐ A" :=
  (tp2 G e d_check A)
    (at level 60, e at next level, no associativity) : type_scope.

Notation "G ⊢ e ⇒ A" :=
  (tp2 G e d_check A)
    (at level 60, e at next level, no associativity) : type_scope.

Notation "G ⊢ e ⇔ d A" :=
  (tp2 G e d A)
    (at level 60, e at next level, d at level 0, no associativity) : type_scope.

Notation "A ⟶ B" := (reduce A B)
  (at level 60, no associativity) : type_scope.

Declare Scope context_scope.
Delimit Scope context_scope with ctx.
Bind Scope context_scope with context.

Notation "G , x : A" :=
  (ctx_cons G x A)
    (at level 58, x at level 0, left associativity) : context_scope.

Reserved Notation "G1 ,, G2"
  (at level 58, left associativity).

Fixpoint ctx_app (Γ1 Γ2 : context) : context :=
  match Γ2 with
  | ctx_nil => Γ1
  | Γ2', x : A => Γ1 ,, Γ2' , x : A
  end%ctx

where "G1 ,, G2" := (ctx_app G1 G2) : context_scope.

Notation "⟦ v /_ x ⟧ G" :=
  (subst_context v x G)
    ( at level 56, v at level 50, x at level 0
    , right associativity) : context_scope.

Declare Scope expr_scope.
Delimit Scope expr_scope with expr.
Bind Scope expr_scope with expr.

Notation "` x" := (e_var_f x)
  (at level 0, x at level 0, no associativity) : expr_scope.
Notation "↑ x" := (e_var_b x)
  (at level 0, x at level 0, no associativity) : expr_scope.

Notation "[ v /_ x ] e" :=
  (subst_expr v x e)
    ( at level 49, v at level 50, x at level 0
    , right associativity) : expr_scope.

Notation "e ^` x" := (open_expr_wrt_expr e (e_var_f x))
  (at level 48, left associativity) : expr_scope.

Notation "e1 ^^ e2" := (open_expr_wrt_expr e1 e2)
  (at level 48, left associativity) : expr_scope.

Notation "⋆" := (e_kind k_star)
  (at level 0, no associativity) : expr_scope.

Notation "◻" := (e_kind k_box) (at level 0, no associativity) : expr_scope.

Notation "⧼ k ⧽" := (e_kind k)
  (at level 0, no associativity) : expr_scope.

Notation "[ v / x ] e" :=
  (subst_expr v x e)
    ( at level 49, v at level 50, x at level 0
    , right associativity) : expr_scope.

Open Scope context_scope.
Open Scope expr_scope.

Declare Scope dwork_scope.
Delimit Scope dwork_scope with dwork.
Bind Scope dwork_scope with dwork.

Notation "G ⊢' e ⇐ A" :=
  (dw_check G e A)
    (at level 55, e at level 50, no associativity) : dwork_scope.

Notation "e ⇐' A" :=
  (dw_check ctx_nil e A)
    (at level 55, no associativity) : dwork_scope.

Notation "e ⇒' c" :=
  (dw_infer e c)
    (at level 55, no associativity) : dwork_scope.

Notation "A -- s e ⇒ c" :=
  (dw_infer_app A s e c)
    ( at level 55, s at level 0, e at level 50, no associativity) : dwork_scope.

Notation "A ∘ e ⇒ c" :=
  (dw_infer_app A ds_nd e c)
    ( at level 55, e at level 50, no associativity) : dwork_scope.

Notation "A ⋅ e ⇒ c" :=
  (dw_infer_app A ds_d e c)
    ( at level 55, e at level 50, no associativity) : dwork_scope.

Notation "c $ e" :=
  (dw_apply c e)
    (at level 55, no associativity) : dwork_scope.

Notation "A ⧼~~⧽ B" :=
  (dw_compact A B)
    (at level 55, no associativity) : dwork_scope.

Declare Scope dworklist_scope.
Delimit Scope dworklist_scope with dwl.
Bind Scope dworklist_scope with dworklist.

Notation "G ⊨ w" :=
  (dwl_cons G w) (at level 58, left associativity) : dworklist_scope.

Notation "G ,' x : A" :=
  (dwl_bind G x A) (at level 58, x at level 0, left associativity) : dworklist_scope.

Notation "G ,' ◁" :=
  (dwl_tag G) (at level 58, left associativity) : dworklist_scope.

Open Scope dworklist_scope.
Open Scope dwork_scope.

Declare Scope dcont_scope.
Delimit Scope dcont_scope with dcont.
Bind Scope dwork_scope with dcont.

Notation "'__' ⋅ e ⇒ c" :=
  (dc_app e c)
    (at level 53, e at level 50, no associativity) : dcont_scope.

Notation "'__' ⧼~~⧽ A" :=
  (dc_check A)
    (at level 53, no associativity) : dcont_scope.

Open Scope dcont_scope.
