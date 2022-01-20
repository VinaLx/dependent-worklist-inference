Require Export decl.ln_inf.
Require Export Coq.Unicode.Utf8.

(* sometimes '_' are used to avoid conflicts *)

Notation "G ⊢ e1 <: e2 : A" :=
  (usub G e1 e2 A)
    (at level 65, e1 at level 50, e2 at level 50, no associativity) : type_scope.

Notation "G ⊢ e : A" :=
  (usub G e e A)
    (at level 65, e at level 50, no associativity) : type_scope.

Notation "⊢ G" :=
  (wf_context G)
    (at level 65, no associativity) : type_scope.

Notation "A ⟶ B" := (reduce A B)
  (at level 65, no associativity) : type_scope.

Notation "x :_ A ∈ G" := (in_ctx x A G)
  (at level 65, no associativity) : type_scope.

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

Notation "'λ_' A , e : B" :=
  (e_abs A (b_anno e B))
    (at level 50, A at level 50, e at level 50, no associativity) : expr_scope.

Notation "'Λ' A , e : B" :=
  (e_bind A (b_anno e B))
    (at level 50, A at level 50, e at level 50, no associativity) : expr_scope.

Open Scope context_scope.
Open Scope expr_scope.
