Require Export decl_inf.
Require Export Coq.Unicode.Utf8.

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

Notation "x :' A ∈ G" := (in_ctx x A G)
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

Notation "⟦ v /' x ⟧ G" :=
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

Notation "[ v /' x ] e" :=
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

Notation "G ⊢ e1 <: e2 ⇒ A" := (busub G e1 e2 d_infer A)
    (at level 65, e1 at level 50, e2 at level 50, no associativity) : type_scope.

Notation "G ⊢ e ⇒ A" := (busub G e e d_infer A)
    (at level 65, e at level 50, no associativity) : type_scope.

Notation "G ⊢ e1 <: e2 ⇐ A" := (busub G e1 e2 d_check A)
    (at level 65, e1 at level 50, e2 at level 50, no associativity) : type_scope.

Notation "G ⊢ e ⇐ A" := (busub G e e d_check A)
    (at level 65, e at level 50, no associativity) : type_scope.

Notation "G ⊢ A ⋅ e ⇒ B" :=
  (infer_app G A e B)
    ( at level 65, A at level 50, e at level 50
    , no associativity) : type_scope.

Notation "G ⊢ A ⟼ B" := (greduce G A B)
    (at level 65, A at level 50, no associativity) : type_scope.

(* 'varVdash' *)
Notation "⫦ G" := (bwf_context G)
    (at level 65, no associativity) : type_scope.

Open Scope context_scope.
Open Scope expr_scope.

Declare Scope obindd_scope.
Delimit Scope obindd_scope with dob.
Bind Scope obindd_scope with obindd.

Notation "x :? A" :=
  (dob_bind x A) (at level 52, no associativity) : obindd_scope.

Declare Scope dwork_scope.
Delimit Scope dwork_scope with dwork.
Bind Scope dwork_scope with dwork.

Notation "ob ⊢? e1 <: e2 ⇐ B" :=
  (dw_check ob e1 e2 B)
    ( at level 55, e1 at level 50, e2 at level 50
    , no associativity) : dwork_scope.

Notation "ob ⊢? e ⇐ B" :=
  (dw_check ob e e B)
    ( at level 55, e at level 50, no associativity) : dwork_scope.

Notation "e1 <: e2 ⇐ A" :=
  (dw_check dob_none e1 e2 A)
    (at level 55, e2 at level 50, no associativity) : dwork_scope.

Notation "e ⇐ A" :=
  (dw_check dob_none e e A) (at level 55, no associativity) : dwork_scope.

Notation "e1 <: e2 ⇒ wl" :=
  (dw_infer e1 e2 wl)
    (at level 55, e2 at level 50, no associativity) : dwork_scope.

Notation "e ⇒ wl" :=
  (dw_infer e e wl)
    (at level 55, no associativity) : dwork_scope.

Notation "A ⋅ e ⇒ wl" :=
  (dw_infer_app A e wl)
    ( at level 55, e at level 50
    , no associativity) : dwork_scope.

Notation "A ⟼ wl" :=
  (dw_reduce A wl)
    (at level 55, no associativity) : dwork_scope.

(*
Notation "e1 <: e2 ⇐ A" :=
  (dw_check dob_none e1 e2 A)
    (at level 55, e2 at level 50, no associativity) : dwork_scope.
 *)

Notation "A ≲ B" :=
  (dw_compact A B)
    (at level 55, no associativity) : dwork_scope.

Declare Scope dworklist_scope.
Delimit Scope dworklist_scope with dwl.
Bind Scope dworklist_scope with dworklist.

Notation "G ⊨ w" :=
  (dwl_cons G w) (at level 58, left associativity) : dworklist_scope.

Notation "G ,' x : A" :=
  (dwl_bind G x A) (at level 58, x at level 0, left associativity) : dworklist_scope.

Open Scope dworklist_scope.
Open Scope dwork_scope.
Open Scope obindd_scope.
