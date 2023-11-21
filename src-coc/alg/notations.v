Require Export alg.ln_inf.
Require Export Coq.Unicode.Utf8.

Notation "e1 ⟶′ e2" := (areduce e1 e2) (at level 65) : type_scope.

Declare Scope acontext_scope.
Delimit Scope acontext_scope with actx.
Bind Scope acontext_scope with acontext.

Notation "G ,′′ x : A" :=
  (actx_cons G x A)
    (at level 58, x at level 0, left associativity) : acontext_scope.

Open Scope acontext_scope.

Declare Scope work_scope.
Delimit Scope work_scope with work.
Bind Scope work_scope with work.

Notation "G ⊢′ e1 ~~ e2 ⇐′ A" :=
  (w_check G e1 e2 A)
    ( at level 55, e1 at level 50, e2 at level 50
    , no associativity) : work_scope.

Notation "G ⊢′ e ⇐′ A" :=
  (w_check G e e A)
    ( at level 55, e at level 50, no associativity) : work_scope.

Notation "e1 ~~ e2 ⇐′ A" :=
  (w_check actx_nil e1 e2 A)
    (at level 55, e2 at level 50, no associativity) : work_scope.

Notation "e ⇐′ A" :=
  (w_check actx_nil e e A)
    (at level 55, no associativity) : work_scope.

Notation "e1 ~~ e2 ⇒′ c" :=
  (w_infer e1 e2 c)
    (at level 55, e2 at level 50, no associativity) : work_scope.

Notation "e ⇒′ c" :=
  (w_infer e e c)
    (at level 55, no associativity) : work_scope.

Notation "A ⋅ e1 & e2 ⇒′ c" :=
  (w_infer_app A e1 e2 c)
    ( at level 55, e1 at level 50
    , e2 at level 50, no associativity) : work_scope.

Notation "A ⧼~~⧽′ B" :=
  (w_compact A B)
    (at level 55, no associativity) : work_scope.

Notation "c $′ e" :=
  (w_apply c e)
    (at level 55, no associativity) : work_scope.

Declare Scope bind_scope.
Delimit Scope bind_scope with bind.
Bind Scope bind_scope with binding.

Notation "x :′ A" :=
  (b_var x A)
    (at level 52, no associativity) : bind_scope.

Notation "^ x :′ k" :=
  (b_ex x k)
    (x at level 0, at level 52, no associativity) : bind_scope.

Notation "⧼ ^ k ⧽" :=
  (b_kind k)
    (k at level 0, at level 0, no associativity) : bind_scope.

Declare Scope worklist_scope.
Delimit Scope worklist_scope with wl.
Bind Scope worklist_scope with worklist.

Notation "G ⊨′ w" :=
  (wl_cons G w) (at level 58, left associativity) : worklist_scope.

Notation "G ,′ b" :=
  (wl_bind G b) (at level 58, b at level 52, left associativity) : worklist_scope.

Notation "G ,′ ◁" :=
  (wl_tag G) (at level 58, left associativity) : worklist_scope.

Declare Scope aexpr_scope.
Delimit Scope aexpr_scope with aexpr.
Bind Scope aexpr_scope with aexpr.

Notation "`′ x" :=
  (ae_var_f x) (at level 0, x at level 0, no associativity) : aexpr_scope.

Notation "↑′ n" :=
  (ae_var_b n) (at level 0, n at level 0) : aexpr_scope.

Notation "e ^`′ x" :=
  (open_aexpr_wrt_aexpr e (ae_var_f x)) (at level 48, left associativity) : aexpr_scope.

Notation "e1 ^^′ e2" :=
  (open_aexpr_wrt_aexpr e1 e2) (at level 48, left associativity) : aexpr_scope.

Notation "[ v /^ x ] e" :=
  (ex_subst_aexpr v x e)
    (at level 49, v at level 50, x at level 0, right associativity) : aexpr_scope.

Notation "[ v /′ x ] e" :=
  (subst_aexpr v x e)
    (at level 49, v at level 50, x at level 0, right associativity) : aexpr_scope.

Notation "[ k /⧼ x ⧽] e" :=
  (k_subst_aexpr k x e)
    (at level 49, k at level 50, x at level 0, right associativity) : aexpr_scope.

Notation "⋆′" :=
  (ae_kind ak_star) (at level 0, no associativity) : aexpr_scope.

Notation "◻′" :=
  (ae_kind ak_box) (at level 0, no associativity) : aexpr_scope.

Notation "⧼ k ⧽′" :=
  (ae_kind k) (at level 0, no associativity) : aexpr_scope.

Notation "⧼ `^ x ⧽" :=
  (ae_kind (ak_ex x)) (at level 0, no associativity) : aexpr_scope.

Notation "`^ x" :=
  (ae_ex x) (at level 0, x at level 0, no associativity) : aexpr_scope.

Open Scope work_scope.
Open Scope worklist_scope.
Open Scope bind_scope.
Open Scope aexpr_scope.

Declare Scope cont_scope.
Delimit Scope cont_scope with cont.
Bind Scope cont_scope with cont.

Notation "'__' ⋅ e1 & e2 ⇒′ c" :=
  (c_app e1 e2 c)
    (at level 53, e1 at level 50, e2 at level 50
      , no associativity) : cont_scope.

Notation "'__' ⧼~~⧽′ A" :=
  (c_check A)
    (at level 53, no associativity) : cont_scope.

Open Scope cont_scope.
