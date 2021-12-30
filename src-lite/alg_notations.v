Require Export alg_inf.
Require Export Coq.Unicode.Utf8.

Notation "e1 ⟶′ e2" := (areduce e1 e2) (at level 65) : type_scope.

Declare Scope obind_scope.
Delimit Scope obind_scope with ob.
Bind Scope obind_scope with obind.

Notation "x :?′ A" :=
  (ob_bind x A) (at level 52, no associativity) : obind_scope.

Declare Scope work_scope.
Delimit Scope work_scope with work.
Bind Scope work_scope with work.

Notation "ob ⊢? e1 <: e2 ⇐′ B" :=
  (w_check ob e1 e2 B)
    ( at level 55, e1 at level 50, e2 at level 50
    , no associativity) : work_scope.

Notation "ob ⊢? e ⇐′ B" :=
  (w_check ob e e B)
    ( at level 55, e at level 50, no associativity) : work_scope.

Notation "e1 <: e2 ⇐′ A" :=
  (w_check ob_none e1 e2 A)
    (at level 55, e2 at level 50, no associativity) : work_scope.

Notation "e ⇐′ A" :=
  (w_check ob_none e e A) (at level 55, no associativity) : work_scope.

Notation "e1 <: e2 ⇒′ wl" :=
  (w_infer e1 e2 wl)
    (at level 55, e2 at level 50, no associativity) : work_scope.

Notation "e ⇒′ wl" :=
  (w_infer e e wl)
    (at level 55, no associativity) : work_scope.

Notation "A ⋅ e1 & e2 ⇒′ wl" :=
  (w_infer_app A e1 e2 wl)
    ( at level 55, e1 at level 50, e2 at level 50
    , no associativity) : work_scope.

Notation "A ⟼′ wl" :=
  (w_reduce A wl)
    (at level 55, no associativity) : work_scope.

Notation "e1 <: e2 ⇐′ A" :=
  (w_check ob_none e1 e2 A)
    (at level 55, e2 at level 50, no associativity) : work_scope.

Notation "A ≲′ B" :=
  (w_compact A B)
    (at level 55, no associativity) : work_scope.

Declare Scope bind_scope.
Delimit Scope bind_scope with bind.
Bind Scope bind_scope with binding.

Notation "x :′ A" :=
  (b_var x A) (at level 52, no associativity) : bind_scope.

Notation "^ x :′ A" :=
  (b_ex x A) (x at level 0, at level 52, no associativity) : bind_scope.

Notation "⧼ ^ k ⧽" :=
  (b_kind k) (k at level 0, at level 0, no associativity) : bind_scope.

(*
Declare Scope obind_scope.
Delimit Scope obind_scope with obind.
Bind Scope obind_scope with obind.

Notation "x :! A" :=
  (ob_bind x A) (at level 52, no associativity) : obind_scope.
*)

Notation "b ∈′ G" :=
  (in_wl b G) (at level 65, no associativity) : type_scope.

Declare Scope worklist_scope.
Delimit Scope worklist_scope with wl.
Bind Scope worklist_scope with worklist.

Notation "G ⊨′ w" :=
  (wl_cons G w) (at level 58, left associativity) : worklist_scope.

Notation "G ,′ b" :=
  (wl_bind G b) (at level 58, b at level 52, left associativity) : worklist_scope.

Notation "⦃ w ⦄" :=
  (wl_cons wl_nil w) (at level 0, no associativity) : worklist_scope.

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

Notation "λ′ e" :=
  (ae_abs e) (at level 50, no associativity) : aexpr_scope.

Notation "Λ′ e" :=
  (ae_bind e) (at level 50, no associativity) : aexpr_scope.

Notation "e ::′ A" :=
  (ae_anno e A) (at level 50, no associativity) : aexpr_scope.

Open Scope work_scope.
Open Scope worklist_scope.
Open Scope bind_scope.
Open Scope aexpr_scope.
