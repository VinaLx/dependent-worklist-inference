Require Export bidir.ln_inf.
Require Export Coq.Unicode.Utf8.

Declare Scope bexpr_scope.
Delimit Scope bexpr_scope with bexpr.
Bind Scope bexpr_scope with bexpr.

Notation "`' x" := (be_var_f x)
  (at level 0, x at level 0, no associativity) : bexpr_scope.
Notation "↑' x" := (be_var_b x)
  (at level 0, x at level 0, no associativity) : bexpr_scope.

Notation "[ v /' x ] e" :=
  (subst_bexpr v x e)
    ( at level 49, v at level 50, x at level 0
    , right associativity) : bexpr_scope.

Notation "e ^`' x" := (open_bexpr_wrt_bexpr e (be_var_f x))
  (at level 48, left associativity) : bexpr_scope.

Notation "e1 ^^' e2" := (open_bexpr_wrt_bexpr e1 e2)
  (at level 48, left associativity) : bexpr_scope.

Notation "e \`' x " := (close_bexpr_wrt_bexpr x e)
  (at level 48, left associativity) : bexpr_scope.

Notation "⋆'" := (be_kind bk_star)
  (at level 0, no associativity) : bexpr_scope.

Notation "◻'" := (be_kind bk_box) (at level 0, no associativity) : bexpr_scope.

Notation "⧼ k ⧽'" := (be_kind k)
  (at level 0, no associativity) : bexpr_scope.

Notation "e ::' A" := (be_anno e A)
  (at level 50, no associativity) : bexpr_scope.

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

Declare Scope bcontext_scope.
Delimit Scope bcontext_scope with bctx.
Bind Scope bcontext_scope with bcontext.

(* 'varVdash' *)
Notation "⫦ G" := (bwf_context G)
    (at level 65, no associativity) : type_scope.

Notation "G ,' x : A" :=
  (bctx_cons G x A)
    (at level 58, x at level 0, left associativity) : bcontext_scope.

Reserved Notation "G1 ,,' G2"
  (at level 58, left associativity).

Fixpoint bctx_app (Γ1 Γ2 : bcontext) : bcontext :=
  match Γ2 with
  | bctx_nil => Γ1
  | Γ2',' x : A => Γ1 ,,' Γ2' ,' x : A
  end%bctx
where "G1 ,,' G2" := (bctx_app G1 G2) : bcontext_scope.


Open Scope bcontext_scope.
Open Scope bexpr_scope.

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

Notation "G ,′' x : A" :=
  (dwl_bind G x A) (at level 58, x at level 0, left associativity) : dworklist_scope.

Open Scope dworklist_scope.
Open Scope dwork_scope.
Open Scope obindd_scope.
