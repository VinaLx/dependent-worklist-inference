Require Export alg.notations.

Reserved Notation "G1 ⫢′ G2" (at level 58, left associativity).
Fixpoint wl_app (G1 G2 : worklist) :=
  match G2 with
  | wl_nil => G1
  | G2' ,′ b => G1 ⫢′ G2' ,′ b
  | G2' ⊨′ b => G1 ⫢′ G2' ⊨′ b
  | G2' ,′ ◁ => G1 ⫢′ G2' ,′ ◁
  end
where "G1 ⫢′ G2" := (wl_app G1 G2) : worklist_scope
.

Reserved Notation "Γ1 ,,′ Γ2" (at level 58, left associativity).
Fixpoint actx_app (Γ1 Γ2 : acontext) :=
  match Γ2 with
  | actx_nil => Γ1
  | Γ2' ,′′ x : A => Γ1 ,,′ Γ2' ,′′ x : A
  end
where "Γ1 ,,′ Γ2" := (actx_app Γ1 Γ2) : acontext_scope.

Reserved Notation "⌈ Γ ⌉′"
  (at level 0, Γ at level 58, no associativity).
Fixpoint to_wl (Γ : acontext) : worklist :=
  match Γ with
  | actx_nil => wl_nil
  | Γ' ,′′ x : A => ⌈ Γ' ⌉′ ,′ x :′ A
  end
where "⌈ Γ ⌉′" := (to_wl Γ) : worklist_scope.

Definition binding_var (b : binding) : var :=
  match b with
  | x :′ A => x
  | ^x :′ k => x
  | ⧼^k⧽ => k
  end.

Fixpoint wl_dom (Γ : worklist) : atoms :=
  match Γ with
  | wl_nil => empty
  | Γ' ⊨′ w => wl_dom Γ'
  | Γ' ,′ b => add (binding_var b) (wl_dom Γ')
  | Γ' ,′ ◁ => wl_dom Γ'
  end
.

Reserved Notation "⟦ e /′ ^ x ⟧ G"
  (at level 56, e at level 50, x at level 0, right associativity).
Fixpoint subst_ex (e : aexpr) (x : var) (Γ : worklist) : worklist :=
  match Γ with
  | wl_nil => wl_nil
  | Γ' ⊨′ w => ⟦ e /′ ^x ⟧ Γ' ⊨′ ex_subst_work e x w
  | Γ' ,′ ◁ => ⟦ e /′ ^x ⟧ Γ' ,′ ◁
  | Γ' ,′ y :′ A => ⟦ e /′ ^x ⟧ Γ' ,′ y :′ [e /^ x] A
  | Γ' ,′ ⧼^k⧽ => ⟦ e /′ ^x ⟧ Γ' ,′ ⧼^k⧽
  | Γ' ,′ ^y :′ k =>
    if eqb x y then Γ'
      else ⟦ e /′ ^x ⟧ Γ' ,′ ^y :′ k
  end
where "⟦ e /′ ^ x ⟧ G" := (subst_ex e x G) : worklist_scope
.

Reserved Notation "⟦ k /′ ⧼ x ⧽ ⟧ G"
  (at level 56, k at level 50, x at level 0, right associativity).
Fixpoint subst_k (k : akind) (x : var) (Γ : worklist) : worklist :=
  match Γ with
  | wl_nil => wl_nil
  | Γ' ⊨′ w => ⟦ k /′ ⧼ x ⧽ ⟧ Γ' ⊨′ k_subst_work k x w
  | Γ' ,′ ◁ => ⟦ k /′ ⧼ x ⧽ ⟧ Γ' ,′ ◁
  | Γ' ,′  y :′ A => ⟦ k /′ ⧼ x ⧽ ⟧ Γ' ,′  y :′ [k /⧼ x ⧽] A
  | Γ' ,′ ^y :′ k' => ⟦ k /′ ⧼ x ⧽ ⟧ Γ' ,′ ^y :′ k_subst_akind k x k'
  | Γ' ,′ ⧼^y⧽ =>
    if eqb x y then Γ' else ⟦ k /′ ⧼x⧽ ⟧ Γ' ,′ ⧼^y⧽
  end
where "⟦ k /′ ⧼ x ⧽ ⟧ G" := (subst_k k x G) : worklist_scope
.

Inductive apply_cont : cont → aexpr → worklist → Prop :=
| apc_app : forall c F e1 e2,
    apply_cont (c_app e1 e2 c) F
      (wl_nil ⊨′ F ⋅ e1 & e2 ⇒′ c)
| apc_done : forall e,
  apply_cont c_done e wl_nil
| apc_check : forall A B,
    apply_cont (c_check B) A
      (wl_nil ⊨′ A ⧼~~⧽′ B)
.

(* expression tranform with variables *)
Definition ev_trans := aexpr → var * aexpr → aexpr → Prop.

Inductive reorder :
  aexpr → ev_trans → atoms → worklist → worklist → aexpr → worklist → Prop :=
| r_nil : forall e F s, reorder e F s wl_nil wl_nil e wl_nil
| r_cons : forall e F s Γ ψ e' Γ' w
  , reorder e F s Γ ψ e' Γ'
  → reorder e F s (Γ ⊨′ w) ψ e' (Γ' ⊨′ w)
| r_var : forall e (F : ev_trans) e' s Γ ψ e'' Γ' x A
  , F e (pair x A) e'
  → reorder e' F s Γ ψ e'' Γ'
  → reorder e' F s (Γ,′ x :′ A) ψ e'' (Γ',′ x :′ A)
| r_tag : forall e F s Γ ψ e' Γ'
  , reorder e F s Γ ψ e' Γ'
  → reorder e F s (Γ ,′ ◁) ψ e' (Γ ,′ ◁)
| r_ex_move : forall e F s Γ ψ e' Γ' x k
  , x `in` fex_aexpr e
  → reorder e F s Γ ψ e' Γ'
  → reorder e F (s `union` fkv_akind k) (Γ,′ ^x :′ k) (ψ,′ ^x :′ k) e' Γ'
| r_ex_stay : forall e F s Γ ψ e' Γ' x k
  , x `notin` fex_aexpr e
  → reorder e F s Γ ψ e' Γ'
  → reorder e F s (Γ,′ ^x :′ k) ψ e' (Γ',′ ^x :′ k)
| r_k_move : forall e F s Γ ψ e' Γ' k
  , k `in` fkv_aexpr e `union` s
  → reorder e F s Γ ψ e' Γ'
  → reorder e F s (Γ,′ ⧼^k⧽) (ψ ,′ ⧼^k⧽) e' Γ'
| r_k_stay : forall e F s Γ ψ e' Γ' k
  , k `notin` fkv_aexpr e `union` s
  → reorder e F s Γ ψ e' Γ'
  → reorder e F s (Γ,′ ⧼^k⧽) ψ e' (Γ',′ ⧼^k⧽)
.

Inductive wrap_var : ev_trans :=
| mk_wrap_var : forall e x A,
    wrap_var e (pair x A) (ae_pi A (close_aexpr_wrt_aexpr x e)).

Inductive scope_trap : ev_trans :=
| mk_scope_trap : forall e x A
  , x `notin` fv_aexpr e
  → scope_trap e (pair x A) e
.

Definition cont_apply_reorder
  (e : aexpr) (Γ ψ : worklist) (e' : aexpr) (Γ' : worklist) :=
  reorder e wrap_var empty Γ ψ e' Γ'.

Definition ex_inst_reorder
  (e : aexpr) (Γ ψ Γ' : worklist) :=
  reorder e scope_trap empty Γ ψ e Γ'.

Hint Unfold cont_apply_reorder ex_inst_reorder : core.

Inductive notags : worklist → Prop :=
| nt_nil : notags wl_nil
| nt_cons : forall w Γ, notags Γ → notags (Γ ⊨′ w)
| nt_bind : forall b Γ, notags Γ → notags (Γ,′ b)
.

Reserved Notation "⪧′ wl" (at level 65, no associativity).
Inductive wl_step : worklist -> Prop :=
| st_nil : ⪧′ wl_nil
(* decl-like inference *)
| st_var : forall Γ Γ1 Γ2 x A c
  , Γ = Γ1 ,′ x :′ A ⫢′ Γ2
  → ⪧′ Γ ⊨′ c $′ A
  → ⪧′ Γ ⊨′ `′ x ⇒′ c
| st_num : forall Γ n c
  , ⪧′ Γ ⊨′ c $′ ae_int
  → ⪧′ Γ ⊨′ ae_num n ⇒′ c
| st_int : forall Γ c
  , ⪧′ Γ ⊨′ c $′ ⋆′
  → ⪧′ Γ ⊨′ ae_int ⇒′ c
| st_star_inf : forall Γ c
  , ⪧′ Γ ⊨′ c $′ ◻′
  → ⪧′ Γ ⊨′ ⋆′ ⇒′ c
| st_app : forall Γ f1 f2 a1 a2 c
  , ⪧′ Γ ,′ ◁ ⊨′ f1 ~~ f2 ⇒′ c_app a1 a2 c
  -> ⪧′ Γ ⊨′ ae_app f1 a1 ~~ ae_app f2 a2 ⇒′ c
| st_pi : forall L Γ A1 A2 B1 B2 c
  , (forall x, x `notin` L → forall k1, k1 `notin` add x L
    → forall k2, k2 `notin` add k1 (add x L)
    → ⪧′ Γ ,′ ⧼^k2⧽
      ⊨′ (actx_nil ,′′ x : A1) ⊢′ B1 ^`′ x ~~ B2 ^`′ x ⇐′ ⧼`^k2⧽
      ,′ ⧼^k1⧽ ⊨′ A1 ~~ A2 ⇐′ ⧼`^k1⧽
      ⊨′ c $′ ⧼`^k2⧽)
  → ⪧′ Γ ⊨′ ae_pi A1 B1 ~~ ae_pi A2 B2 ⇒′ c
| st_abs : forall L Γ e1 e2 c
  , (forall x, x `notin` L → forall k, k `notin` add x L
    → forall A, A `notin` add k (add x L)
      → ⪧′ Γ ,′ ⧼^k⧽ ,′ ^A :′ ak_ex k ,′ x :′ `^A
          ⊨′ e1 ^`′ x ~~ e2 ^`′ x ⇒′ c)
  → ⪧′ Γ ⊨′ ae_abs e1 ~~ ae_abs e2 ⇒′ c
| st_iapp_pi : forall L Γ A B e1 e2 c
  , (forall x, x `notin` L → forall k, k `notin` add x L
    → ⪧′ Γ ⊨′ c $′ B ^^′ e1 ⊨′ e1 ~~ e2 ⇐′ A)
  → ⪧′ Γ ⊨′ ae_pi A B ⋅ e1 & e2 ⇒′ c

| st_iapp_ex : forall L Γ x k c Γ1 Γ2 e1 e2
  , Γ = Γ1 ,′ ^x :′ k ⫢′ Γ2
  → (forall A, A `notin` L → forall B, B `notin` add A L
    → forall k', k' `notin` add A (add B L)
      → forall F, F = ae_pi `^A `^B
        → ⪧′ Γ1 ,′ ⧼^k'⧽ ,′ ^A :′ ak_ex k' ,′ ^B :′ k
          ⫢′ ex_subst_worklist F x (Γ2 ⊨′ F ⋅ e1 & e2 ⇒′ c))
  → ⪧′ Γ ⊨′ `^x ⋅ e1 & e2 ⇒′ c

(* ex vars *)
| st_ex_eq : forall Γ Γ1 x k Γ2 c
  , Γ = Γ1 ,′ ^x :′ k ⫢′ Γ2
  → ⪧′ Γ ⊨′ c $′ ae_kind k
  → ⪧′ Γ ⊨′ `^x ~~ `^x ⇒′ c
| st_ex_l : forall Γ Γ1 x k Γ2 ψ Γ2' e c
  , e <> `^ x
  → Γ = Γ1,′ ^x :′ k ⫢′ Γ2
  → ex_inst_reorder e Γ2 ψ Γ2'
  → ⪧′ Γ1 ⫢′ ψ ⊨′ e ⇐′ ⧼ k ⧽′
      ⫢′ ex_subst_worklist e x (Γ2' ⊨′ c $′ ⧼k⧽′)
  → ⪧′ Γ ⊨′ `^x ~~ e ⇒′ c
| st_ex_r : forall Γ Γ1 x k Γ2 ψ Γ2' e c
  , e <> `^ x
  → Γ = Γ1,′ ^x :′ k ⫢′ Γ2
  → ex_inst_reorder e Γ2 ψ Γ2'
  → ⪧′ Γ1 ⫢′ ψ ⊨′ e ⇐′ ⧼ k ⧽′
      ⫢′ ex_subst_worklist e x (Γ2' ⊨′ c $′ ⧼k⧽′)
  → ⪧′ Γ ⊨′ e ~~ `^x ⇒′ c

(* kind ex infer *)
| st_kv_eq : forall Γ x c
  , ⪧′ ⟦ak_star /′ ⧼x⧽⟧ (Γ ⊨′ c $′ ◻′)
  → ⪧′ Γ ⊨′ ⧼`^x⧽ ~~ ⧼`^x⧽ ⇒′ c
| st_kv_lr : forall Γ x y c
  , x <> y
  → ⪧′ ⟦ak_star /′ ⧼y⧽⟧ ⟦ak_star /′ ⧼x⧽⟧ (Γ ⊨′ c $′ ◻′)
  → ⪧′ Γ ⊨′ ⧼`^x⧽ ~~ ⧼`^y⧽ ⇒′ c
| st_kv_l : forall Γ x c
  , ⪧′ ⟦ak_star /′ ⧼x⧽⟧ (Γ ⊨′ c $′ ◻′)
  → ⪧′ Γ ⊨′ ⧼`^x⧽ ~~ ⋆′ ⇒′ c
| st_kv_r : forall Γ x c
  , ⪧′ ⟦ak_star /′ ⧼x⧽⟧ (Γ ⊨′ c $′ ◻′)
  → ⪧′ Γ ⊨′ ⋆′ ~~ ⧼`^x⧽ ⇒′ c

(* check *)
| st_check : forall Γ Γ' e1 e2 A
  , ⪧′ Γ ⫢′ ⌈ Γ' ⌉′,′ ◁ ⊨′ e1 ~~ e2 ⇒′ c_check A
  → ⪧′ Γ ⊨′ Γ' ⊢′ e1 ~~ e2 ⇐′ A

| st_comp_box_l : forall Γ1 Γ2 k
  , ⪧′ Γ1 ⫢′ k_subst_worklist ak_box k Γ2
  → ⪧′ Γ1 ,′ ⧼^k⧽ ⫢′ Γ2 ⊨′ ◻′ ⧼~~⧽′ ⧼`^k⧽
| st_comp_box_r : forall Γ1 Γ2 k
  , ⪧′ Γ1 ⫢′ k_subst_worklist ak_box k Γ2
  → k `notin` wl_dom Γ1 `union` wl_dom Γ2
  → ⪧′ Γ1 ,′ ⧼^k⧽ ⫢′ Γ2 ⊨′ ⧼`^k⧽ ⧼~~⧽′ ◻′
| st_comp_kv_eq : forall Γ Γ1 Γ2 k
  , Γ = Γ1 ,′ ⧼^k⧽ ⫢′ Γ2
  → ⪧′ Γ
  → ⪧′ Γ ⊨′ ⧼`^k⧽ ⧼~~⧽′ ⧼`^k⧽
| st_comp_kv : forall Γ1 Γ2 Γ3 x y
  , y `notin` add x (wl_dom Γ1 `union` wl_dom Γ2 `union` wl_dom Γ3)
  → ⪧′ Γ1,′ ⧼^x⧽ ⫢′ Γ2 ⫢′ k_subst_worklist (ak_ex x) y Γ3
  → ⪧′ Γ1 ,′ ⧼^x⧽ ⫢′ Γ2 ,′ ⧼^y⧽ ⫢′ Γ3 ⊨′ ⧼`^x⧽ ⧼~~⧽′ ⧼`^y⧽
| st_comp_sub : forall L Γ A B
  , (forall k, A <> ⧼k⧽′)
  → (forall k, B <> ⧼k⧽′)
  → (forall k, k `notin` L → ⪧′ Γ,′ ⧼^k⧽ ⊨′ A ~~ B ⇐′ ⧼`^k⧽)
  → ⪧′ Γ ⊨′ A ⧼~~⧽′ B

| st_app_cont : forall Γ1 Γ2 ψ Γ2' c e e' Γ'
  , apply_cont c e' Γ'
  → notags Γ2
  → cont_apply_reorder e Γ2 ψ e' Γ2'
  → ⪧′ Γ1 ⫢′ ψ ⫢′ Γ' ⫢′ Γ2'
  → ⪧′ Γ1 ,′ ◁ ⫢′ Γ2 ⊨′ c $′ e

(* elim bindings *)
| st_bind_var : forall L Γ x A
  , x `notin` wl_dom Γ
  → (forall k, k `notin` L → ⪧′ Γ ,′ ⧼^k⧽ ⊨′ A ⇐′ ⧼`^k⧽)
  → ⪧′ Γ ,′ x :′ A
| st_bind_ex : forall Γ x k
  , x `notin` wl_dom Γ
  → ⪧′ Γ
  → ⪧′ Γ ,′ ^x :′ k
| st_bind_k : forall Γ k
  , k `notin` wl_dom Γ
  → ⪧′ Γ
  → ⪧′ Γ ,′ ⧼^k⧽

where "⪧′ wl" := (wl_step wl) : type_scope
.


#[export]
Hint Constructors wl_step : core.
