Require Export alg_notations.

Notation "k $′ e" :=
  (open_worklist_wrt_aexpr k e)
    (at level 57, left associativity) : worklist_scope.

Reserved Notation "G1 ⫢′ G2" (at level 58, left associativity).
Fixpoint wl_app (G1 G2 : worklist) :=
  match G2 with
  | wl_nil => G1
  | G2' ,′ b => G1 ⫢′ G2' ,′ b
  | G2' ⊨′ b => G1 ⫢′ G2' ⊨′ b
  end
where "G1 ⫢′ G2" := (wl_app G1 G2) : worklist_scope
.

Definition wl_ocons (Γ : worklist) (b : obind) :=
  match b with
  | ob_none => Γ
  | ob_bind x A => Γ,′ x :′ A
  end
.

Notation "Γ ,?′ b" :=
  (wl_ocons Γ b)
    (at level 58, left associativity) : worklist_scope.


Fixpoint to_wl (bs : list binding) : worklist :=
  match bs with
  | nil => wl_nil
  | b :: bs => to_wl bs ,′ b
  end
.

Definition fv_psi_gen (fv : binding → atoms) (ψ : list binding) : atoms :=
  fold_right (fun b acc => acc `union` fv b) {} ψ.

Definition fv_psi := fv_psi_gen fv_binding.
Definition fex_psi := fv_psi_gen fex_binding.
Definition fkv_psi := fv_psi_gen fkv_binding.

Definition binding_var (b : binding) : var :=
  match b with
  |  x :′ _ => x
  | ^x :′ _ => x
  | ⧼^k⧽ => k
  end
.

Definition psi_dom (ψ : list binding) : atoms :=
  fold_right (fun b acc => add (binding_var b) acc) {} ψ.

Reserved Notation "G1 ‖ psi ⊢ ^ x ≔ e ⊣ G2"
  (at level 65, psi at level 60, x at level 0, e at level 50, no associativity).
Inductive reorder : worklist → list binding → var → aexpr → worklist → Prop :=
| re_stop : forall Γ ψ x A e
  , x `notin` fex_aexpr e
  → Γ ,′ ^x :′ A ‖ ψ ⊢ ^x ≔ e ⊣ Γ ⫢′ to_wl ψ ,′ ^x :′ A
| re_skip_work : forall Γ w ψ x e Γ'
  , Γ ‖ ψ ⊢ ^x ≔ e ⊣ Γ'
  → Γ ⊨′ w ‖ ψ ⊢ ^x ≔ e ⊣ Γ ⊨′ w
| re_bind_var : forall Γ x A ψ y e Γ'
  , y `notin` fv_psi ψ `union` fv_aexpr e
  → Γ ‖ ψ ⊢ ^x ≔ e ⊣ Γ'
  → Γ ,′ y :′ A ‖ ψ ⊢ ^x ≔ e ⊣ Γ' ,′ y :′ A
| re_ex_move : forall Γ x A ψ y e Γ'
  , y `in` fex_psi ψ `union` fex_aexpr e
  → Γ ‖ ^y :′ A :: ψ ⊢ ^x ≔ e ⊣ Γ'
  → Γ ,′ ^y :′ A ‖ ψ ⊢ ^x ≔ e ⊣ Γ'
| re_ex_stay : forall Γ x A ψ y e Γ'
  , y `notin` fex_psi ψ `union` fex_aexpr e
  → Γ ‖ ψ ⊢ ^x ≔ e ⊣ Γ'
  → Γ ,′ ^y :′ A ‖ ψ ⊢ ^x ≔ e ⊣ Γ' ,′ ^y :′ A
| re_k_move : forall Γ k ψ x e Γ'
  , k `in` fkv_psi ψ `union` fkv_aexpr e
  → Γ ‖ ⧼^k⧽ :: ψ ⊢ ^x ≔ e ⊣ Γ'
  → Γ ,′ ⧼^k⧽ ‖ ψ ⊢ ^x ≔ e ⊣ Γ'
| re_k_stay : forall Γ k ψ x e Γ'
  , k `notin` fkv_psi ψ `union` fkv_aexpr e
  → Γ ‖ ψ ⊢ ^x ≔ e ⊣ Γ'
  → Γ ,′ ⧼^k⧽ ‖ ψ ⊢ ^x ≔ e ⊣ Γ' ,′ ⧼^k⧽
where "G1 ‖ psi ⊢ ^ x ≔ e ⊣ G2" := (reorder G1 psi x e G2) : type_scope
.

#[export]
Hint Constructors reorder : core.

(* variance sign for monoization *)
Inductive vsign : Set :=
| v_pos : vsign
| v_neg : vsign
| v_neu : vsign
.

Notation "⊕" := v_pos.
Notation "⊖" := v_neg.
Notation "⊚" := v_neu.

Definition vneg (s : vsign) : vsign :=
  match s with
  | ⊕ => ⊖
  | ⊖ => ⊕
  | ⊚ => ⊚
  end
.

Reserved Notation "e1 ⤚ s ⇥ e2 ‖ bs \ L"
  (at level 65, s at level 0, e2 at level 50, bs at level 60, no associativity).
Inductive monoize : atoms → aexpr → vsign → aexpr → list binding → Prop :=
| mz_var   : forall x s L, `′x  ⤚ s ⇥ `′x  ‖ nil \ L
| mz_var_b : forall x s L, ↑′x  ⤚ s ⇥ ↑′x  ‖ nil \ L
| mz_kind  : forall k s L, ⧼k⧽′ ⤚ s ⇥ ⧼k⧽′ ‖ nil \ L
| mz_ex    : forall x s L, `^x  ⤚ s ⇥ `^x  ‖ nil \ L
| mz_num : forall n s L, ae_num n ⤚ s ⇥ ae_num n ‖ nil \ L
| mz_int : forall   s L, ae_int   ⤚ s ⇥ ae_int   ‖ nil \ L
| mz_bot : forall s ψ L
  , ae_bot ⤚ s ⇥ ae_bot ‖ ψ \ L
| mz_app : forall f1 f2 a s ψ L
  , mono_atype a
  → f1 ⤚ s ⇥ f2 ‖ ψ \ L
  → ae_app f1 a ⤚ s ⇥ ae_app f2 a ‖ ψ \ L
| mz_abs : forall e1 e2 s ψ L
  , e1 ⤚ s ⇥ e2 ‖ ψ \ L
  → λ′ e1 ⤚ s ⇥ λ′ e2 ‖ ψ \ L
| mz_pi : forall A1 A2 B1 B2 s ψ1 ψ2 L
  , A1 ⤚ (vneg s) ⇥ A2 ‖ ψ1 \ L
  → B1 ⤚ s ⇥ B2 ‖ ψ2 \ L
  → ae_pi A1 B1 ⤚ s ⇥ ae_pi A2 B2 ‖ ψ1 ++ ψ2 \ L
| mz_bind : forall e1 e2 s ψ L
  , e1 ⤚ s ⇥ e2 ‖ ψ \ L
  → Λ′ e1 ⤚ s ⇥ Λ′ e2 ‖ ψ \ L
| mz_forall_pos : forall L A B C ψ x
  , x `notin` L
  → B ^^′ `^x ⤚ ⊕ ⇥ C ‖ ψ \ add x L
  → ae_all A B ⤚ ⊕ ⇥ C ‖ x :′ A :: ψ \ L
| mz_forall_neg : forall L A B C ψ x
  , (forall x, x `notin` L → x `notin` fv_aexpr (B ^`′ x))
  → B ^`′ x ⤚ ⊖ ⇥ C ‖ ψ \ L
  → ae_all A B ⤚ ⊖ ⇥ C ‖ ψ \ L
| mz_castdn : forall e1 e2 s ψ L
  , e1 ⤚ s ⇥ e2 ‖ ψ \ L
  → ae_castdn e1 ⤚ s ⇥ ae_castdn e2 ‖ ψ \ L
| mz_castup : forall e1 e2 s ψ L
  , e1 ⤚ s ⇥ e2 ‖ ψ \ L
  → ae_castup e1 ⤚ s ⇥ ae_castup e2 ‖ ψ \ L
| mz_anno : forall e1 e2 A s ψ L
  , e1 ⤚ s ⇥ e2 ‖ ψ \ L
  → ae_anno e1 A ⤚ s ⇥ ae_anno e2 A ‖ ψ \ L
where "e1 ⤚ s ⇥ e2 ‖ bs \ L" := (monoize L e1 s e2 bs) : type_scope.

#[export]
Hint Constructors monoize : core.

Reserved Notation "⟦ e /′ ^ x ⟧ G"
  (at level 56, e at level 50, x at level 0, right associativity).
Fixpoint subst_ex (e : aexpr) (x : var) (Γ : worklist) : worklist :=
  match Γ with
  | wl_nil => wl_nil
  | Γ' ⊨′ w => ⟦ e /′ ^x ⟧ Γ' ⊨′ ex_subst_work e x w
  | Γ' ,′ y :′ A => ⟦ e /′ ^x ⟧ Γ' ,′ y :′ ex_subst_aexpr e x A
  | Γ' ,′ ⧼^k⧽ => ⟦ e /′ ^x ⟧ Γ' ,′ ⧼^k⧽
  | Γ' ,′ ^y :′ A =>
    if eqb x y then Γ'
      else ⟦ e /′ ^x ⟧ Γ' ,′ ^y :′ ex_subst_aexpr e x A
  end
where "⟦ e /′ ^ x ⟧ G" := (subst_ex e x G) : worklist_scope
.

Reserved Notation "⟦ k /′ ⧼ x ⧽ ⟧ G"
  (at level 56, k at level 50, x at level 0, right associativity).
Fixpoint subst_k (k : akind) (x : var) (Γ : worklist) : worklist :=
  match Γ with
  | wl_nil => wl_nil
  | Γ' ⊨′ w => ⟦ k /′ ⧼ x ⧽ ⟧ Γ' ⊨′ k_subst_work k x w
  | Γ' ,′  y :′ A => ⟦ k /′ ⧼ x ⧽ ⟧ Γ' ,′  y :′ k_subst_aexpr k x A
  | Γ' ,′ ^y :′ A => ⟦ k /′ ⧼ x ⧽ ⟧ Γ' ,′ ^y :′ k_subst_aexpr k x A
  | Γ' ,′ ⧼^y⧽ =>
    if eqb x y then Γ' else ⟦ k /′ ⧼x⧽ ⟧ Γ' ,′ ⧼^y⧽
  end
where "⟦ k /′ ⧼ x ⧽ ⟧ G" := (subst_k k x G) : worklist_scope
.

Inductive kind_syn_eq : akind → akind → Prop :=
| kseq_star : kind_syn_eq ak_star ak_star
| kseq_box  : kind_syn_eq ak_box  ak_box
| kseq_ex_l : forall x k, kind_syn_eq (ak_ex x) k
| kseq_ex_r : forall x k, kind_syn_eq k (ak_ex x)
.

Reserved Notation "e1 ≃ e2" (at level 65, e2 at level 50, no associativity).
Inductive syn_eq : aexpr → aexpr → Prop :=
| seq_ex_l : forall x e, mono_atype e → `^x ≃ e
| seq_ex_r : forall x e, mono_atype e → e ≃ `^x
| seq_var  : forall x, `′x ≃ `′x
| seq_kind : forall k1 k2, kind_syn_eq k1 k2 → ⧼k1⧽′ ≃ ⧼k2⧽′
| seq_num  : forall n, ae_num n ≃ ae_num n
| seq_int  : ae_int ≃ ae_int
| seq_bot  : ae_bot ≃ ae_bot
| seq_app : forall f1 f2 a1 a2
  , f1 ≃ f2
  → a1 ≃ a2
  → ae_app f1 a2 ≃ ae_app f2 a2
| seq_abs : forall L e1 e2
  , (forall x, x `notin` L → e1 ^`′ x ≃ e2 ^`′ x)
  → ae_abs e1 ≃ ae_abs e2
| seq_pi : forall L A1 A2 B1 B2
  , A1 ≃ A2
  → (forall x, x `notin` L → B1 ^`′ x ≃ B2 ^`′ x)
  → ae_pi A1 B1 ≃ ae_pi A2 B2
| seq_bind : forall L e1 e2
  , (forall x, x `notin` L → e1 ^`′ x ≃ e2 ^`′ x)
  → ae_bind e1 ≃ ae_bind e2
| seq_all : forall L A1 A2 B1 B2
  , A1 ≃ A2
  → (forall x, x `notin` L → B1 ^`′ x ≃ B2 ^`′ x)
  → ae_all A1 B1 ≃ ae_all A2 B2
| seq_castup : forall e1 e2 , e1 ≃ e2 → ae_castup e1 ≃ ae_castup e2
| seq_castdn : forall e1 e2 , e1 ≃ e2 → ae_castdn e1 ≃ ae_castdn e2
| seq_anno : forall e1 e2 A1 A2
  , e1 ≃ e2 → A1 ≃ A2
  → e1 ::′ A1 ≃ e2 ::′ A2
where "e1 ≃ e2" := (syn_eq e1 e2) : type_scope
.


Reserved Notation "⪧′ wl" (at level 65, no associativity).
Inductive wl_step : worklist -> Prop :=
| st_nil : ⪧′ wl_nil
(* decl-like inference *)
| st_var : forall Γ x A c
  , x :′ A  ∈′ Γ
  → ⪧′ Γ ⫢′ c $′ A
  → ⪧′ Γ ⊨′ `′ x ⇒′ c
| st_num : forall Γ n c
  , ⪧′ Γ ⫢′ c $′ ae_int
  → ⪧′ Γ ⊨′ ae_num n ⇒′ c
| st_int : forall Γ c
  , ⪧′ Γ ⫢′ c $′ ⋆′
  → ⪧′ Γ ⊨′ ae_int ⇒′ c
| st_star_inf : forall Γ c
  , ⪧′ Γ ⫢′ c $′ ◻′
  → ⪧′ Γ ⊨′ ⋆′ ⇒′ c
| st_star_chk : forall Γ
  , ⪧′ Γ
  → ⪧′ Γ ⊨′ ⋆′ ⇐′ ◻′
| st_bot : forall L Γ b A
  , (forall k, k `notin` L -> ⪧′ Γ ,?′ b ,′ ⧼^k ⧽ ⊨′ A ⇐′ ⧼`^k⧽)
  → ⪧′ Γ ⊨′ b ⊢? ae_bot <: ae_bot ⇐′ A
| st_app : forall Γ f1 f2 a1 a2 c
  , ⪧′ Γ ⊨′ f1 <: f2 ⇒′ ⦃ ↑′0 ⋅ a1 & a2 ⇒′ c ⦄
  -> ⪧′ Γ ⊨′ ae_app f1 a1 <: ae_app f2 a2 ⇒′ c
| st_abs : forall L Γ b e1 e2 A B
  , (forall x, x `notin` L → forall k1, k1 `notin` add x L
    → forall k2, k2 `notin` add k1 (add x L)
      → ⪧′ Γ ,?′ b ,′ ⧼^k2⧽ ⊨′ A ⇐′ ⧼`^k1⧽
      ⊨′ x :?′ A ⊢? B ^`′ x ⇐′ ⧼`^k2⧽
      ⊨′ x :?′ A ⊢? e1 ^`′ x <: e2 ^`′ x ⇐′ B ^`′ x)
  → ⪧′ Γ ⊨′ b ⊢? λ′ e1 <: λ′ e2 ⇐′ ae_pi A B
| st_pi : forall L Γ A1 A2 B1 B2 c
  , (forall x, x `notin` L → forall k1, k1 `notin` add x L
    → forall k2, k2 `notin` add k1 (add x L)
    → ⪧′ Γ ,′ ⧼^k2⧽ ⫢′ c $′ ⧼`^k2⧽
      ⊨′ x :?′ A1 ⊢? B1 ^`′ x ⇐′ ⧼`^k2⧽
      ⊨′ x :?′ A2 ⊢? B1 ^`′ x <: B2 ^`′ x ⇐′ ⧼`^k2⧽
      ,′ ⧼^k1⧽ ⊨′ A2 <: A2 ⇐′ ⧼`^k1⧽)
  → ⪧′ Γ ⊨′ ae_pi A1 B1 <: ae_pi A2 B2 ⇒′ c
| st_bind : forall L Γ b A B e1 e2 c
  , (forall x, x `notin` L → forall k1, k1 `notin` add x L
    → forall k2, k2 `notin` add k1 (add x L)
    → ⪧′ Γ ,?′ b ,′ ⧼^k2⧽ ⊨′ A ⇐′ ⧼`^k1⧽
      ⊨′ x :?′ A ⊢? B ^`′ x ⇐′ ⧼`^k2⧽
      ⊨′ x :?′ A ⊢? e1 ^`′ x <: e2 ^`′ x ⇐′ B ^`′ x)
  → ⪧′ Γ ⊨′ b ⊢? Λ′ e1 <: Λ′ e2 ⇐′ c
| st_forall_l : forall L Γ A B C c
  , (forall x, x `notin` L → forall k, k `notin` add x L
    → forall t, t `notin` add k (add x L)
    → ⪧′ Γ ⫢′ c $′ ⋆′ ,′ ⧼^k⧽ ⊨′ A ⇐′ ⧼`^k⧽
      ⊨′ x :?′ A ⊢? B ^`′ x ⇐′ ⧼`^k⧽
      ,′ ^t :′ A ⊨′ B ^^′ `^t <: C ⇐′ ⋆′)
  → ⪧′ Γ ⊨′ ae_all A B <: C ⇒′ c
| st_forall_r : forall L Γ A B C c
  , (forall x, x `notin` L → forall k, k `notin` add x L
    → ⪧′ Γ ⫢′ c $′ ⋆′ ,′ ⧼^k⧽ ⊨′ B ⇐′ ⧼`^k⧽
      ⊨′ x :?′ B ⊢? A <: C ^`′ x ⇐′ ⧼`^k⧽ ⊨′ A ⇐′ ⋆′)
  → ⪧′ Γ ⊨′ A <: ae_all B C ⇒′ c
| st_forall : forall L Γ A1 A2 B C c
  , (forall x, x `notin` L → forall k, k `notin` add x L
    → ⪧′ Γ ⫢′ c $′ ⋆′ ,′ ⧼^k⧽
      ⊨′ A1 ⇐′ ⧼`^k⧽ ⊨′ A2 ⇐′ ⧼`^k⧽
      ⊨′ x :?′ A1 ⊢? B ⇐′ ⋆′
      ⊨′ x :?′ A2 ⊢? ae_all A1 B <: C ^`′ x ⇐′ ⋆′)
  → ⪧′ Γ ⊨′ ae_all A1 B <: ae_all A2 C ⇒′ c
| st_castdn : forall Γ e1 e2 c
  , ⪧′ Γ ⊨′ e1 <: e2 ⇒′ ⦃ ↑′0 ⟼′ c ⦄
  → ⪧′ Γ ⊨′ ae_castdn e1 <: ae_castdn e2 ⇒′ c
| st_castup : forall L Γ A e1 e2 B
  , A ⟶′ B
  → (forall k, k `notin` L
    → ⪧′ Γ ,′ ⧼^k ⧽ ⊨′ A ⇐′ ⧼`^k⧽ ⊨′ e1 <: e2 ⇐′ B)
  → ⪧′ Γ ⊨′ ae_castup e1 <: ae_castup e2 ⇐′ A
| st_anno : forall L Γ e1 e2 A1 A2 c
  , (forall k, k `notin` L
    → ⪧′ Γ ⫢′ c $′ A1 ,′ ⧼^k⧽
      ⊨′ A1 <: A2 ⇐′ ⧼`^k⧽ ⊨′ A2 <: A2 ⇐′ ⧼`^k⧽
      ⊨′ e1 <: e2 ⇐′ A1)
  → ⪧′ Γ ⊨′ e1 ::′ A1 <: e2 ::′ A2 ⇒′ c

(* ex vars *)
| st_ex_eq : forall Γ x A c
  , ^x :′ A  ∈′ Γ
  → ⪧′ Γ ⫢′ c $′ A
  → ⪧′ Γ ⊨′ `^x <: `^x ⇒′ c
| st_ex_l : forall L Γ Γ' x A e e' ψ c
  , ^x :′ A  ∈′ Γ → `^x <> e
  → e ⤚ ⊖ ⇥ e' ‖ ψ \ L
  → Γ ⫢′ to_wl ψ ‖ nil ⊢ ^x ≔ e' ⊣ Γ'
  → (forall k, k `notin` L `union` psi_dom ψ
    → ⪧′ ⟦e' /′ ^x⟧ Γ' ⫢′ ⟦e' /′ ^x⟧ c $′ A
      ⊨′ e' ⇒′ (wl_nil ,′ ⧼^k⧽ ⊨′ ↑′0 <: A ⇐′ ⧼`^k⧽))
  → ⪧′ Γ ⊨′ `^x <: e ⇒′ c
| st_ex_r : forall L Γ Γ' x A e e' ψ c
  , ^x :′ A  ∈′ Γ → `^x <> e
  → e ⤚ ⊕ ⇥ e' ‖ ψ \ L
  → Γ ⫢′ to_wl ψ ‖ nil ⊢ ^x ≔ e' ⊣ Γ'
  → (forall k, k `notin` L `union` psi_dom ψ
    → ⪧′ ⟦e' /′ ^x⟧ Γ' ⫢′ ⟦e' /′ ^x⟧ c $′ A
      ⊨′ e' ⇒′ (wl_nil ,′ ⧼^k⧽ ⊨′ ↑′0 <: A ⇐′ ⧼`^k⧽))
  → ⪧′ Γ ⊨′ e <: `^x ⇒′ c

(* infer_app *)
| st_iapp_forall : forall L Γ A B e1 e2 c
  , (forall x, x `notin` L → forall y, y `notin` add x L
    → ⪧′ Γ ⊨′ x :?′ A ⊢? B ^`′ x ⇐′ ⋆′ ,′ ^y :′ A
      ⊨′ B ^^′ `^y ⋅ e1 & e2 ⇒′ c)
  → ⪧′ Γ ⊨′ ae_all A B ⋅ e1 & e2 ⇒′ c
| st_iapp_pi : forall L Γ A B e1 e2 c
  , (forall x, x `notin` L → forall k, k `notin` add x L
    → mono_atype e1 → mono_atype e2 → e1 ≃ e2
    → ⪧′ Γ ⫢′ c $′ B ^^′ e1 ⊨′ e1 <: e2 ⇐′ A ⊨′ e2 <: e1 ⇐′ A
      ,′ ⧼^k⧽ ⊨′ x :?′ A ⊢? B ⇐′ ⧼`^k⧽)
  → ⪧′ Γ ⊨′ ae_pi A B ⋅ e1 & e2 ⇒′ c
| st_iapp_ex : forall L Γ x e1 e2 c Γ1 Γ2
  , Γ = Γ1 ,′ ^x :′ ⋆′ ⫢′ Γ2
  → (forall A, A `notin` L → forall B, B `notin` add A L
    → forall k, k `notin` add A (add B L) → forall F, F = ae_pi `^A `^B
    → ⪧′ Γ1 ,′ ⧼^k⧽ ,′ ^A :′ ⧼`^k⧽ ,′ ^B :′ ⋆′ ⫢′ ⟦ F /′ ^x ⟧ Γ2
      ⊨′ F ⋅ [F /^ x ] e1 & [F /^ x] e2 ⇒′ ⟦ F /′ ^x ⟧ c)
  → ⪧′ Γ ⊨′ `^x ⋅ e1 & e2 ⇒′ c

(* general reduce *)
| st_gred : forall Γ A B c
  , A ⟶′ B
  → ⪧′ Γ ⫢′ c $′ B
  → ⪧′ Γ ⊨′ A ⟼′ c
| st_gred_forall : forall L Γ A B c
  , (forall x, x `notin` L
    → ⪧′ Γ ,′ ^x :′ A ⊨′ B ^^′ `^x ⟼′ c ⊨′ x :?′ A ⊢? B ⇐′ ⋆′)
  → ⪧′ Γ ⊨′ ae_all A B ⟼′ c

(* kind ex infer *)
| st_kv_eq : forall Γ x c
  , ⪧′ ⟦ak_star /′ ⧼x⧽⟧ Γ ⫢′ ⟦ak_star /′ ⧼x⧽⟧ c $′ ◻′
  → ⪧′ Γ ⊨′ ⧼`^x⧽ <: ⧼`^x⧽ ⇒′ c
| st_kv_lr : forall Γ x y c
  , x <> y
  → ⪧′ ⟦ak_star /′ ⧼y⧽⟧ ⟦ak_star /′ ⧼x⧽⟧ Γ
    ⫢′ ⟦ak_star /′ ⧼y⧽⟧ ⟦ak_star /′ ⧼x⧽⟧ c $′ ◻′
  → ⪧′ Γ ⊨′ ⧼`^x⧽ <: ⧼`^y⧽ ⇒′ c
| st_kv_l : forall Γ x c
  , ⪧′ ⟦ak_star /′ ⧼x⧽⟧ Γ ⫢′ ⟦ak_star /′ ⧼x⧽⟧ c $′ ◻′
  → ⪧′ Γ ⊨′ ⧼`^x⧽ <: ⋆′ ⇒′ c
| st_kv_r : forall Γ x c
  , ⪧′ ⟦ak_star /′ ⧼x⧽⟧ Γ ⫢′ ⟦ak_star /′ ⧼x⧽⟧ c $′ ◻′
  → ⪧′ Γ ⊨′ ⋆′ <: ⧼`^x⧽ ⇒′ c

(* check *)
| st_check : forall Γ e1 e2 b A
  , ⪧′ Γ ,?′ b ⊨′ e1 <: e2 ⇒′ ⦃ ↑′ 0 ≲′ A ⦄
  → ⪧′ Γ ⊨′ b ⊢? e1 <: e2 ⇐′ A
| st_comp_box_l : forall Γ k
  , ⪧′ ⟦ ak_box /′ ⧼k⧽ ⟧ Γ
  (*  (wl_step (wl_work Γ (w_compact (ae_kind ak_box) (ae_ex k))))) *)
  → ⪧′ Γ ⊨′ ◻′ ≲′ ⧼`^k⧽
| st_comp_box_r : forall Γ k
  , ⪧′ ⟦ ak_box /′ ⧼k⧽ ⟧ Γ
  → ⪧′ Γ ⊨′ ⧼`^k⧽ ≲′ ◻′
| st_comp_kv_eq : forall Γ k
  , ⪧′ Γ
  → ⪧′ Γ ⊨′ ⧼`^k⧽ ≲′ ⧼`^k⧽
| st_comp_kv : forall Γ x y
  , x <> y
  → in_scope Γ ⧼^x⧽ ⧼^y⧽
  → ⪧′ ⟦ ak_ex x /′ ⧼y⧽⟧ Γ
  → ⪧′ Γ ⊨′ ⧼`^x⧽ ≲′ ⧼`^y⧽
| st_comp_sub : forall L Γ A B
  , (forall k, k `notin` L → ⪧′ Γ,′ ⧼^k⧽ ⊨′ A <: B ⇐′ ⧼`^k⧽)
  → ⪧′ Γ ⊨′ A ≲′ B

(* elim bindings *)
| st_bind_var : forall L Γ x A
  , (forall k, k `notin` L → ⪧′ Γ ,′ ⧼^k⧽ ⊨′ A ⇐′ ⧼`^k⧽)
  → ⪧′ Γ ,′ x :′ A
| st_bind_ex : forall L Γ x A
  , (forall k, k `notin` L → ⪧′ Γ ,′ ⧼^k⧽ ⊨′ A ⇐′ ⧼`^k⧽)
  → ⪧′ Γ ,′ ^x :′ A
| st_bind_k : forall Γ k
  , ⪧′ Γ
  → ⪧′ Γ ,′ ⧼^k⧽
where "⪧′ wl" := (wl_step wl) : type_scope
.

#[export]
Hint Constructors wl_step : core.
