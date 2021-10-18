Require Import worklist.
Require Import decl_worklist.

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
| wiso_iapp : forall L A A' e1 e1' e2 e2' c c'
  , expr_iso A A' → expr_iso e1 e1' → expr_iso e2 e2'
  → (forall x, x `notin` L → worklist_iso (c $ `x) (c' $′ `′x))
  → work_iso (A ⋅ e1 & e2 ⇒ c) (A' ⋅ e1' & e2' ⇒′ c')
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
