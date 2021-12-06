Require Import decl_notations.
Require Import bidir_notations.
Require Import erased_ott.

Definition to_k (bk : bkind) : kind :=
  match bk with
  | bk_star => k_star
  | bk_box => k_box
  end
.


Inductive wf_context_elab : bcontext → context → Prop :=
| wfe_nil : wf_context_elab bctx_nil ctx_nil
| wfe_cons : forall Γ' Γ x A' A k
  , wf_context_elab Γ' Γ
  → x `notin` bctx_dom Γ'
  -> busub_elab Γ' A' A' d_infer ⧼k⧽' Γ A A ⧼(to_k k)⧽
  -> wf_context_elab (Γ' ,' x : A') (Γ, x : A)
with infer_app_elab
  : bcontext -> bexpr -> bexpr -> bexpr
  -> expr → expr → Prop :=
| iappe_pi : forall L Γ' Γ A' A B' B e' e k
  , (forall x, x \notin L
    -> busub_elab (Γ' ,' x : A') (B' ^`' x) (B' ^`' x) d_infer ⧼k⧽'
                 (Γ  ,  x : A ) (B  ^`  x) (B ^`  x) ⧼(to_k k)⧽)
  → busub_elab Γ' e' e' d_check A' Γ e e A
  -> infer_app_elab Γ' (be_pi A' B') e' (B' ^^' e') e (B ^^ e)
| iappe_all : forall L Γ' Γ A' A B' B e' e C' C t' t
  , mono_btype t'
  -> busub_elab Γ' t' t' d_check A' Γ t t A
  -> (forall x , x \notin  L
    -> busub_elab (Γ' ,' x : A') (B' ^`' x) (B' ^`' x) d_infer ⋆'
                 (Γ  ,  x : A ) (B  ^`  x) (B  ^`  x) ⋆)
  -> infer_app_elab Γ' (B' ^^' t') e' C' e C
  -> infer_app_elab Γ' (be_all A' B') e' C' e C
with greduce_elab : bcontext -> bexpr -> bexpr → Prop :=
| gre_reduce : forall Γ' e1 e2
  , lc_bcontext Γ'
  -> breduce e1 e2
  -> greduce_elab Γ' e1 e2
| gre_all : forall L Γ' Γ A' A B' B C' t
  , mono_btype t
  -> busub Γ' t t d_check A'
  -> (forall x , x \notin  L
    -> busub_elab (Γ' ,' x : A') (B' ^`' x) (B' ^`' x) d_infer ⋆'
                 (Γ  ,  x : A ) (B  ^`  x) (B  ^`  x) ⋆)
  -> greduce_elab Γ' (B' ^^' t) C'
  -> greduce_elab Γ' (be_all A' B') C'
with busub_elab
  : bcontext → bexpr → bexpr → dir  → bexpr
  →  context →  expr →  expr → expr → Prop :=
| bse_var : forall Γ Γ' x A A'
  , wf_context_elab Γ' Γ -> in_bctx x A' Γ' → in_ctx x A Γ
  -> busub_elab Γ' `'x `'x d_infer A' Γ `x `x A
| bse_lit : forall Γ' Γ n
  , wf_context_elab Γ' Γ
  -> busub_elab Γ' (be_num n) (be_num n) d_infer be_int Γ (e_num n) (e_num n) e_int
| bse_star : forall Γ' Γ dir
  , wf_context_elab Γ' Γ
  -> busub_elab Γ' ⋆' ⋆' dir ◻' Γ ⋆ ⋆ ◻
| bse_int : forall Γ' Γ
  , wf_context_elab Γ' Γ
  -> busub_elab Γ' be_int be_int d_infer ⋆' Γ e_int e_int ⋆
| bse_bot : forall Γ' Γ A' A k
  , busub_elab Γ' A' A' d_infer ⧼k⧽' Γ A A ⧼(to_k k)⧽
  -> busub_elab Γ' be_bot be_bot d_check A' Γ (e_bot A) (e_bot A) A
| bse_abs : forall L Γ' Γ e1 e1' e2 e2' A A' B B' k1 k2
  , busub_elab Γ' A' A' d_infer ⧼k1⧽' Γ A A ⧼(to_k k1)⧽
  -> (forall x, x \notin L
    -> busub_elab (Γ' ,' x : A') (B' ^`' x) (B' ^`' x) d_infer ⧼k2⧽'
                 (Γ  ,  x : A ) (B  ^`  x) (B  ^`  x) ⧼(to_k k2)⧽)
  -> (forall x, x \notin L
    -> busub_elab (Γ' ,' x : A') (e1' ^`' x) (e2' ^`' x) d_check (B' ^`' x)
                 (Γ  ,  x : A ) (e1  ^`  x) (e2  ^`  x) (B ^` x))
  -> busub_elab Γ' (be_abs e1') (be_abs e2') d_check (be_pi A' B')
               Γ (λ_ A, e1 : B) (λ_ A, e2 : B) (e_pi A B)
| bse_pi : forall L Γ Γ' A1 A1' A2 A2' B1 B1' B2 B2' dir k1 k2
  , busub_elab Γ' A1' A1' d_infer ⧼k1⧽' Γ A1 A1 ⧼(to_k k1)⧽
  -> busub_elab Γ' A2' A1' d_infer ⧼k1⧽' Γ A2 A1 ⧼(to_k k1)⧽
  -> (forall x, x \notin  L
    -> busub_elab (Γ' ,' x : A1') (B1' ^`' x) (B1' ^`' x) dir ⧼k2⧽'
                 (Γ  ,  x : A1 ) (B1  ^`  x) (B1  ^`  x) ⧼(to_k k2)⧽)
  -> (forall x, x \notin  L
    -> busub_elab (Γ' ,' x : A2') (B1' ^`' x) (B2' ^`' x) dir ⧼k2⧽'
                 (Γ  ,  x : A2 ) (B1  ^`  x) (B2  ^`  x) ⧼(to_k k2)⧽)
  -> busub_elab Γ' (be_pi A1' B1') (be_pi A2' B2') dir ⧼k2⧽'
               Γ  ( e_pi A1  B1 ) ( e_pi A2  B2 ) ⧼(to_k k2)⧽
| bse_app : forall Γ' Γ e1' e1 t' t e2' e2 B' B A' A
  , mono_btype t'
  -> busub_elab Γ' e1' e2' d_infer A' Γ e1 e2 A
  -> infer_app_elab Γ' A' t' B' t B
  -> busub_elab Γ' (be_app e1' t') (be_app e2' t') d_infer B'
               Γ  ( e_app e1  t ) ( e_app e2  t ) B
| bse_bind : forall L Γ' Γ e1' e1 e2' e2 A' A B' B k
  , busub_elab Γ' A' A' d_infer ⧼k⧽' Γ A A ⧼(to_k k)⧽
  -> (forall x , x \notin L
    -> busub_elab (Γ' ,' x : A') (B' ^`' x) (B' ^`' x) d_infer ⋆'
                 (Γ  ,  x : A ) (B  ^`  x) (B  ^`  x) ⋆)
  -> (forall x , x \notin L
    -> busub_elab (Γ' ,' x : A') (e1' ^`' x) (e2' ^`' x) d_check (B' ^`' x)
                 (Γ  ,  x : A ) (e1  ^`  x) (e2  ^`  x) (B ^` x))
  -> (forall x , x \notin  L -> x `notin` fv_eexpr (berase (e1' ^`' x)))
  -> (forall x , x \notin  L -> x `notin` fv_eexpr (berase (e2' ^`' x)))
  -> busub_elab Γ' (be_bind e1') (be_bind e2') d_check (be_all A' B')
               Γ (Λ A, e1 : B) (Λ A, e2 : B) (e_all A B)
| bse_castup : forall Γ' Γ e1' e1 e2' e2 A' A k B' B
  , busub_elab Γ' A' A' d_infer ⧼k⧽' Γ A A ⧼(to_k k)⧽
  -> breduce A' B'
  -> busub_elab Γ' e1' e2' d_check B' Γ e1 e2 B
  -> busub_elab Γ' (be_castup e1') (be_castup e2') d_check A'
               Γ  (e_castup A e1) (e_castup A e2) A
| bse_castdn : forall Γ' Γ e1' e1 e2' e2 B' B k A' A
  , busub_elab Γ' B' B' d_infer ⧼k⧽' Γ B B ⧼(to_k k)⧽
  -> greduce_elab Γ' A' B'
  -> busub_elab Γ' e1' e2' d_infer A' Γ e1 e2 A
  -> busub_elab Γ' (be_castdn e1') (be_castdn e2') d_infer B'
               Γ  ( e_castdn e1 ) ( e_castdn e2 ) B
| bse_forall_l : forall L Γ' Γ A' A B' B C' C t' t k
  , mono_btype t'
  -> busub_elab Γ' A' A' d_infer ⧼k⧽' Γ A A ⧼(to_k k)⧽
  -> busub_elab Γ' t' t' d_check A' Γ t t A
  -> busub_elab Γ' (B' ^^' t') C' d_infer ⋆' Γ (B ^^ t) C ⋆
  -> (forall x , x \notin  L
    -> busub_elab (Γ' ,' x : A') (B' ^`' x) (B' ^`' x) d_infer ⋆'
                 (Γ  ,  x : A ) (B  ^`  x) (B  ^`  x) ⋆)
  -> busub_elab Γ' (be_all A' B') C' d_infer ⋆'
               Γ  ( e_all A  B ) C ⋆
| bse_forall_r : forall L Γ' Γ A' A B' B C' C k
  , busub_elab Γ' B' B' d_infer ⧼k⧽' Γ B B ⧼(to_k k)⧽
  -> busub_elab Γ' A' A' d_infer ⋆' Γ A A ⋆
  -> (forall x , x \notin  L
    -> busub_elab (Γ' ,' x : B') A' (C' ^`' x)  d_infer ⋆'
                 (Γ  ,  x : B ) A  (C  ^`  x) ⋆)
  -> busub_elab Γ' A' (be_all B' C') d_infer ⋆'
               Γ  A  ( e_all B  C ) ⋆
| bse_forall : forall L Γ' Γ A1 A1' B B' A2 A2' C C' k
  , busub_elab Γ' A1' A2' d_infer ⧼k⧽' Γ A1 A2 ⧼(to_k k)⧽
  -> busub_elab Γ' A2' A1' d_infer ⧼k⧽' Γ A2 A1 ⧼(to_k k)⧽
  -> (forall x , x \notin L
    -> busub_elab (Γ' ,' x : A1') (B' ^`' x) (C' ^`' x) d_infer ⋆'
                 (Γ  ,  x : A1 ) (B  ^`  x) (C  ^`  x) ⋆)
  -> busub_elab Γ' (be_all A1' B') (be_all A2' C') d_infer ⋆'
               Γ  ( e_all A1  B ) ( e_all A2  C ) ⋆
| bse_anno : forall Γ' Γ e1 e1' A1 A1' e2 e2' A2 A2' k
  , busub_elab Γ' e1' e2' d_check A1' Γ e1 e2 A1
  -> busub_elab Γ' A1' A2' d_infer ⧼k⧽' Γ A1 A2 ⧼(to_k k)⧽
  -> busub_elab Γ' A2' A1' d_infer ⧼k⧽' Γ A1 A2 ⧼(to_k k)⧽
  -> busub_elab Γ' (be_anno e1' A1') (be_anno e2' A2') d_infer A1'
               Γ e1 e2 A1
| bse_sub : forall Γ' Γ e1' e1 e2' e2 B B' A A' k
  , busub_elab Γ' e1' e2' d_infer A' Γ e1 e2 A
  -> busub_elab Γ' A' B' d_infer ⧼k⧽' Γ A B ⧼(to_k k)⧽
  -> busub_elab Γ' e1' e2' d_check B' Γ e1 e2 B
.
