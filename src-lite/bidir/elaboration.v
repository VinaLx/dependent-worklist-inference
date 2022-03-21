Require Import decl.notations.
Require Import bidir.notations.
Require Import erased.ott.

Definition to_k (bk : bkind) : kind :=
  match bk with
  | bk_star => k_star
  | bk_box => k_box
  end
.

Inductive decl_app_fun : Type :=
| dfun_pi (A : expr) (B : expr)
.


Inductive wf_bcontext_elab : bcontext → context → Prop :=
| wfe_nil : wf_bcontext_elab bctx_nil ctx_nil
| wfe_cons : forall Γ' Γ x A' A k
  , wf_bcontext_elab Γ' Γ
  → x `notin` bctx_dom Γ'
  -> busub_elab Γ' A' A' d_infer ⧼k⧽' Γ A A ⧼(to_k k)⧽
  -> wf_bcontext_elab (Γ' ,' x : A') (Γ, x : A)
with infer_app_elab
  : bcontext -> bexpr → app_fun
  ->  context ->  expr -> decl_app_fun → Prop :=
| iappe_pi : forall L Γ' Γ A' A B' B k
  , infer_app_elab Γ' (be_pi A' B') (fun_pi A' B')
                   Γ  (e_pi A B)   (dfun_pi A B)
| iappe_all : forall L Γ' Γ A' A B' B t' t F' F
  , mono_btype t'
  -> busub_elab Γ' t' t' d_check A' Γ t t A
  -> infer_app_elab Γ' (B' ^^' t')    F' Γ (B ^^ t)    F
  -> infer_app_elab Γ' (be_all A' B') F' Γ (e_all A B) F
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
  , wf_bcontext_elab Γ' Γ -> in_bctx x A' Γ' → in_ctx x A Γ
  -> busub_elab Γ' `'x `'x d_infer A' Γ `x `x A
| bse_lit : forall Γ' Γ n
  , wf_bcontext_elab Γ' Γ
  -> busub_elab Γ' (be_num n) (be_num n) d_infer be_int Γ (e_num n) (e_num n) e_int
| bse_star : forall Γ' Γ dir
  , wf_bcontext_elab Γ' Γ
  -> busub_elab Γ' ⋆' ⋆' dir ◻' Γ ⋆ ⋆ ◻
| bse_int : forall Γ' Γ
  , wf_bcontext_elab Γ' Γ
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
| bse_app : forall Γ' Γ e1' e1 t' t e2' e2 A' A B' B C' C
  , mono_btype t'
  -> busub_elab Γ' e1' e2' d_infer A' Γ e1 e2 A
  -> infer_app_elab Γ' A' (fun_pi B' C') Γ A (dfun_pi B C)
  → busub_elab Γ' t' t' d_check B' Γ t t B
  -> busub_elab Γ' (be_app e1' t') (be_app e2' t') d_infer (C' ^^' t')
               Γ  ( e_app e1  t ) ( e_app e2  t ) (C ^^ t)
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

Definition to_bk (k : kind) : bkind :=
  match k with
  | k_star => bk_star
  | k_box  => bk_box
  end
.

Inductive wf_context_elab : context → bcontext → Prop :=
| wf_nil : wf_context_elab ctx_nil bctx_nil
| wf_cons : forall Γ x A k Γ' A'
  , wf_context_elab Γ Γ'
  -> x `notin` ctx_dom Γ
  -> usub_elab Γ A A ⧼k⧽ Γ' A' A' ⧼(to_bk k)⧽'
  -> wf_context_elab (Γ , x : A) (Γ' ,' x : A')
with usub_elab
  : context  → expr  → expr  → expr
  → bcontext → bexpr → bexpr → bexpr → Prop :=
| s_var : forall Γ x A Γ' A'
  , wf_context_elab Γ Γ'
  -> in_ctx x A Γ
  -> in_bctx x A' Γ'
  -> usub_elab Γ `x `x A Γ' `'x `'x A'
| s_lit : forall Γ n Γ'
  , wf_context_elab Γ Γ'
  → usub_elab Γ (e_num n) (e_num n) e_int Γ' (be_num n) (be_num n) be_int
| s_star : forall Γ Γ'
  , wf_context_elab Γ Γ'
  → usub_elab Γ ⋆ ⋆ ◻ Γ' ⋆' ⋆' ◻'
| s_int : forall Γ Γ'
  , wf_context_elab Γ Γ'
  -> usub_elab Γ e_int e_int ⋆ Γ' be_int be_int ⋆'
| s_bot : forall Γ A1 A2 Γ' A1' A2' k
  , usub_elab Γ A1 A2 ⧼k⧽ Γ' A1' A2' ⧼(to_bk k)⧽'
  → usub_elab Γ A2 A1 ⧼k⧽ Γ' A2' A1' ⧼(to_bk k)⧽'
  -> usub_elab Γ  (e_bot     A1 ) (e_bot     A2 ) A1
              Γ' (be_bot ::' A1') (be_bot ::' A2') A1'
| s_abs : forall L Γ Γ' A1 A1' e1 e1' B1 B1' A2 A2' e2 e2' B2 B2' k1 k2
  , usub_elab Γ A1 A2 ⧼k1⧽ Γ' A1' A2' ⧼(to_bk k1)⧽'
  → usub_elab Γ A2 A1 ⧼k1⧽ Γ' A2' A1' ⧼(to_bk k1)⧽'
  → (forall x , x \notin L
    → usub_elab (Γ , x : A1 ) (B1  ^`  x) (B2  ^`  x) ⧼k2⧽
                (Γ','x : A1') (B1' ^`' x) (B2' ^`' x) ⧼(to_bk k2)⧽')
  → (forall x , x \notin L
    → usub_elab (Γ , x : A1 ) (B2  ^`  x) (B1  ^`  x) ⧼k2⧽
                (Γ','x : A1') (B2' ^`' x) (B1' ^`' x) ⧼(to_bk k2)⧽')
  → (forall x , x \notin L
    → usub_elab (Γ , x : A1 ) (e1  ^`  x) (e2  ^`  x) (B1  ^`  x)
                (Γ','x : A1') (e1' ^`' x) (e2' ^`' x) (B1' ^`' x))
  → usub_elab Γ (λ_ A1, e1 : B1) (λ_ A2, e2 : B2) (e_pi A1 B1)
              Γ' (be_abs e1' ::' be_pi A1' B1')
                 (be_abs e1' ::' be_pi A2' B2') (be_pi A1' B1')
| s_pi : forall L Γ Γ' A1 A1' B1 B1' A2 A2' B2 B2' k1 k2
  , usub_elab Γ A1 A1 ⧼k1⧽ Γ' A1' A1' ⧼(to_bk k1)⧽'
  -> usub_elab Γ A2 A1 ⧼k1⧽ Γ' A2' A1' ⧼(to_bk k1)⧽'
  -> (forall x , x \notin  L
    → usub_elab (Γ , x : A1 ) (B1  ^`  x) (B1  ^`  x) ⧼k2⧽
                (Γ','x : A1') (B1' ^`' x) (B1' ^`' x) ⧼(to_bk k2)⧽')
  -> (forall x , x \notin  L
    → usub_elab (Γ , x : A2 ) (B1  ^`  x) (B2  ^`  x) ⧼k2⧽
                (Γ','x : A2') (B1' ^`' x) (B2' ^`' x) ⧼(to_bk k2)⧽')
  → usub_elab Γ  (e_pi  A1  B1 ) (e_pi  A2  B2 ) ⧼k2⧽
              Γ' (be_pi A1' B1') (be_pi A2' B2') ⧼(to_bk k2)⧽'
| s_app : forall Γ Γ' e1 e1' t t' e2 e2' A A' B B' k
  , mono_type t
  -> usub_elab Γ t t A Γ' t' t' A'
  -> usub_elab Γ e1 e2 (e_pi A B) Γ' e1' e2' (be_pi A' B')
  → usub_elab Γ A A ⧼k⧽ Γ' A' A' ⧼(to_bk k)⧽'
  -> usub_elab Γ  (e_app  e1  t ) (e_app  e2  t ) (B  ^^  t )
              Γ' (be_app e1' t') (be_app e2' t') (B' ^^' t')
| s_bind : forall L Γ Γ' A1 A1' e1 e1' B1 B1' A2 A2' e2 e2' B2 B2' k1
  , usub_elab Γ A1 A2 ⧼k1⧽ Γ' A1' A2' ⧼(to_bk k1)⧽'
  → usub_elab Γ A2 A1 ⧼k1⧽ Γ' A2' A1' ⧼(to_bk k1)⧽'
  → (forall x , x \notin L
    → usub_elab (Γ , x : A1 ) (B1  ^`  x) (B2  ^`  x) ⋆
                (Γ','x : A1') (B1' ^`' x) (B2' ^`' x) ⋆')
  → (forall x , x \notin L
    → usub_elab (Γ , x : A1 ) (B2  ^`  x) (B1  ^`  x) ⋆
                (Γ','x : A1') (B2' ^`' x) (B1' ^`' x) ⋆')
  → (forall x , x \notin L
    → usub_elab (Γ , x : A1 ) (e1  ^`  x) (e2  ^`  x) (B1  ^`  x)
                (Γ','x : A1') (e1' ^`' x) (e2' ^`' x) (B1' ^`' x))
  -> ( forall x , x \notin  L
      -> ( x  `notin` fv_eexpr (erase (e1  ^`  x))))
  -> ( forall x , x \notin  L
      -> ( x  `notin` fv_eexpr (erase (e2  ^`  x))))
  → usub_elab Γ (Λ A1, e1 : B1) (Λ A2, e2 : B2) (e_all A1 B1)
              Γ' (be_bind e1' ::' be_all A1' B1')
                 (be_bind e1' ::' be_all A2' B2') (be_all A1' B1')
| s_castup : forall Γ Γ' A1 A1' e1 e1' A2 A2' e2 e2' k B B'
  , usub_elab Γ A1 A2 ⧼k⧽ Γ' A1' A2' ⧼(to_bk k)⧽'
  → usub_elab Γ A2 A1 ⧼k⧽ Γ' A2' A1' ⧼(to_bk k)⧽'
  → A1 ⟶ B
  → A2 ⟶ B
  → usub_elab Γ e1 e2 B Γ' e1' e2' B'
  → usub_elab Γ  (e_castup A1 e1)       (e_castup A2 e2)      A1
              Γ' (be_castup e1' ::' A1') (be_castup e2' ::' A2') A1'
| s_castdn : forall Γ Γ' e1 e2 B k A e1' e2' A' B'
  , usub_elab Γ B B ⧼k⧽ Γ' B' B' ⧼(to_bk k)⧽'
  -> A ⟶ B
  -> usub_elab Γ e1 e2 A Γ' e1' e2' A'
  -> usub_elab Γ  (e_castdn  e1 ) (e_castdn  e2 ) B
              Γ' (be_castdn e1') (be_castdn e2') B'
| s_forall_l : forall L Γ Γ' A B C t A' B' C' t' k
  , mono_type t
  -> usub_elab Γ A A ⧼k⧽ Γ' A' A' ⧼(to_bk k)⧽'
  -> usub_elab Γ t t A Γ' t' t' A'
  -> usub_elab Γ (B ^^ t) C ⋆ Γ' (B' ^^' t') C' ⋆'
  -> (forall x , x \notin  L
    -> usub_elab (Γ , x : A) (B ^` x) (B ^` x) ⋆
                (Γ','x : A') (B' ^`' x) (B' ^`' x) ⋆')
  -> usub_elab Γ (e_all A B) C ⋆ Γ' (be_all A' B') C' ⋆'
| s_forall_r : forall L Γ Γ' A B C A' B' C' k
  , usub_elab Γ B B ⧼k⧽ Γ' B' B' ⧼(to_bk k)⧽'
  -> usub_elab Γ A A ⋆ Γ' A' A' ⋆'
  -> (forall x , x \notin L
    -> usub_elab (Γ ,  x : B ) A  (C  ^`  x) ⋆
                (Γ',' x : B') A' (C' ^`' x) ⋆')
  -> usub_elab Γ A (e_all B C) ⋆ Γ' A' (be_all B' C') ⋆'
| s_forall : forall L Γ Γ' A1 B A2 C A1' A2' B' C' k
  , usub_elab Γ A1 A2 ⧼k⧽ Γ' A1' A2' ⧼(to_bk k)⧽'
  → usub_elab Γ A2 A1 ⧼k⧽ Γ' A2' A1' ⧼(to_bk k)⧽'
  -> (forall x , x \notin  L
    -> usub_elab (Γ , x : A1 ) (B  ^`  x) (C  ^`  x) ⋆
                (Γ','x : A1') (B' ^`' x) (C' ^`' x) ⋆')
  -> usub_elab Γ  (e_all  A1  B ) (e_all  A2  C) ⋆
              Γ' (be_all A1' B') (be_all A2' C') ⋆'
| s_sub : forall Γ Γ' e1 e2 B A e1' e2' B' A' k
  , usub_elab Γ e1 e2 A Γ' e1' e2' A'
  -> usub_elab Γ A B ⧼k⧽ Γ' A' B' ⧼(to_bk k)⧽'
  → usub_elab Γ B B ⧼k⧽ Γ' B' B' ⧼(to_bk k)⧽'
  -> usub_elab Γ e1 e2 B Γ' (e1' ::' B') (e2' ::' B') B'.



Scheme usub_elab_mut
  :=   Induction for usub_elab Sort Prop
  with Induction for wf_context_elab Sort Prop.

Scheme busub_elab_mut
  :=   Induction for busub_elab Sort Prop
  with Induction for wf_bcontext_elab Sort Prop
  with Induction for infer_app_elab Sort Prop
  with Induction for greduce_elab Sort Prop.
