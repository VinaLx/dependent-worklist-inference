(* generated by Ott 0.31, locally-nameless lngen from: alg.ott *)
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
(** syntax *)
Definition aexprvar : Set := var.
Definition number : Set := nat.
Definition exvar : Set := var.
Definition kindvar : Set := var.

Inductive akind : Set := 
 | ak_star : akind
 | ak_box : akind
 | ak_ex (kx:kindvar).

Inductive abody : Set := 
 | ab_anno (e:aexpr) (A:aexpr)
with aexpr : Set := 
 | ae_var_b (_:nat)
 | ae_var_f (x:aexprvar)
 | ae_kind (k:akind)
 | ae_ex (ex:exvar)
 | ae_num (n:number)
 | ae_int : aexpr
 | ae_bot (A:aexpr)
 | ae_app (e1:aexpr) (e2:aexpr)
 | ae_abs (A:aexpr) (ab:abody)
 | ae_pi (A:aexpr) (B:aexpr)
 | ae_bind (A:aexpr) (ab:abody)
 | ae_all (A:aexpr) (B:aexpr)
 | ae_castup (A:aexpr) (e:aexpr)
 | ae_castdn (e:aexpr).

Inductive obind : Set := 
 | ob_none : obind
 | ob_bind (x:aexprvar) (A:aexpr).

Inductive binding : Set := 
 | b_var (x:aexprvar) (A:aexpr)
 | b_ex (ex:exvar) (A:aexpr)
 | b_kind (kx:kindvar).

Inductive work : Set := 
 | w_check (ob:obind) (e1:aexpr) (e2:aexpr) (A:aexpr)
 | w_infer (e1:aexpr) (e2:aexpr) (wl:worklist)
 | w_infer_app (A:aexpr) (e1:aexpr) (e2:aexpr) (wl:worklist)
 | w_reduce (e:aexpr) (wl:worklist)
 | w_compact (A:aexpr) (B:aexpr)
with worklist : Set := 
 | wl_nil : worklist
 | wl_cons (wl:worklist) (w:work)
 | wl_bind (wl:worklist) (b:binding).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_aexpr_wrt_aexpr_rec (k:nat) (e_5:aexpr) (e__6:aexpr) {struct e__6}: aexpr :=
  match e__6 with
  | (ae_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => ae_var_b nat
        | inleft (right _) => e_5
        | inright _ => ae_var_b (nat - 1)
      end
  | (ae_var_f x) => ae_var_f x
  | (ae_kind k) => ae_kind k
  | (ae_ex ex) => ae_ex ex
  | (ae_num n) => ae_num n
  | ae_int => ae_int 
  | (ae_bot A) => ae_bot (open_aexpr_wrt_aexpr_rec k e_5 A)
  | (ae_app e1 e2) => ae_app (open_aexpr_wrt_aexpr_rec k e_5 e1) (open_aexpr_wrt_aexpr_rec k e_5 e2)
  | (ae_abs A ab) => ae_abs (open_aexpr_wrt_aexpr_rec k e_5 A) (open_abody_wrt_aexpr_rec (S k) e_5 ab)
  | (ae_pi A B) => ae_pi (open_aexpr_wrt_aexpr_rec k e_5 A) (open_aexpr_wrt_aexpr_rec (S k) e_5 B)
  | (ae_bind A ab) => ae_bind (open_aexpr_wrt_aexpr_rec k e_5 A) (open_abody_wrt_aexpr_rec (S k) e_5 ab)
  | (ae_all A B) => ae_all (open_aexpr_wrt_aexpr_rec k e_5 A) (open_aexpr_wrt_aexpr_rec (S k) e_5 B)
  | (ae_castup A e) => ae_castup (open_aexpr_wrt_aexpr_rec k e_5 A) (open_aexpr_wrt_aexpr_rec k e_5 e)
  | (ae_castdn e) => ae_castdn (open_aexpr_wrt_aexpr_rec k e_5 e)
end
with open_abody_wrt_aexpr_rec (k:nat) (e5:aexpr) (ab5:abody) : abody :=
  match ab5 with
  | (ab_anno e A) => ab_anno (open_aexpr_wrt_aexpr_rec k e5 e) (open_aexpr_wrt_aexpr_rec k e5 A)
end.

Definition open_binding_wrt_aexpr_rec (k:nat) (e5:aexpr) (b5:binding) : binding :=
  match b5 with
  | (b_var x A) => b_var x (open_aexpr_wrt_aexpr_rec k e5 A)
  | (b_ex ex A) => b_ex ex (open_aexpr_wrt_aexpr_rec k e5 A)
  | (b_kind kx) => b_kind kx
end.

Definition open_obind_wrt_aexpr_rec (k:nat) (e5:aexpr) (ob5:obind) : obind :=
  match ob5 with
  | ob_none => ob_none 
  | (ob_bind x A) => ob_bind x (open_aexpr_wrt_aexpr_rec k e5 A)
end.

Fixpoint open_worklist_wrt_aexpr_rec (k:nat) (e5:aexpr) (wl5:worklist) {struct wl5}: worklist :=
  match wl5 with
  | wl_nil => wl_nil 
  | (wl_cons wl w) => wl_cons (open_worklist_wrt_aexpr_rec k e5 wl) (open_work_wrt_aexpr_rec k e5 w)
  | (wl_bind wl b) => wl_bind (open_worklist_wrt_aexpr_rec k e5 wl) (open_binding_wrt_aexpr_rec k e5 b)
end
with open_work_wrt_aexpr_rec (k:nat) (e_5:aexpr) (w5:work) : work :=
  match w5 with
  | (w_check ob e1 e2 A) => w_check (open_obind_wrt_aexpr_rec k e_5 ob) (open_aexpr_wrt_aexpr_rec k e_5 e1) (open_aexpr_wrt_aexpr_rec k e_5 e2) (open_aexpr_wrt_aexpr_rec k e_5 A)
  | (w_infer e1 e2 wl) => w_infer (open_aexpr_wrt_aexpr_rec k e_5 e1) (open_aexpr_wrt_aexpr_rec k e_5 e2) (open_worklist_wrt_aexpr_rec (S k) e_5 wl)
  | (w_infer_app A e1 e2 wl) => w_infer_app (open_aexpr_wrt_aexpr_rec k e_5 A) (open_aexpr_wrt_aexpr_rec k e_5 e1) (open_aexpr_wrt_aexpr_rec k e_5 e2) (open_worklist_wrt_aexpr_rec (S k) e_5 wl)
  | (w_reduce e wl) => w_reduce (open_aexpr_wrt_aexpr_rec k e_5 e) (open_worklist_wrt_aexpr_rec (S k) e_5 wl)
  | (w_compact A B) => w_compact (open_aexpr_wrt_aexpr_rec k e_5 A) (open_aexpr_wrt_aexpr_rec k e_5 B)
end.

Definition open_aexpr_wrt_aexpr e_5 e__6 := open_aexpr_wrt_aexpr_rec 0 e__6 e_5.

Definition open_binding_wrt_aexpr e5 b5 := open_binding_wrt_aexpr_rec 0 b5 e5.

Definition open_worklist_wrt_aexpr e5 wl5 := open_worklist_wrt_aexpr_rec 0 wl5 e5.

Definition open_abody_wrt_aexpr e5 ab5 := open_abody_wrt_aexpr_rec 0 ab5 e5.

Definition open_work_wrt_aexpr e_5 w5 := open_work_wrt_aexpr_rec 0 w5 e_5.

Definition open_obind_wrt_aexpr e5 ob5 := open_obind_wrt_aexpr_rec 0 ob5 e5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_aexpr_abody *)
Inductive lc_aexpr : aexpr -> Prop :=    (* defn lc_aexpr *)
 | lc_ae_var_f : forall (x:aexprvar),
     (lc_aexpr (ae_var_f x))
 | lc_ae_kind : forall (k:akind),
     (lc_aexpr (ae_kind k))
 | lc_ae_ex : forall (ex:exvar),
     (lc_aexpr (ae_ex ex))
 | lc_ae_num : forall (n:number),
     (lc_aexpr (ae_num n))
 | lc_ae_int : 
     (lc_aexpr ae_int)
 | lc_ae_bot : forall (A:aexpr),
     (lc_aexpr A) ->
     (lc_aexpr (ae_bot A))
 | lc_ae_app : forall (e1 e2:aexpr),
     (lc_aexpr e1) ->
     (lc_aexpr e2) ->
     (lc_aexpr (ae_app e1 e2))
 | lc_ae_abs : forall (A:aexpr) (ab:abody),
     (lc_aexpr A) ->
      ( forall x , lc_abody  ( open_abody_wrt_aexpr ab (ae_var_f x) )  )  ->
     (lc_aexpr (ae_abs A ab))
 | lc_ae_pi : forall (A B:aexpr),
     (lc_aexpr A) ->
      ( forall x , lc_aexpr  ( open_aexpr_wrt_aexpr B (ae_var_f x) )  )  ->
     (lc_aexpr (ae_pi A B))
 | lc_ae_bind : forall (A:aexpr) (ab:abody),
     (lc_aexpr A) ->
      ( forall x , lc_abody  ( open_abody_wrt_aexpr ab (ae_var_f x) )  )  ->
     (lc_aexpr (ae_bind A ab))
 | lc_ae_all : forall (A B:aexpr),
     (lc_aexpr A) ->
      ( forall x , lc_aexpr  ( open_aexpr_wrt_aexpr B (ae_var_f x) )  )  ->
     (lc_aexpr (ae_all A B))
 | lc_ae_castup : forall (A e:aexpr),
     (lc_aexpr A) ->
     (lc_aexpr e) ->
     (lc_aexpr (ae_castup A e))
 | lc_ae_castdn : forall (e:aexpr),
     (lc_aexpr e) ->
     (lc_aexpr (ae_castdn e))
with lc_abody : abody -> Prop :=    (* defn lc_abody *)
 | lc_ab_anno : forall (e A:aexpr),
     (lc_aexpr e) ->
     (lc_aexpr A) ->
     (lc_abody (ab_anno e A)).

(* defns LC_obind *)
Inductive lc_obind : obind -> Prop :=    (* defn lc_obind *)
 | lc_ob_none : 
     (lc_obind ob_none)
 | lc_ob_bind : forall (x:aexprvar) (A:aexpr),
     (lc_aexpr A) ->
     (lc_obind (ob_bind x A)).

(* defns LC_binding *)
Inductive lc_binding : binding -> Prop :=    (* defn lc_binding *)
 | lc_b_var : forall (x:aexprvar) (A:aexpr),
     (lc_aexpr A) ->
     (lc_binding (b_var x A))
 | lc_b_ex : forall (ex:exvar) (A:aexpr),
     (lc_aexpr A) ->
     (lc_binding (b_ex ex A))
 | lc_b_kind : forall (kx:kindvar),
     (lc_binding (b_kind kx)).

(* defns LC_worklist_work *)
Inductive lc_worklist : worklist -> Prop :=    (* defn lc_worklist *)
 | lc_wl_nil : 
     (lc_worklist wl_nil)
 | lc_wl_cons : forall (wl:worklist) (w:work),
     (lc_worklist wl) ->
     (lc_work w) ->
     (lc_worklist (wl_cons wl w))
 | lc_wl_bind : forall (wl:worklist) (b:binding),
     (lc_worklist wl) ->
     (lc_binding b) ->
     (lc_worklist (wl_bind wl b))
with lc_work : work -> Prop :=    (* defn lc_work *)
 | lc_w_check : forall (ob:obind) (e1 e2 A:aexpr),
     (lc_obind ob) ->
     (lc_aexpr e1) ->
     (lc_aexpr e2) ->
     (lc_aexpr A) ->
     (lc_work (w_check ob e1 e2 A))
 | lc_w_infer : forall (e1 e2:aexpr) (wl:worklist),
     (lc_aexpr e1) ->
     (lc_aexpr e2) ->
      ( forall x , lc_worklist  ( open_worklist_wrt_aexpr wl (ae_var_f x) )  )  ->
     (lc_work (w_infer e1 e2 wl))
 | lc_w_infer_app : forall (A e1 e2:aexpr) (wl:worklist),
     (lc_aexpr A) ->
     (lc_aexpr e1) ->
     (lc_aexpr e2) ->
      ( forall x , lc_worklist  ( open_worklist_wrt_aexpr wl (ae_var_f x) )  )  ->
     (lc_work (w_infer_app A e1 e2 wl))
 | lc_w_reduce : forall (e:aexpr) (wl:worklist),
     (lc_aexpr e) ->
      ( forall x , lc_worklist  ( open_worklist_wrt_aexpr wl (ae_var_f x) )  )  ->
     (lc_work (w_reduce e wl))
 | lc_w_compact : forall (A B:aexpr),
     (lc_aexpr A) ->
     (lc_aexpr B) ->
     (lc_work (w_compact A B)).
(** free variables *)
Definition fkv_akind (k5:akind) : vars :=
  match k5 with
  | ak_star => {}
  | ak_box => {}
  | (ak_ex kx) => {{kx}}
end.

Fixpoint fex_aexpr (e_5:aexpr) : vars :=
  match e_5 with
  | (ae_var_b nat) => {}
  | (ae_var_f x) => {}
  | (ae_kind k) => {}
  | (ae_ex ex) => {{ex}}
  | (ae_num n) => {}
  | ae_int => {}
  | (ae_bot A) => (fex_aexpr A)
  | (ae_app e1 e2) => (fex_aexpr e1) \u (fex_aexpr e2)
  | (ae_abs A ab) => (fex_aexpr A) \u (fex_abody ab)
  | (ae_pi A B) => (fex_aexpr A) \u (fex_aexpr B)
  | (ae_bind A ab) => (fex_aexpr A) \u (fex_abody ab)
  | (ae_all A B) => (fex_aexpr A) \u (fex_aexpr B)
  | (ae_castup A e) => (fex_aexpr A) \u (fex_aexpr e)
  | (ae_castdn e) => (fex_aexpr e)
end
with fex_abody (ab5:abody) : vars :=
  match ab5 with
  | (ab_anno e A) => (fex_aexpr e) \u (fex_aexpr A)
end.

Fixpoint fv_aexpr (e_5:aexpr) : vars :=
  match e_5 with
  | (ae_var_b nat) => {}
  | (ae_var_f x) => {{x}}
  | (ae_kind k) => {}
  | (ae_ex ex) => {}
  | (ae_num n) => {}
  | ae_int => {}
  | (ae_bot A) => (fv_aexpr A)
  | (ae_app e1 e2) => (fv_aexpr e1) \u (fv_aexpr e2)
  | (ae_abs A ab) => (fv_aexpr A) \u (fv_abody ab)
  | (ae_pi A B) => (fv_aexpr A) \u (fv_aexpr B)
  | (ae_bind A ab) => (fv_aexpr A) \u (fv_abody ab)
  | (ae_all A B) => (fv_aexpr A) \u (fv_aexpr B)
  | (ae_castup A e) => (fv_aexpr A) \u (fv_aexpr e)
  | (ae_castdn e) => (fv_aexpr e)
end
with fv_abody (ab5:abody) : vars :=
  match ab5 with
  | (ab_anno e A) => (fv_aexpr e) \u (fv_aexpr A)
end.

Fixpoint fkv_aexpr (e_5:aexpr) : vars :=
  match e_5 with
  | (ae_var_b nat) => {}
  | (ae_var_f x) => {}
  | (ae_kind k) => (fkv_akind k)
  | (ae_ex ex) => {}
  | (ae_num n) => {}
  | ae_int => {}
  | (ae_bot A) => (fkv_aexpr A)
  | (ae_app e1 e2) => (fkv_aexpr e1) \u (fkv_aexpr e2)
  | (ae_abs A ab) => (fkv_aexpr A) \u (fkv_abody ab)
  | (ae_pi A B) => (fkv_aexpr A) \u (fkv_aexpr B)
  | (ae_bind A ab) => (fkv_aexpr A) \u (fkv_abody ab)
  | (ae_all A B) => (fkv_aexpr A) \u (fkv_aexpr B)
  | (ae_castup A e) => (fkv_aexpr A) \u (fkv_aexpr e)
  | (ae_castdn e) => (fkv_aexpr e)
end
with fkv_abody (ab5:abody) : vars :=
  match ab5 with
  | (ab_anno e A) => (fkv_aexpr e) \u (fkv_aexpr A)
end.

Definition fex_obind (ob5:obind) : vars :=
  match ob5 with
  | ob_none => {}
  | (ob_bind x A) => (fex_aexpr A)
end.

Definition fex_binding (b5:binding) : vars :=
  match b5 with
  | (b_var x A) => (fex_aexpr A)
  | (b_ex ex A) => (fex_aexpr A)
  | (b_kind kx) => {}
end.

Definition fv_binding (b5:binding) : vars :=
  match b5 with
  | (b_var x A) => (fv_aexpr A)
  | (b_ex ex A) => (fv_aexpr A)
  | (b_kind kx) => {}
end.

Definition fv_obind (ob5:obind) : vars :=
  match ob5 with
  | ob_none => {}
  | (ob_bind x A) => (fv_aexpr A)
end.

Definition fkv_obind (ob5:obind) : vars :=
  match ob5 with
  | ob_none => {}
  | (ob_bind x A) => (fkv_aexpr A)
end.

Definition fkv_binding (b5:binding) : vars :=
  match b5 with
  | (b_var x A) => (fkv_aexpr A)
  | (b_ex ex A) => (fkv_aexpr A)
  | (b_kind kx) => {}
end.

Fixpoint fex_worklist (wl5:worklist) : vars :=
  match wl5 with
  | wl_nil => {}
  | (wl_cons wl w) => (fex_worklist wl) \u (fex_work w)
  | (wl_bind wl b) => (fex_worklist wl) \u (fex_binding b)
end
with fex_work (w5:work) : vars :=
  match w5 with
  | (w_check ob e1 e2 A) => (fex_obind ob) \u (fex_aexpr e1) \u (fex_aexpr e2) \u (fex_aexpr A)
  | (w_infer e1 e2 wl) => (fex_aexpr e1) \u (fex_aexpr e2) \u (fex_worklist wl)
  | (w_infer_app A e1 e2 wl) => (fex_aexpr A) \u (fex_aexpr e1) \u (fex_aexpr e2) \u (fex_worklist wl)
  | (w_reduce e wl) => (fex_aexpr e) \u (fex_worklist wl)
  | (w_compact A B) => (fex_aexpr A) \u (fex_aexpr B)
end.

Fixpoint fv_worklist (wl5:worklist) : vars :=
  match wl5 with
  | wl_nil => {}
  | (wl_cons wl w) => (fv_worklist wl) \u (fv_work w)
  | (wl_bind wl b) => (fv_worklist wl) \u (fv_binding b)
end
with fv_work (w5:work) : vars :=
  match w5 with
  | (w_check ob e1 e2 A) => (fv_obind ob) \u (fv_aexpr e1) \u (fv_aexpr e2) \u (fv_aexpr A)
  | (w_infer e1 e2 wl) => (fv_aexpr e1) \u (fv_aexpr e2) \u (fv_worklist wl)
  | (w_infer_app A e1 e2 wl) => (fv_aexpr A) \u (fv_aexpr e1) \u (fv_aexpr e2) \u (fv_worklist wl)
  | (w_reduce e wl) => (fv_aexpr e) \u (fv_worklist wl)
  | (w_compact A B) => (fv_aexpr A) \u (fv_aexpr B)
end.

Fixpoint fkv_worklist (wl5:worklist) : vars :=
  match wl5 with
  | wl_nil => {}
  | (wl_cons wl w) => (fkv_worklist wl) \u (fkv_work w)
  | (wl_bind wl b) => (fkv_worklist wl) \u (fkv_binding b)
end
with fkv_work (w5:work) : vars :=
  match w5 with
  | (w_check ob e1 e2 A) => (fkv_obind ob) \u (fkv_aexpr e1) \u (fkv_aexpr e2) \u (fkv_aexpr A)
  | (w_infer e1 e2 wl) => (fkv_aexpr e1) \u (fkv_aexpr e2) \u (fkv_worklist wl)
  | (w_infer_app A e1 e2 wl) => (fkv_aexpr A) \u (fkv_aexpr e1) \u (fkv_aexpr e2) \u (fkv_worklist wl)
  | (w_reduce e wl) => (fkv_aexpr e) \u (fkv_worklist wl)
  | (w_compact A B) => (fkv_aexpr A) \u (fkv_aexpr B)
end.

(** substitutions *)
Definition k_subst_akind (k5:akind) (kx5:kindvar) (k_6:akind) : akind :=
  match k_6 with
  | ak_star => ak_star 
  | ak_box => ak_box 
  | (ak_ex kx) => (if eq_var kx kx5 then k5 else (ak_ex kx))
end.

Fixpoint ex_subst_aexpr (e_5:aexpr) (ex5:exvar) (e__6:aexpr) {struct e__6} : aexpr :=
  match e__6 with
  | (ae_var_b nat) => ae_var_b nat
  | (ae_var_f x) => ae_var_f x
  | (ae_kind k) => ae_kind k
  | (ae_ex ex) => (if eq_var ex ex5 then e_5 else (ae_ex ex))
  | (ae_num n) => ae_num n
  | ae_int => ae_int 
  | (ae_bot A) => ae_bot (ex_subst_aexpr e_5 ex5 A)
  | (ae_app e1 e2) => ae_app (ex_subst_aexpr e_5 ex5 e1) (ex_subst_aexpr e_5 ex5 e2)
  | (ae_abs A ab) => ae_abs (ex_subst_aexpr e_5 ex5 A) (ex_subst_abody e_5 ex5 ab)
  | (ae_pi A B) => ae_pi (ex_subst_aexpr e_5 ex5 A) (ex_subst_aexpr e_5 ex5 B)
  | (ae_bind A ab) => ae_bind (ex_subst_aexpr e_5 ex5 A) (ex_subst_abody e_5 ex5 ab)
  | (ae_all A B) => ae_all (ex_subst_aexpr e_5 ex5 A) (ex_subst_aexpr e_5 ex5 B)
  | (ae_castup A e) => ae_castup (ex_subst_aexpr e_5 ex5 A) (ex_subst_aexpr e_5 ex5 e)
  | (ae_castdn e) => ae_castdn (ex_subst_aexpr e_5 ex5 e)
end
with ex_subst_abody (e5:aexpr) (ex5:exvar) (ab5:abody) {struct ab5} : abody :=
  match ab5 with
  | (ab_anno e A) => ab_anno (ex_subst_aexpr e5 ex5 e) (ex_subst_aexpr e5 ex5 A)
end.

Fixpoint subst_aexpr (e_5:aexpr) (x5:aexprvar) (e__6:aexpr) {struct e__6} : aexpr :=
  match e__6 with
  | (ae_var_b nat) => ae_var_b nat
  | (ae_var_f x) => (if eq_var x x5 then e_5 else (ae_var_f x))
  | (ae_kind k) => ae_kind k
  | (ae_ex ex) => ae_ex ex
  | (ae_num n) => ae_num n
  | ae_int => ae_int 
  | (ae_bot A) => ae_bot (subst_aexpr e_5 x5 A)
  | (ae_app e1 e2) => ae_app (subst_aexpr e_5 x5 e1) (subst_aexpr e_5 x5 e2)
  | (ae_abs A ab) => ae_abs (subst_aexpr e_5 x5 A) (subst_abody e_5 x5 ab)
  | (ae_pi A B) => ae_pi (subst_aexpr e_5 x5 A) (subst_aexpr e_5 x5 B)
  | (ae_bind A ab) => ae_bind (subst_aexpr e_5 x5 A) (subst_abody e_5 x5 ab)
  | (ae_all A B) => ae_all (subst_aexpr e_5 x5 A) (subst_aexpr e_5 x5 B)
  | (ae_castup A e) => ae_castup (subst_aexpr e_5 x5 A) (subst_aexpr e_5 x5 e)
  | (ae_castdn e) => ae_castdn (subst_aexpr e_5 x5 e)
end
with subst_abody (e5:aexpr) (x5:aexprvar) (ab5:abody) {struct ab5} : abody :=
  match ab5 with
  | (ab_anno e A) => ab_anno (subst_aexpr e5 x5 e) (subst_aexpr e5 x5 A)
end.

Fixpoint k_subst_aexpr (k5:akind) (kx5:kindvar) (e_5:aexpr) {struct e_5} : aexpr :=
  match e_5 with
  | (ae_var_b nat) => ae_var_b nat
  | (ae_var_f x) => ae_var_f x
  | (ae_kind k) => ae_kind (k_subst_akind k5 kx5 k)
  | (ae_ex ex) => ae_ex ex
  | (ae_num n) => ae_num n
  | ae_int => ae_int 
  | (ae_bot A) => ae_bot (k_subst_aexpr k5 kx5 A)
  | (ae_app e1 e2) => ae_app (k_subst_aexpr k5 kx5 e1) (k_subst_aexpr k5 kx5 e2)
  | (ae_abs A ab) => ae_abs (k_subst_aexpr k5 kx5 A) (k_subst_abody k5 kx5 ab)
  | (ae_pi A B) => ae_pi (k_subst_aexpr k5 kx5 A) (k_subst_aexpr k5 kx5 B)
  | (ae_bind A ab) => ae_bind (k_subst_aexpr k5 kx5 A) (k_subst_abody k5 kx5 ab)
  | (ae_all A B) => ae_all (k_subst_aexpr k5 kx5 A) (k_subst_aexpr k5 kx5 B)
  | (ae_castup A e) => ae_castup (k_subst_aexpr k5 kx5 A) (k_subst_aexpr k5 kx5 e)
  | (ae_castdn e) => ae_castdn (k_subst_aexpr k5 kx5 e)
end
with k_subst_abody (k5:akind) (kx5:kindvar) (ab5:abody) {struct ab5} : abody :=
  match ab5 with
  | (ab_anno e A) => ab_anno (k_subst_aexpr k5 kx5 e) (k_subst_aexpr k5 kx5 A)
end.

Definition ex_subst_obind (e5:aexpr) (ex5:exvar) (ob5:obind) : obind :=
  match ob5 with
  | ob_none => ob_none 
  | (ob_bind x A) => ob_bind x (ex_subst_aexpr e5 ex5 A)
end.

Definition ex_subst_binding (e5:aexpr) (ex5:exvar) (b5:binding) : binding :=
  match b5 with
  | (b_var x A) => b_var x (ex_subst_aexpr e5 ex5 A)
  | (b_ex ex A) => b_ex ex (ex_subst_aexpr e5 ex5 A)
  | (b_kind kx) => b_kind kx
end.

Definition subst_binding (e5:aexpr) (x5:aexprvar) (b5:binding) : binding :=
  match b5 with
  | (b_var x A) => b_var x (subst_aexpr e5 x5 A)
  | (b_ex ex A) => b_ex ex (subst_aexpr e5 x5 A)
  | (b_kind kx) => b_kind kx
end.

Definition subst_obind (e5:aexpr) (x5:aexprvar) (ob5:obind) : obind :=
  match ob5 with
  | ob_none => ob_none 
  | (ob_bind x A) => ob_bind x (subst_aexpr e5 x5 A)
end.

Definition k_subst_obind (k5:akind) (kx5:kindvar) (ob5:obind) : obind :=
  match ob5 with
  | ob_none => ob_none 
  | (ob_bind x A) => ob_bind x (k_subst_aexpr k5 kx5 A)
end.

Definition k_subst_binding (k5:akind) (kx5:kindvar) (b5:binding) : binding :=
  match b5 with
  | (b_var x A) => b_var x (k_subst_aexpr k5 kx5 A)
  | (b_ex ex A) => b_ex ex (k_subst_aexpr k5 kx5 A)
  | (b_kind kx) => b_kind kx
end.

Fixpoint ex_subst_worklist (e5:aexpr) (ex5:exvar) (wl5:worklist) {struct wl5} : worklist :=
  match wl5 with
  | wl_nil => wl_nil 
  | (wl_cons wl w) => wl_cons (ex_subst_worklist e5 ex5 wl) (ex_subst_work e5 ex5 w)
  | (wl_bind wl b) => wl_bind (ex_subst_worklist e5 ex5 wl) (ex_subst_binding e5 ex5 b)
end
with ex_subst_work (e_5:aexpr) (ex5:exvar) (w5:work) {struct w5} : work :=
  match w5 with
  | (w_check ob e1 e2 A) => w_check (ex_subst_obind e_5 ex5 ob) (ex_subst_aexpr e_5 ex5 e1) (ex_subst_aexpr e_5 ex5 e2) (ex_subst_aexpr e_5 ex5 A)
  | (w_infer e1 e2 wl) => w_infer (ex_subst_aexpr e_5 ex5 e1) (ex_subst_aexpr e_5 ex5 e2) (ex_subst_worklist e_5 ex5 wl)
  | (w_infer_app A e1 e2 wl) => w_infer_app (ex_subst_aexpr e_5 ex5 A) (ex_subst_aexpr e_5 ex5 e1) (ex_subst_aexpr e_5 ex5 e2) (ex_subst_worklist e_5 ex5 wl)
  | (w_reduce e wl) => w_reduce (ex_subst_aexpr e_5 ex5 e) (ex_subst_worklist e_5 ex5 wl)
  | (w_compact A B) => w_compact (ex_subst_aexpr e_5 ex5 A) (ex_subst_aexpr e_5 ex5 B)
end.

Fixpoint subst_worklist (e5:aexpr) (x5:aexprvar) (wl5:worklist) {struct wl5} : worklist :=
  match wl5 with
  | wl_nil => wl_nil 
  | (wl_cons wl w) => wl_cons (subst_worklist e5 x5 wl) (subst_work e5 x5 w)
  | (wl_bind wl b) => wl_bind (subst_worklist e5 x5 wl) (subst_binding e5 x5 b)
end
with subst_work (e_5:aexpr) (x5:aexprvar) (w5:work) {struct w5} : work :=
  match w5 with
  | (w_check ob e1 e2 A) => w_check (subst_obind e_5 x5 ob) (subst_aexpr e_5 x5 e1) (subst_aexpr e_5 x5 e2) (subst_aexpr e_5 x5 A)
  | (w_infer e1 e2 wl) => w_infer (subst_aexpr e_5 x5 e1) (subst_aexpr e_5 x5 e2) (subst_worklist e_5 x5 wl)
  | (w_infer_app A e1 e2 wl) => w_infer_app (subst_aexpr e_5 x5 A) (subst_aexpr e_5 x5 e1) (subst_aexpr e_5 x5 e2) (subst_worklist e_5 x5 wl)
  | (w_reduce e wl) => w_reduce (subst_aexpr e_5 x5 e) (subst_worklist e_5 x5 wl)
  | (w_compact A B) => w_compact (subst_aexpr e_5 x5 A) (subst_aexpr e_5 x5 B)
end.

Fixpoint k_subst_worklist (k5:akind) (kx5:kindvar) (wl5:worklist) {struct wl5} : worklist :=
  match wl5 with
  | wl_nil => wl_nil 
  | (wl_cons wl w) => wl_cons (k_subst_worklist k5 kx5 wl) (k_subst_work k5 kx5 w)
  | (wl_bind wl b) => wl_bind (k_subst_worklist k5 kx5 wl) (k_subst_binding k5 kx5 b)
end
with k_subst_work (k5:akind) (kx5:kindvar) (w5:work) {struct w5} : work :=
  match w5 with
  | (w_check ob e1 e2 A) => w_check (k_subst_obind k5 kx5 ob) (k_subst_aexpr k5 kx5 e1) (k_subst_aexpr k5 kx5 e2) (k_subst_aexpr k5 kx5 A)
  | (w_infer e1 e2 wl) => w_infer (k_subst_aexpr k5 kx5 e1) (k_subst_aexpr k5 kx5 e2) (k_subst_worklist k5 kx5 wl)
  | (w_infer_app A e1 e2 wl) => w_infer_app (k_subst_aexpr k5 kx5 A) (k_subst_aexpr k5 kx5 e1) (k_subst_aexpr k5 kx5 e2) (k_subst_worklist k5 kx5 wl)
  | (w_reduce e wl) => w_reduce (k_subst_aexpr k5 kx5 e) (k_subst_worklist k5 kx5 wl)
  | (w_compact A B) => w_compact (k_subst_aexpr k5 kx5 A) (k_subst_aexpr k5 kx5 B)
end.


(** definitions *)

(* defns InWorklist *)
Inductive in_wl : binding -> worklist -> Prop :=    (* defn in_wl *)
 | iwl_here : forall (b:binding) (wl:worklist),
     lc_worklist wl ->
     lc_binding b ->
     in_wl b (wl_bind wl b)
 | iwl_there_w : forall (b:binding) (wl:worklist) (w:work),
     lc_work w ->
     in_wl b wl ->
     in_wl b (wl_cons wl w)
 | iwl_there_b : forall (b1:binding) (wl:worklist) (b2:binding),
     lc_binding b2 ->
     in_wl b1 wl ->
     in_wl b1 (wl_bind wl b2).

(* defns InScope *)
Inductive in_scope : worklist -> binding -> binding -> Prop :=    (* defn in_scope *)
 | ins_here : forall (wl:worklist) (b2 b1:binding),
     lc_binding b2 ->
     in_wl b1 wl ->
     in_scope (wl_bind wl b2) b1 b2
 | ins_there_w : forall (wl:worklist) (w:work) (b1 b2:binding),
     lc_work w ->
     in_scope wl b1 b2 ->
     in_scope (wl_cons wl w) b1 b2
 | ins_there_b : forall (wl:worklist) (b b1 b2:binding),
     lc_binding b ->
     in_scope wl b1 b2 ->
     in_scope (wl_bind wl b) b1 b2.

(* defns Monotype *)
Inductive mono_atype : aexpr -> Prop :=    (* defn mono_atype *)
 | amono_kind : forall (k:akind),
     mono_atype (ae_kind k)
 | amono_ex : forall (ex:exvar),
     mono_atype (ae_ex ex)
 | amono_var : forall (x:aexprvar),
     mono_atype (ae_var_f x)
 | amono_int : 
     mono_atype ae_int
 | amono_lit : forall (n:number),
     mono_atype (ae_num n)
 | amono_bot : forall (A:aexpr),
     lc_aexpr A ->
     mono_atype (ae_bot A)
 | amono_app : forall (e1 e2:aexpr),
     mono_atype e1 ->
     mono_atype e2 ->
     mono_atype  ( (ae_app e1 e2) ) 
 | amono_pi : forall (L:vars) (A B:aexpr),
     mono_atype A ->
      ( forall x , x \notin  L  -> mono_atype  ( open_aexpr_wrt_aexpr B (ae_var_f x) )  )  ->
     mono_atype (ae_pi A B)
 | amono_lambda : forall (L:vars) (A e B:aexpr),
     lc_aexpr A ->
     lc_aexpr (ae_abs A (ab_anno e B)) ->
      ( forall x , x \notin  L  -> mono_atype  ( open_aexpr_wrt_aexpr e (ae_var_f x) )  )  ->
     mono_atype (ae_abs A (ab_anno e B))
 | amono_bind : forall (L:vars) (A e B:aexpr),
     lc_aexpr A ->
     lc_aexpr (ae_bind A (ab_anno e B)) ->
      ( forall x , x \notin  L  -> mono_atype  ( open_aexpr_wrt_aexpr e (ae_var_f x) )  )  ->
     mono_atype (ae_bind A (ab_anno e B))
 | amono_castup : forall (A e:aexpr),
     lc_aexpr A ->
     mono_atype e ->
     mono_atype (ae_castup A e)
 | amono_castdn : forall (e:aexpr),
     mono_atype e ->
     mono_atype (ae_castdn e).

(* defns Reduce *)
Inductive areduce : aexpr -> aexpr -> Prop :=    (* defn areduce *)
 | ar_app : forall (e1 e3 e2:aexpr),
     lc_aexpr e3 ->
     areduce e1 e2 ->
     areduce (ae_app e1 e3) (ae_app e2 e3)
 | ar_beta : forall (A e1 B e2:aexpr),
     lc_aexpr A ->
     lc_aexpr (ae_abs A (ab_anno e1 B)) ->
     lc_aexpr (ae_abs A (ab_anno e1 B)) ->
     lc_aexpr e2 ->
     areduce (ae_app  ( (ae_abs A (ab_anno e1 B)) )  e2)  (open_aexpr_wrt_aexpr  e1   e2 ) 
 | ar_inst : forall (A e1 B e2 e:aexpr),
     lc_aexpr A ->
     lc_aexpr (ae_bind A (ab_anno e1 B)) ->
     lc_aexpr (ae_bind A (ab_anno e1 B)) ->
     lc_aexpr e2 ->
     mono_atype e ->
     areduce (ae_app  ( (ae_bind A (ab_anno e1 B)) )  e2) (ae_app  (  (open_aexpr_wrt_aexpr  e1   e )  )  e2)
 | ar_castdn : forall (e1 e2:aexpr),
     areduce e1 e2 ->
     areduce (ae_castdn e1) (ae_castdn e2)
 | ar_cast_inst : forall (A e1 B e:aexpr),
     lc_aexpr A ->
     lc_aexpr (ae_bind A (ab_anno e1 B)) ->
     lc_aexpr (ae_bind A (ab_anno e1 B)) ->
     mono_atype e ->
     areduce (ae_castdn  ( (ae_bind A (ab_anno e1 B)) ) ) (ae_castdn  (  (open_aexpr_wrt_aexpr  e1   e )  ) )
 | ar_cast_elim : forall (B e:aexpr),
     lc_aexpr B ->
     lc_aexpr e ->
     areduce (ae_castdn  ( (ae_castup B e) ) ) e.


(** infrastructure *)
Hint Constructors in_wl in_scope mono_atype areduce lc_aexpr lc_abody lc_obind lc_binding lc_worklist lc_work : core.


