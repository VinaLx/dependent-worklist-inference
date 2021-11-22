Require Import worklist.
Require Import decl_worklist.
Require Import wl_transfer.

(*
Theorem wl_sound : forall Γ',
    ⪧′ Γ' → exists Γ, Γ' ⟿ Γ ∧ ⪧ Γ.
Proof.
  intros * H.
  induction H; intros.
  (* nil *)
  - eauto.
  (* var *)
  - admit.
  (* num *)
  - admit.
Admitted.
*)
