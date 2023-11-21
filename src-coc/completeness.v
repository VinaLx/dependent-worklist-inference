Require Import alg.worklist.
Require Import decl.worklist.
Require Import transfer.

Require Import Equality.

Theorem completeness : forall Γ,
    ⪧₂ Γ → forall Γ' Θ, nil ⊢ Γ' ⟿₂ Γ ⊣ Θ → ⪧′ Γ'.
Proof.
  induction 1; intros Γ_ Θ Trans.
  - dependent induction Trans.
    (* all solveable *)
    + admit.
    + admit.
    + admit.
  - dependent induction Trans.
      (* main case infer *)
    + admit.
    + admit.
    + admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
