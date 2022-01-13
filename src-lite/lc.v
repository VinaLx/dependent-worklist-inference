Require Import bidir_notations.

Lemma mono_lc_bexpr : forall e, mono_btype e → lc_bexpr e.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve mono_lc_bexpr : lc.
