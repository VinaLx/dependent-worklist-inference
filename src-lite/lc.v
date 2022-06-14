Require Import bidir.notations.
Require Import Utf8.

Lemma mono_lc_bexpr : forall e, mono_btype e → lc_bexpr e.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve mono_lc_bexpr : lc.
