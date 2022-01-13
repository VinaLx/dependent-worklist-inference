Require Export Lists.List.
Require Import Utf8.

Import ListNotations.

Lemma app_r_cons : forall {A} {a : A} xs ys,
    xs ++ a :: ys = (xs ++ [a]) ++ ys.
Proof.
  intros. now rewrite <- app_assoc.
Qed.

Lemma app_inj_l : forall A (xs ys zs : list A),
    ys ++ xs = zs ++ xs → ys = zs.
Proof.
  induction xs; intros.
  - now repeat rewrite app_nil_r in H.
  - rewrite (app_r_cons ys xs) in H.
    rewrite (app_r_cons zs xs) in H.
    apply IHxs in H.
    now apply app_inj_tail_iff in H as (? & ?).
Qed.

Lemma app_nil_invert : forall A (xs ys : list A),
    xs = ys ++ xs -> ys = [].
Proof.
  intros.
  replace xs with (nil ++ xs) in H at 1.
  - now apply app_inj_l in H.
  - auto.
Qed.
