Require Import decl.properties.
Require Import decl.ln_inf.
Require Import Program.Tactics.
Require Import bidir.notations.
Require Import bidir.properties.
Require Import Lia.

Set Printing Parentheses.

Fixpoint to_bexpr (e : expr) : bexpr :=
  match e with
  | e_var_f x => be_var_f x
  | e_var_b x => be_var_b x
  | e_kind k_star => be_kind bk_star
  | e_kind k_box => be_kind bk_box
  | e_num n => be_num n
  | e_int => be_int
  | e_bot A => be_anno be_bot (to_bexpr A)
  | e_app f a => be_app (to_bexpr f) (to_bexpr a)
  | e_abs  A (b_anno e B) => be_anno (be_abs  (to_bexpr e)) (be_pi  (to_bexpr A) (to_bexpr B))
  | e_bind A (b_anno e B) => be_anno (be_bind (to_bexpr e)) (be_all (to_bexpr A) (to_bexpr B))
  | e_pi  A B => be_pi  (to_bexpr A) (to_bexpr B)
  | e_all A B => be_all (to_bexpr A) (to_bexpr B)
  | e_castup A e => be_anno (be_castup (to_bexpr e)) (to_bexpr A)
  | e_castdn e => be_castdn (to_bexpr e)
  end
.

Fixpoint to_bcontext (Γ : context) : bcontext :=
  match Γ with
  | ctx_nil => bctx_nil
  | ctx_cons Γ' x A => bctx_cons (to_bcontext Γ') x (to_bexpr A)
  end
.
  
Lemma size_expr_lt_size_body : forall n e A,
    size_body (b_anno e A) < S n -> size_expr e < n /\ size_expr A < n.
Proof.
  intros. unfold size_body in H. fold size_expr in H. lia.
Qed.


Ltac eq_swap_open_bexpr_with_to_bexpr IHn x:=
  match goal with
  | [ _ : _ |- eq (_ (open_bexpr_wrt_bexpr_rec ?n0 _(to_bexpr ?A))) ?Q ] 
      => rewrite (IHn A n0 x); auto; lia
  | [ _ : _ |- eq (_ (open_bexpr_wrt_bexpr_rec ?n0 _ (to_bexpr ?A1)) (open_bexpr_wrt_bexpr_rec ?n1 _ (to_bexpr ?A2))) _ ] 
      => rewrite (IHn A1 n0 x); try rewrite (IHn A2 n1 x); auto; lia
  | [ _ : _ |- eq (_ (_ (open_bexpr_wrt_bexpr_rec ?n0 _ (to_bexpr ?A1))) (open_bexpr_wrt_bexpr_rec ?n1 _ (to_bexpr ?A2))) _ ] 
      => rewrite (IHn A1 n0 x); try rewrite (IHn A2 n1 x); auto; lia
  end.

Lemma open_bexpr_wrt_bexpr_rec_exchanges_to_bexpr : forall n A n0 t,
  size_expr A < n -> 
  open_bexpr_wrt_bexpr_rec n0 (to_bexpr t) (to_bexpr A) = to_bexpr (open_expr_wrt_expr_rec n0 t A).
Proof.
  intro n. induction n.
  - intros. inversion H.
  - intro A. induction A; intros; auto; simpl in *;try (eq_swap_open_bexpr_with_to_bexpr IHn t).
    + destruct (lt_eq_lt_dec n0 n1).
      * destruct s; auto; lia.
      * auto.
    + destruct k; auto.
    + destruct b. simpl.
      assert (size_body (b_anno e A0) < S n). { lia. } specialize (size_expr_lt_size_body n e A0 H0). intro.
      rewrite (IHA n0 t). rewrite (IHn e (S n0) t). rewrite (IHn A0 (S n0) t).
      auto. all : lia.
    + destruct b. simpl.
      assert (size_body (b_anno e A0) < S n). { lia. } specialize (size_expr_lt_size_body n e A0 H0). intro.
      rewrite (IHA n0 t). rewrite (IHn e (S n0) t). rewrite (IHn A0 (S n0) t).
      auto. all : lia.
Qed.


Lemma open_bexpr_wrt_bexpr_rec_exchanges_to_bexpr_var : forall n A n0 x,
    size_expr A < n -> 
    open_bexpr_wrt_bexpr_rec n0 `' x (to_bexpr A) = to_bexpr (open_expr_wrt_expr_rec n0 ` x A).
Proof.
  intros.
  replace (`' x) with (to_bexpr (` x)) by auto.
  eapply open_bexpr_wrt_bexpr_rec_exchanges_to_bexpr; auto.
Qed.


Ltac swap_open_expr_wrt_bexpr_rec_with_to_bexpr :=
  match goal with 
  | _ : _ |- lc_bexpr (open_bexpr_wrt_bexpr_rec 1 `' ?x (to_bexpr ?A) ^`' _) => 
    rewrite (open_bexpr_wrt_bexpr_rec_exchanges_to_bexpr_var (S (size_expr A)) A 1 x); auto; lia
  end.
      

Theorem lc_tobexpr : forall A x,
    lc_bexpr (to_bexpr (A ^` x))
  -> lc_bexpr (to_bexpr A ^`' x).
Proof.
  intros. dependent induction A; auto.
  - destruct n.
    + constructor.
    + simpl in *. unfold open_bexpr_wrt_bexpr. simpl. auto.
  - destruct k; constructor.
  - inversion H. constructor; eauto.
  - inversion H. constructor; eauto. 
  - unfold to_bexpr. destruct b.
    constructor; fold open_bexpr_wrt_bexpr_rec; fold to_bexpr.
    + inversion H. inversion H2. constructor. intro. swap_open_expr_wrt_bexpr_rec_with_to_bexpr.
    + inversion H. inversion H3. constructor.
      * apply IHA. assumption.
      * intros. swap_open_expr_wrt_bexpr_rec_with_to_bexpr.
  - inversion H. constructor; fold open_bexpr_wrt_bexpr_rec; fold to_bexpr.
    + apply IHA1. auto.
    + intros. specialize (H3 x0). swap_open_expr_wrt_bexpr_rec_with_to_bexpr.
  - unfold to_bexpr. destruct b. inversion H. constructor; fold open_bexpr_wrt_bexpr_rec; fold to_bexpr.
    + constructor. intro. inversion H2. swap_open_expr_wrt_bexpr_rec_with_to_bexpr.
    + constructor; inversion H3. eauto.
      intro. swap_open_expr_wrt_bexpr_rec_with_to_bexpr.
  - inversion H. constructor; fold open_bexpr_wrt_bexpr_rec; fold to_bexpr.
    + apply IHA1. assumption. 
    + intro. swap_open_expr_wrt_bexpr_rec_with_to_bexpr.
  - inversion H; constructor.
    + inversion H2. constructor. apply IHA2. auto.
    + eauto.
  - inversion H; constructor; eauto.
Qed.

Ltac solve_lc_bexpr_with_to_bexpr_and_open := 
  match goal with 
  | H : forall x, ?P -> ?Q -> lc_bexpr (to_bexpr x) |- lc_bexpr (to_bexpr ?A ^`' ?x) =>
        apply lc_tobexpr; eapply H; try (unfold open_expr_wrt_expr; rewrite (size_expr_open_expr_wrt_expr_rec_var A x 0); lia); try auto
  end.

Scheme Induction for lc_expr Sort Prop
  with Induction for lc_body Sort Prop.

Theorem to_bexpr_keeps_lc : forall A,lc_expr A -> lc_bexpr (to_bexpr A).
Proof.
  intros A.
  apply lc_expr_ind_dep with
  (P := fun e (_ : lc_expr e) => lc_bexpr (to_bexpr e))
  (P0 := fun b  (_ : lc_body b) => match b with (b_anno e A)  => lc_bexpr (to_bexpr e) /\ lc_bexpr (to_bexpr A) end); intros; try (simpl; auto).
  - destruct k; auto.
  - destruct b. constructor.
    + constructor. intro. specialize (H0 x). simpl in H0. inversion H0. apply lc_tobexpr. auto.
    + constructor. auto. intro. specialize (H0 x). simpl in H0. inversion H0. apply lc_tobexpr. auto.
  - constructor.
    + auto. 
    + intros. specialize (H0 x). apply lc_tobexpr. auto.
  - destruct b. constructor.
    + constructor. intro. specialize (H0 x). simpl in H0. inversion H0. apply lc_tobexpr. auto.
    + constructor.
      * auto.
      * intros. specialize (H0 x). simpl in H0. inversion H0. apply lc_tobexpr. auto.
  - constructor. 
    + auto.
    + intros. specialize (H0 x). apply lc_tobexpr. auto.
Qed. 


Theorem to_bcontext_keeps_lc : forall Γ, lc_context Γ -> lc_bcontext (to_bcontext Γ).
Proof.
  intros.
  induction Γ.
  - auto.
  - simpl. constructor; inversion H; subst.
    + apply IHΓ. auto.
    + eapply to_bexpr_keeps_lc; auto.
Qed.


Theorem to_bcontext_keeps_notin : forall x G, 
  x `notin` ctx_dom G
  -> x `notin` bctx_dom (to_bcontext G).
Proof.
  intros. induction G.
  - auto.
  - simpl in *.
    eapply notin_add_3.
    + eapply notin_add_1'. eauto.
    + eapply notin_add_2. eauto.
Qed.

Ltac rewrite_to_expr A x := 
  unfold open_bexpr_wrt_bexpr; 
  rewrite (open_bexpr_wrt_bexpr_rec_exchanges_to_bexpr_var (S (size_expr A)) A 0 x (le_lt_n_Sm (size_expr A) (size_expr A) (le_n (size_expr A)))); 
  fold open_expr_wrt_expr_rec.

Scheme Induction for expr Sort Prop
  with Induction for body Sort Prop.

Theorem to_bexpr_keeps_mono_type: forall t,
  mono_type t -> mono_btype (to_bexpr t).
Proof.
  intros. 
  dependent induction H; try constructor; auto.
  - destruct k; constructor.
  - fold to_bexpr. apply to_bexpr_keeps_lc. auto.
  - simpl. econstructor; auto. intros.
    specialize (H1 x H2). rewrite_to_expr B x. auto.
  - constructor. apply to_bexpr_keeps_lc. auto.
    intros. fold to_bexpr. inversion H0.
    specialize (H6 x). inversion H6. auto. 
    apply lc_tobexpr.
    apply to_bexpr_keeps_lc. auto.
  - fold to_bexpr.
    econstructor. intros.
    rewrite_to_expr e x. apply H2. auto.
  - constructor. apply to_bexpr_keeps_lc. auto.
    inversion H0.
    intro. specialize (H6 x).
    inversion H6. apply lc_tobexpr. apply to_bexpr_keeps_lc.  
    auto.
  - econstructor.
    intros. fold to_bexpr. rewrite_to_expr e x. apply H2. auto.
  - apply to_bexpr_keeps_lc. auto.
Qed.


Theorem to_bexpr_keeps_fv : forall e,
  ott.fv_eexpr (erase e) = ott.fv_eexpr (berase (to_bexpr e)).
Proof.
  intros.
  pattern e.
  apply expr_ind with 
  (P0 := fun b => match b with (b_anno e A)  =>  
    ott.fv_eexpr (erase e) = ott.fv_eexpr (berase (to_bexpr e)) /\ 
    ott.fv_eexpr (erase A) = ott.fv_eexpr (berase (to_bexpr A))  
    end); intros; auto.
  - destruct k; auto.
  - simpl. rewrite <- H. rewrite <- H0. auto.
  - destruct b. simpl. inversion H0. auto. 
  - simpl. rewrite <- H. rewrite <- H0. auto.
  - destruct b. simpl. inversion H0. auto.
  - simpl. rewrite <- H. rewrite <- H0. auto.
Qed.

Theorem to_bexpr_keeps_reduce : forall A B, 
   A ⟶ B -> breduce (to_bexpr A) (to_bexpr B).
Proof. (* *** *)
  intros.
  induction H.
  - constructor; fold to_bexpr.
    + apply to_bexpr_keeps_lc. auto.
    + auto.
  (* - replace (to_bexpr (e1 ^^ e2)) with ((to_bexpr e1) ^^' (to_bexpr e2)) by admit. eapply br_beta; fold to_bexpr; inversion H0.
    + constructor. intro. specialize (H6 x). inversion H6. admit.
    + apply to_bexpr_keeps_lc. auto.
    + constructor. apply to_bexpr_keeps_lc. auto. intro. specialize (H6 x). inversion H6. admit.
    + apply to_bexpr_keeps_lc. auto. *)
  (* - simpl.
    + apply to_bexpr_keeps_lc. auto.
    + admit. *)
  - admit.
  - admit.
  - constructor. fold to_bexpr. auto.
  - simpl. constructor. admit. 
  - constructor; fold to_bexpr; apply to_bexpr_keeps_lc; auto.
Admitted.
