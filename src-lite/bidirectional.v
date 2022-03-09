Require Import decl.properties.
Require Import decl.ln_inf.
Require Import Program.Tactics.
Require Import bidir.notations.
Require Import bidir.properties.
Require Import bidir.elaboration.

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

Definition to_bk (k : kind) : bkind :=
  match k with
  | k_star => bk_star
  | k_box => bk_box
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


Lemma open_bexpr_wrt_bexpr_rec_exchanges_to_bexpr : forall n A n0 x,
    size_expr A < n -> 
    open_bexpr_wrt_bexpr_rec n0 `' x (to_bexpr A) = to_bexpr (open_expr_wrt_expr_rec n0 ` x A).
Proof.
  intro n. induction n.
  - intros. inversion H.
  - intro A. induction A; intros; auto; simpl in *;try (eq_swap_open_bexpr_with_to_bexpr IHn x).
    + destruct (lt_eq_lt_dec n0 n1).
      * destruct s; auto; lia.
      * auto.
    + destruct k; auto.
    + destruct b. simpl.
      assert (size_body (b_anno e A0) < S n). { lia. } specialize (size_expr_lt_size_body n e A0 H0). intro.
      rewrite (IHA n0 x). rewrite (IHn e (S n0) x). rewrite (IHn A0 (S n0) x).
      auto. all : lia.
    + destruct b. simpl.
      assert (size_body (b_anno e A0) < S n). { lia. } specialize (size_expr_lt_size_body n e A0 H0). intro.
      rewrite (IHA n0 x). rewrite (IHn e (S n0) x). rewrite (IHn A0 (S n0) x).
      auto. all : lia.
Qed.

Ltac swap_open_expr_wrt_bexpr_rec_with_to_bexpr :=
  match goal with 
  | _ : _ |- lc_bexpr (open_bexpr_wrt_bexpr_rec 1 `' ?x (to_bexpr ?A) ^`' _) => 
    rewrite (open_bexpr_wrt_bexpr_rec_exchanges_to_bexpr (S (size_expr A)) A 1 x); auto; lia
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
  match goal with 
  | [ _ : _ |- _ ] 
  => unfold open_bexpr_wrt_bexpr; rewrite (open_bexpr_wrt_bexpr_rec_exchanges_to_bexpr (S (size_expr A)) A 0 x (le_lt_n_Sm (size_expr A) (size_expr A) (le_n (size_expr A)))); fold open_expr_wrt_expr_rec
 end.

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


Theorem bidir_complete : forall Γ e1 e2 A
  , Γ ⊢ e1 <: e2 : A
  -> to_bcontext Γ ⊢ to_bexpr e1 <: to_bexpr e2 ⇒ to_bexpr A.
Proof.
  intros. pattern Γ, e1, e2, A, H.
  apply usub_mut with
    (P0 := fun Γ (_ : ⊢ Γ) => bwf_context (to_bcontext Γ)); intros.
(* busub *)
  (* var *)
  - constructor; auto. induction i; simpl in *.
    + apply inb_here. apply to_bcontext_keeps_lc. auto. eapply to_bexpr_keeps_lc; auto.
    + apply inb_there. eapply to_bexpr_keeps_lc; eauto. 
      eapply IHi. inversion w. auto. inversion H0. auto. 
  (* num *)
  - constructor. auto.
  (* star *)
  - constructor. auto.
   (* int  *)
  - constructor. auto.
  (* bot *)
  - simpl. destruct k; econstructor; eauto.
    + eapply bs_bot. apply bidir_refl_l in H0. eauto.
    + eapply bs_bot. apply bidir_refl_l in H0. eauto.
  (* abs *)
  - simpl. econstructor.
    + eapply bs_abs with (k1:= to_bk k1) (k2:= to_bk k2) (L:=L).
      * apply bidir_refl_l in H0. destruct k1; simpl in *; eauto.
      * intros. specialize (H2 x H5). apply bidir_refl_l in H2. 
        rewrite_to_expr B1 x. destruct k2; simpl in *; auto.
      * intros. eapply bs_sub with (A:=(to_bexpr (B1 ^` x))) (k:=to_bk k2).
        -- rewrite_to_expr e0 x. rewrite_to_expr e3 x. auto.
           specialize (H4 x H5). simpl in H4. auto.
        -- specialize (H2 x H5). apply bidir_refl_l in H2.
          rewrite_to_expr B1 x. simpl in H2. destruct k2; auto.
    + eapply bs_pi_inf with (k1:=to_bk k1) (k2:=to_bk k2) (L:=L).
      * eapply bidir_refl_l in H0. destruct k1; simpl in *; eauto.
      * destruct k1; eauto.
      * intros. specialize (H2 x H5). apply bidir_refl_l in H2. 
        rewrite_to_expr B1 x. simpl in H2. destruct k2; auto.  
      * intros. specialize (H2 x H5). simpl in H2.
        replace ((to_bcontext G),' x : (to_bexpr A1)) with ((to_bcontext G),' x : (to_bexpr A1),,'bctx_nil) in H2.
        eapply bidir_narrowing with (A:=to_bexpr A2) (k:=to_bk k1) in H2.
        -- rewrite_to_expr B1 x. rewrite_to_expr B2 x. destruct k2; auto.
        -- destruct k1; auto.
        -- auto.
    + eapply bs_pi_inf with (k1:=to_bk k1) (k2:=to_bk k2) (L:=L).
      * eapply bidir_refl_l in H1. destruct k1; simpl in *; eauto.
      * destruct k1; eauto.
      * intros. specialize (H3 x H5). simpl in H3.
        replace ((to_bcontext G),' x : (to_bexpr A1)) with ((to_bcontext G),' x : (to_bexpr A1),,'bctx_nil) in H3.
        eapply bidir_narrowing with (A:=to_bexpr A2) (k:=to_bk k1) in H3. simpl in H3.
        -- apply bidir_refl_l in H3. rewrite_to_expr B2 x. destruct k2; auto. 
        -- destruct k1; auto.
        -- auto.
      * intros. specialize (H3 x H5). 
        simpl in H3. rewrite_to_expr B1 x. rewrite_to_expr B2 x. destruct k2; auto.
  (* pi *)
  - replace (to_bexpr (e_pi A1 B1)) with (be_pi (to_bexpr A1) (to_bexpr B1)) by auto. 
    replace (to_bexpr (e_pi A2 B2)) with (be_pi (to_bexpr A2) (to_bexpr B2)) by auto.
    replace (to_bexpr ⧼ k2 ⧽) with (⧼ to_bk k2 ⧽') by (destruct k2; auto). 
    eapply bs_pi_inf with (k1:=to_bk k1) (L:=L).
    + destruct k1; auto.
    + destruct k1; auto.
    + intros. specialize (H2 x H4). rewrite_to_expr B1 x.
      destruct k2; auto.
    + intros. specialize (H3 x H4). rewrite_to_expr B1 x. rewrite_to_expr B2 x.
      destruct k2; auto.
  - econstructor; fold to_bexpr.
    + apply to_bexpr_keeps_mono_type. auto.
    + eauto.
    + simpl. replace (to_bexpr (B ^^ t)) with ((to_bexpr) B ^^' (to_bexpr t)).  econstructor.
    * admit.  (* *** *)
    * eapply bs_sub. eauto. admit. (* ** *)
    * admit. (* * *)
  - econstructor; fold to_bexpr.
    + eapply bs_bind with (k:=to_bk k) (L:=L); fold to_bexpr.
      * apply bidir_refl_l in H0. destruct k; auto.
      * intros. specialize (H2 x H5). apply bidir_refl_l in H2. simpl in H2.
        rewrite_to_expr B1 x. auto.
      * intros. specialize (H4 x H5). simpl in H4.
        eapply bs_sub with (k:=bk_star).
        rewrite_to_expr e0 x. rewrite_to_expr e3 x. eauto.
        rewrite_to_expr B1 x. 
        specialize (H2 x H5). apply bidir_refl_l in H2. simpl in H2. auto.
      * admit. (* * *)
      * admit. (* * *)
    + eapply bs_forall with (k:=to_bk k); fold to_bexpr.
      * destruct k; eauto.
      * destruct k; eauto.
      * intros. specialize (H2 x H5). simpl in H2.
        rewrite_to_expr B1 x. rewrite_to_expr B2 x. auto.
    + eapply bs_forall with (k:=to_bk k); fold to_bexpr.
      * destruct k; auto.
      * destruct k; auto.
      * intros. specialize (H3 x H5). simpl in H3.
        rewrite_to_expr B2 x. rewrite_to_expr B1 x. auto.
        replace ((to_bcontext G),' x : (to_bexpr A1)) with ((to_bcontext G),' x : (to_bexpr A1),,'bctx_nil) in H3.
        eapply bidir_narrowing with (A:=to_bexpr A2) (k:=to_bk k) in H3.
        auto. destruct k; auto. auto.
  - simpl. eapply bs_anno with (k:=to_bk k).
    eapply bs_sub with (A := to_bexpr B) (k:=to_bk k).
    + admit. (* *** *)
    + admit. (* ** *)
    + destruct k; auto.
    + destruct k; auto.
  - eapply bs_castdn with (k:=to_bk k) (A:=to_bexpr A0). 
    + destruct k; auto.
    + constructor. 
      * apply to_bcontext_keeps_lc. admit. (* ** *)
      * admit. (* * *)
    + fold to_bexpr. eauto.
  - eapply bs_forall_l with (t:=to_bexpr t) (k:=to_bk k); fold to_bexpr.
    + apply to_bexpr_keeps_mono_type. auto.
    + destruct k; auto.
    + eapply bs_sub with (k:=to_bk k); eauto.
      destruct k; auto.
    + admit. (* * *)
    + intros. specialize (H3 x H4). simpl in H4.
      rewrite_to_expr B x. auto.
  - eapply bs_forall_r with (k:=to_bk k) (L:=L).
    + destruct k; auto.
    + auto.
    + intros. fold to_bexpr. specialize (H2 x H3). simpl in H2.
      rewrite_to_expr C x. auto.
  - eapply bs_forall with (k:=to_bk k) (L:=L).
    + destruct k; auto.
    + destruct k; auto.
    + intros. fold to_bexpr. specialize (H2 x H3). simpl in H2.
      rewrite_to_expr B x. rewrite_to_expr C x. auto. 
  - admit. (* ** *)

(* wf_context *)
  - constructor.
  - simpl. apply bwf_cons with (k:=to_bk k). 
    + auto.
    + apply to_bcontext_keeps_notin; auto.
    + destruct k; auto.
Admitted.


Theorem bidir_sound : forall Γ' e1' e2' d A' Γ e1 e2 A,
  busub_elab Γ' e1' e2' d A' Γ e1 e2 A → Γ ⊢ e1 <: e2 : A.
Proof.
  intros.
  induct ion H.
  (* pattern Γ', e1, e2', d, A', Γ, e1, e2, A, H.
  eapply busub_ind_dep with 
    (P0 := fun Γ' (_ : ⫦ Γ') => ⊢ Γ). *)
  1-7: admit.
  -
    replace B with (B ^^ t) by admit.
    eapply s_app.
Admitted.




(*
Theorem bidir_sound : forall Γ e1 e2 A d,
    busub Γ e1 e2 d A -> Γ ⊢ e1 <: e2 : A
Proof.
  intros.
  pattern Γ, e1, e2, d, A, H.
  apply busub_ind_dep with
      (P0 := fun Γ (_ : ⫦ Γ) => ⊢ Γ)
      (P1 := fun G A e B (_ : G ⊢ A ⋅ e ⇒ B) =>
        exists D E, G ⊢ e : D
        /\ B = E ^^ e /\ (A = e_pi D E \/ G ⊢ A <: e_pi D E : ⋆))
      (P2 := fun G A B (_ : G ⊢ A ⟼ B) => A ⟶ B \/ exists C, G ⊢ A <: C : ⋆ /\ C ⟶ B);
    intros.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - (* app *)
    destruct H1 as (D & E & Ht & -> & [-> | Hsub]).
    + eauto.
    + eauto.
  - admit.
  - admit.
  - (* castdn *) destruct H1.
    + eauto.
    + destruct_conjs.
      assert (G ⊢ e0 <: e3 : H1) by eauto 3.
      eauto 3.
  - admit.
  - admit.
  - admit.
  - admit.

  (* wf *)
  - admit.
  - admit.

  (* infer_app *)
  - exists A0, B; eauto.
  - destruct H1 as (D & E & Ht & -> & [Eb | Hsub]).
    + exists D, E; repeat split; eauto 3; right.
      rewrite <- Eb.
      pick fresh x and apply s_forall_l; eauto; admit.
    + exists D, E; repeat split; eauto 3; right.
      admit.

  (* greduce *)
  - auto.
  - right.
    assert (G ⊢ e_all A0 B <: B ^^ t : ⋆) by admit.
    destruct H1.
    + eauto.
    + destruct_conjs. exists H1. admit.

Admitted.

Theorem bidir_complete : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> Γ ⊢ e1 <: e2 ⇐ A.
Proof.
  intros.
  pattern Γ, e1, e2, A, H.
  apply usub_mut with (P0 := fun Γ (_ : ⊢ Γ) => ⫦ Γ); intros.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - (* app *)
    eapply bs_sub with (A := B ^^ t).
    + eapply bs_app; eauto 3; admit.
    + admit.
  - admit.
  - admit.
  - eapply bs_sub with (A := B).
    + eapply bs_castdn; eauto 3; admit.
    + admit.
  - admit.
  - admit.
  - admit.
  - (* sub, seems doable *)
    admit.

  (* ⫦ Γ *)
  - auto.
  - admit.
Admitted.
*)
