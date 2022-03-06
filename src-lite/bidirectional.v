Require Import decl.properties.
Require Import decl.ln_inf.
Require Import Program.Tactics.
Require Import bidir.properties.
Require Import bidir.elaboration.

Require Import Lia.

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
    + inversion H.
      inversion H2. constructor. admit.
    + inversion H.
      inversion H3. constructor.
      * apply IHA. assumption.
      * admit.
  
  - inversion H. constructor; fold open_bexpr_wrt_bexpr_rec; fold to_bexpr.
    + apply IHA1. auto.
    + intros.
      specialize (H3 x0).
      admit.
  - unfold to_bexpr. destruct b. inversion H. constructor; fold open_bexpr_wrt_bexpr_rec; fold to_bexpr.
    + constructor. admit.
    + constructor; inversion H3.  apply IHA. auto. admit. 
  - inversion H. constructor; fold open_bexpr_wrt_bexpr_rec; fold to_bexpr.
    + apply IHA1. assumption. 
    + intro. admit.
  - inversion H; constructor.
    + inversion H2. constructor. apply IHA2. auto.
    + eauto.
  - inversion H; constructor; eauto.
Admitted. 


(* Theorem to_bexpr_keeps_lc : forall A, lc_expr A -> lc_bexpr (to_bexpr A).
Proof.
  intros. induction H; try (simpl; constructor; auto).
  (* lc_e_kind *)
  - destruct k; constructor.
  (* lc_e_abs *)
  - unfold to_bexpr. destruct b. fold to_bexpr.
    constructor.

    constructor. destruct b eqn:Heqb. subst. simpl. constructor.  
    + constructor. intros. specialize (H0 x). inversion H0. auto. admit.
    + constructor. auto. intros. specialize (H0 x). inversion H0. admit.
  (* lc_e_pi *)
  - intros. specialize (H1 x). auto. eapply lc_tobexpr. eauto.
| _ => (* lc_e_bind *)
  - destruct b eqn:Heqb. subst. simpl. constructor.
    + constructor. intro. specialize (H0 x). admit.
    + constructor. auto.  intro. specialize (H0 x). admit.
  (* lc_e_all *)
  - intros. eapply lc_tobexpr. eapply H1.
Admitted.

Scheme Induction for lc_expr Sort Prop
  with Induction for lc_body Sort Prop.

Theorem to_bexpr_keeps_lc : forall A, lc_expr A -> lc_bexpr (to_bexpr A).
Proof.
  intros. pattern A, H.  
  apply lc_expr_ind_dep with (
      P0 := fun b (_ : lc_body b) => match b with (b_anno e A)  => lc_expr e /\ lc_expr A end);
    intros; try (simpl; auto).
  - destruct k; simpl; auto.
  - destruct b. simpl in H1.
    + constructor.
      * constructor. intros. specialize (H1 x). destruct H1. apply lc_tobexpr. admit.
      * constructor. auto. intros. specialize (H1 x). destruct H1. apply lc_tobexpr. admit.
  - constructor; auto. intros. apply lc_tobexpr. auto.
  - destruct b. simpl in H1. constructor.
    + constructor. intros. specialize (H1 x). destruct H1. apply lc_tobexpr. admit.
    + constructor. auto. intros. specialize (H1 x). destruct H1. apply lc_tobexpr. admit.
  - constructor; auto. intros. apply lc_tobexpr. auto.
Admitted. *)

Scheme Induction for expr Sort Prop
  with Induction for body Sort Prop.

Theorem to_bexpr_keeps_lc : forall n A, size_expr A < n -> lc_expr A -> lc_bexpr (to_bexpr A).
Proof.
  intros n.
  induction n.
  - intros. inversion H.
  - intro.
    apply expr_ind with
      (P := fun A => (size_expr A < S n -> lc_expr A -> lc_bexpr (to_bexpr A)))
      (P0 := fun b => lc_body b ->  match b with (b_anno e A)  => lc_expr e /\ lc_expr A end);
    intros; try (simpl; auto).
(* P *)
    + inversion H0.
    + destruct k; constructor.
    + constructor.
      * constructor.
      * inversion H1. simpl in H0. eapply H; eauto. lia.
    + constructor.
      * inversion H2. simpl in H1. eapply H; eauto. lia.
      * inversion H2. simpl in H1. eapply H0; auto. lia.
    + destruct b. simpl in *. constructor; inversion H2.
      * constructor. intros.  apply lc_tobexpr.
        eapply IHn.
        -- unfold open_expr_wrt_expr. rewrite (size_expr_open_expr_wrt_expr_rec_var e x 0). lia.
        -- specialize (H6 x). inversion H6. auto.
      * constructor.
        -- apply IHn. lia. auto.
        -- intro. specialize (H6 x). inversion H6. apply lc_tobexpr. apply IHn.
           unfold open_expr_wrt_expr. rewrite (size_expr_open_expr_wrt_expr_rec_var A1 x 0). lia.
           assumption.
    + inversion H2. simpl in *. constructor.
      * apply IHn. lia. auto.
      * intros. apply lc_tobexpr. apply IHn.
        unfold open_expr_wrt_expr. rewrite (size_expr_open_expr_wrt_expr_rec_var B x 0). lia.
        apply H6.
    + destruct b. simpl in *. inversion H2. constructor.
      * constructor. intro. specialize (H6 x). inversion H6. apply lc_tobexpr.
        eapply IHn.
        -- unfold open_expr_wrt_expr. rewrite (size_expr_open_expr_wrt_expr_rec_var e x 0). lia.
        -- auto.
      * constructor.
        -- apply IHn. lia. auto.
        -- intro. specialize (H6 x). inversion H6. apply lc_tobexpr.
           apply IHn.
           ++ unfold open_expr_wrt_expr. rewrite (size_expr_open_expr_wrt_expr_rec_var A1 x 0). lia.
           ++ assumption.
    + inversion H2. simpl in *. constructor.
      * apply IHn. lia. assumption.
      * intro. specialize (H6 x). apply lc_tobexpr. eapply IHn.
        -- unfold open_expr_wrt_expr. rewrite (size_expr_open_expr_wrt_expr_rec_var B x 0). lia.
        -- assumption.
    + inversion H2. simpl in H1. constructor.
      * constructor. apply IHn. lia. assumption.
      * apply IHn. lia. assumption.
    + inversion H1. simpl in H0. constructor.
      * apply IHn. lia. assumption.
(* P0 *)
    + inversion H1. split; auto.
Qed.        


Theorem to_bcontext_keeps_lc : forall Γ, lc_context Γ -> lc_bcontext (to_bcontext Γ).
Proof.
  intros.
  induction Γ.
  - auto.
  - simpl. constructor; inversion H; subst.
    + apply IHΓ. auto.
    + apply to_bexpr_keeps_lc. auto.
Qed.


Theorem to_bcontext_keeps_notin : forall x G, 
  x `notin` ctx_dom G
  -> x `notin` bctx_dom (to_bcontext G).
Proof.
  intros. induction G.
  - auto.
  - simpl in *.
    specialize (notin_add_1' x0 x (ctx_dom G) H) as Hxx0.
    specialize (notin_add_2 x0 x (ctx_dom G) H) as HxG.
    apply notin_add_3; auto.
Qed.

Lemma wf_context_elab_keeps_lc : forall G Γ,
    wf_context_elab Γ G
    -> lc_context G
    -> lc_bcontext Γ.
Proof.
  intros. induction H.
  - constructor.
  - constructor. inversion H0. auto.  
Admitted.


Check expr_ind.

Lemma in_context_elab : forall Γ x A,
    x :_ A ∈ Γ -> ⊢ Γ -> forall Γ', wf_context_elab Γ' Γ -> exists A' k, in_bctx x A' Γ' /\ busub_elab Γ' A' A' d_infer ⧼k⧽' Γ A A ⧼(to_k k)⧽.
Proof.
  intros * In Wf.
  induction In; intros.
  - inversion H1; subst. exists A', k.
    split. inversion H1. subst. eapply inb_here.
    + inversion H6.  constructor. constructor.  admit.
    + admit.
    + admit.
  - inversion H0. subst.
    inversion Wf; subst.
    specialize (IHIn H4 Γ'0 H5). destruct IHIn as [A'0 [k1 [IHInbctx  IHBusubElab]]].
    exists A'0, k1. split. 
    + apply inb_there. admit. auto.
    + constructor. 
    
      admit. admit.
Admitted.

Print usub_mut.

Theorem bidir_complete : forall Γ e1 e2 A
  , Γ ⊢ e1 <: e2 : A
  -> busub_elab
      (to_bcontext Γ) (to_bexpr e1) (to_bexpr e2) d_infer (to_bexpr A)
      Γ e1 e2 A.
Proof.
  intros. pattern Γ, e1, e2, A, H.
  apply usub_mut with
    (P0 := fun Γ (_ : ⊢ Γ) => wf_context_elab (to_bcontext Γ) Γ); intros.
  
(* busub_elab *)
  - constructor; auto. induction i; simpl in *.
    + apply inb_here. apply to_bcontext_keeps_lc. auto. apply to_bexpr_keeps_lc. auto.
    + apply inb_there. apply to_bexpr_keeps_lc. auto. 
      eapply IHi. inversion w. auto. inversion H0. auto. 
  - constructor. auto. 
  - constructor. auto. 
  - constructor. auto.
  (* busub_elab *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
    
(* wf_context_elab *)
  - constructor.
  - simpl. apply (wfe_cons (to_bcontext G) G x (to_bexpr A0) A0 (to_bk k)).
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
