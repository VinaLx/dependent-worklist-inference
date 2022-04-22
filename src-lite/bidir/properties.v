Require Import decl.notations.
Require Export bidir.notations.
Require Import bidir.elaboration.
Require Import ln_utils.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.

Scheme Induction for busub Sort Prop
  with Induction for wf_bcontext Sort Prop
  with Induction for infer_app Sort Prop
  with Induction for greduce Sort Prop.


Lemma bctx_app_cons : forall Γ1 Γ2 x A,
    Γ1 ,,' Γ2 ,' x : A = Γ1 ,,' (Γ2 ,' x : A).
Proof.
  auto.
Qed.

Hint Rewrite bctx_app_cons : bctx.

Lemma weakening_auto_helper : forall Γ1 Γ2 x A,
    ⊢ Γ1 ,, Γ2 , x : A -> ⊢ Γ1 ,, (Γ2 , x : A).
Proof.
  auto.
Qed.


Lemma check_sub_invert : forall Γ e1 e2 A,
  Γ ⊢ e1 <: e2 ⇐ A ->
  A = ◻' \/ exists B k, Γ ⊢ B <: A ⇒ ⧼ k ⧽' /\ Γ ⊢ e1 <: e2 ⇒ B.
Proof.
  intros. dependent induction H; eauto.
Admitted.


Scheme  bwf_context_lc_mut     := Induction for wf_bcontext Sort Prop
  with  busub_bwf_lc_mut       := Induction for busub       Sort Prop
  with  infer_app_bwf_lc_mut   := Induction for infer_app   Sort Prop.


Lemma bwf_lc : forall Γ',
  ⫦ Γ' -> lc_bcontext Γ'.
Proof.
  intros.
  pattern Γ', H.
  eapply bwf_context_lc_mut with 
  (P0 := fun Γ' e1' e2' d A' (_ : busub Γ' e1' e2' d A') => 
    lc_bexpr e1' /\ lc_bexpr e2' /\ lc_bexpr A'
  )
  (P1 := fun Γ' A' F' (_ : infer_app Γ' A' F') => 
    match F' with 
    | fun_pi B C => forall x, lc_bexpr (C ^^' `'x)
    end
  ); 
  intros; try (intuition; fail); repeat split; auto; try solve_lc_bexpr.
  - induction i; auto. dependent destruction H0. dependent destruction w. auto.
  - intuition.
  - intuition.
  - dependent destruction l0. auto.
Qed.

Scheme  busub_lc_mut           := Induction for busub       Sort Prop
  with  infer_app_busub_lc_mut := Induction for infer_app   Sort Prop.

Lemma busub_all_lc : forall Γ' e1' e2' d' A',
  busub Γ' e1' e2' d' A' -> lc_bcontext Γ' /\ lc_bexpr e1' /\ lc_bexpr e2' /\ lc_bexpr A'.
Proof.
  intros.
  pattern Γ', e1', e2', d', A', H.
  eapply busub_lc_mut with 
  (P0 := fun Γ' A' F' (_ : infer_app Γ' A' F') => 
    match F' with 
    | fun_pi B C => forall x, lc_bexpr (C ^^' `'x)
    end
  );
  try (intuition; fail); repeat split; auto; try solve_lc_bexpr; intuition.
  + eapply bwf_lc; eauto. 
  + induction i; auto. dependent destruction w.  auto.
  + eapply bwf_lc; eauto.
  + eapply bwf_lc; eauto.
  + eapply bwf_lc; eauto.
  + dependent destruction l0. auto.
Qed.


Scheme busub_refl_mut := Induction for busub     Sort Prop
  with  iapp_refl_mut := Induction for infer_app Sort Prop.


Theorem bidir_refl_l : forall Γ e1 e2 d A,
  busub Γ e1 e2 d A -> busub Γ e1 e1 d A.
Proof.
  intros; induction H; eauto.
Qed.

Hint Resolve bidir_refl_l : bidir.

Theorem bidir_elab_refl_l : forall Γ' e1' e2' d A' Γ e1 e2 A,
  busub_elab Γ' e1' e2' d A' Γ e1 e2 A -> 
  busub_elab Γ' e1' e1' d A' Γ e1 e1 A.
Proof.
  intros.
  induction H; try solve [ auto | econstructor; eauto ].
Qed.

Lemma lc_binsert_middle : forall Γ1 Γ2 Γ3,
    lc_bcontext Γ2 -> lc_bcontext (Γ1,,'Γ3) -> lc_bcontext (Γ1,,'Γ2,,'Γ3).
Proof.
  intros.
  induction Γ2.
  - auto.
  - inversion H. simpl in *.
    induction Γ3.
    + simpl in *. constructor; auto.
    + simpl in *. inversion H0. 
      specialize (IHΓ2 H3). inversion IHΓ2.
      constructor; auto.
Qed.

Lemma lc_bmiddle : forall Γ1 Γ2 Γ3,
    lc_bcontext (Γ1,,'Γ2,,'Γ3) -> lc_bcontext Γ2.
Proof.
  intros.
  induction Γ3.
  - induction Γ2; simpl in *. auto.
    inversion H. constructor; auto.
  - inversion H. auto.
Qed.

Lemma in_bctx_weakening : forall Γ1 Γ2 Γ3 x A,
    lc_bcontext Γ2 -> in_bctx x A (Γ1 ,,' Γ3) -> in_bctx x A (Γ1 ,,' Γ2 ,,' Γ3).
Proof.
  intros.
  induction Γ3.
  - induction Γ2.
    + auto.
    + inversion H. simpl in *. econstructor; auto.
  - simpl in *. inversion H0. subst.
    + apply inb_here. 2: auto. apply lc_binsert_middle; auto.
    + apply inb_there. auto. apply IHΓ3. auto.
Qed.

Scheme  busub_weakening_mut     := Induction for busub       Sort Prop
  with  greduce_weakening_mut   := Induction for greduce     Sort Prop
  with  infer_app_weakening_mut := Induction for infer_app   Sort Prop.

Ltac weakening_auto := 
  match goal with 
  | x : atom |- _ =>
    repeat
    match goal with 
    | H : x `notin` union ?L ?dom |- _ => 
      match goal with 
      | H1 : forall x, x `notin` ?L -> 
              forall Γ4 Γ2 Γ5, _ -> bctx_cons (?Γ1 ,,' ?Γ3) x ?A = Γ5 ,,' Γ4 -> _ |- _ => 
        match goal with 
        | H2 : ⫦ ?Γ1,,' ?Γ2,,' ?Γ3 |- _ => 
        assert (⫦ Γ1,,' Γ2,,' Γ3,' x:A) as Hwfx by eauto;
        apply notin_union_1 in H as HnotinL;
        specialize (H1 x HnotinL (Γ3,'x:A) Γ2 Γ1 Hwfx (eq_refl (Γ1,,'Γ3,'x:A)));
        eauto 3;
        clear HnotinL; clear Hwfx
        end
      end
    end
  end.

Theorem bidir_weakening : forall Γ1 Γ2 Γ3 e1 e2 d A,
  busub (Γ1,,'       Γ3) e1 e2 d A -> ⫦ Γ1 ,,' Γ2 ,,' Γ3 ->
  busub (Γ1,,' Γ2,,' Γ3) e1 e2 d A.
Proof.  
  intros. remember (Γ1,,' Γ3) as Γ. 
  generalize dependent HeqΓ. generalize dependent Γ1. generalize dependent Γ2. generalize dependent Γ3.
  pattern Γ, e1, e2, d, A, H. 

  eapply busub_weakening_mut with 
  (P0 := fun Γ A B (_ : Γ ⊢ A ⟼ B) => 
    forall Γ1 Γ2 Γ3, 
    ⫦ Γ1,,' Γ2,,' Γ3 -> Γ = Γ1,,' Γ3 ->
    Γ1,,' Γ3 ⊢ A ⟼ B ->
    Γ1,,' Γ2,,' Γ3 ⊢ A ⟼ B
  )
  (P1 := fun Γ A F (_ : infer_app Γ A F) => 
    forall Γ1 Γ2 Γ3, 
    ⫦ Γ1,,' Γ2,,' Γ3 -> Γ = Γ1,,' Γ3 ->
    infer_app (Γ1,,'Γ3) A F -> 
    infer_app (Γ1,,'Γ2,,'Γ3) A F
  ); intros; auto; subst. 

  (** busub **)
  - constructor. auto. eapply in_bctx_weakening; auto. 
    eapply lc_bmiddle. apply bwf_lc. eauto.
  - econstructor. eauto.
  - eapply bs_abs with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros; weakening_auto. 
  - eapply bs_pi with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros.
    + weakening_auto. 
    + specialize (H1 Γ3 Γ2 Γ1 H4). apply bidir_refl_l in H1. weakening_auto. auto.
  - eauto.
  - eapply bs_bind with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros; weakening_auto.
  - eauto.
  - eauto.
  - eapply bs_forall_l with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros; weakening_auto.
  - eapply bs_forall_r with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros; weakening_auto.
  - eapply bs_forall with (L:=L `union` bctx_dom (Γ1,,'Γ2,,'Γ3)); eauto; intros.
    specialize (H0 Γ3 Γ2 Γ1 H3 (eq_refl (Γ1,,'Γ3))). apply bidir_refl_l in H0.
    weakening_auto.
  - eauto.
  - eauto.

  (** greduce **)
  - dependent destruction H2.
    + apply gr_reduce; auto. apply bwf_lc. auto.
    + econstructor. apply bwf_lc. auto. auto. 
  - eapply gr_all with (t:=t); auto.
  
  (** infer_app **)
  - econstructor; eauto. apply bwf_lc. eauto.
  - dependent destruction H4. 
    intros. eapply iapp_all with (t:=t); eauto.
Qed.

Theorem bidir_weakening' : forall Γ1 Γ2 Γ3 e1 e2 d A,
  busub (Γ1,,'       Γ3) e1 e2 d A -> ⫦ Γ1 ,,' Γ2 ,,' Γ3 ->
  busub (Γ1,,' Γ2,,' Γ3) e1 e2 d A.
Proof with autorewrite with bctx; eauto.  
  intros. remember (Γ1,,' Γ3) as Γ. 
  generalize dependent HeqΓ. generalize dependent Γ3.
  pattern Γ, e1, e2, d, A, H. 

  eapply busub_weakening_mut with 
  (P0 := fun Γ A B (_ : Γ ⊢ A ⟼ B) => 
    forall Γ3, 
    Γ = Γ1,,' Γ3 ->
    Γ1,,' Γ2,,' Γ3 ⊢ A ⟼ B
  )
  (P1 := fun Γ A F (_ : infer_app Γ A F) => 
    forall Γ3, 
    Γ = Γ1,,' Γ3 ->
    infer_app (Γ1,,'Γ2,,'Γ3) A F
  ); intros; auto; subst. 

  (** busub **)
  - constructor. auto. eapply in_bctx_weakening; auto. 
    eapply lc_bmiddle. apply bwf_lc. eauto.
  - econstructor. eauto.
  - eapply bs_abs with (L:=L); eauto; intros; inst_cofinites_with x. eauto...
    eapply H1; auto. simpl. admit.
Admitted.

(* Theorem bidir_elab_weakening : forall Γ1' Γ2' Γ3' e1' e2' d k Γ1 Γ2 Γ3 e1 e2,
  busub_elab (Γ1',,'         Γ3') e1' e2' d ⧼k⧽' (Γ1,,      Γ3) e1 e2 ⧼(to_k k)⧽ ->
  wf_context_elab (Γ1',,'Γ2',,'Γ3') (Γ1,,Γ2,,Γ3) ->
  busub_elab (Γ1',,'  Γ2',,' Γ3') e1' e2' d ⧼k⧽' (Γ1,, Γ2,, Γ3) e1 e2 ⧼(to_k k)⧽.
Proof.
  intros.
Admitted. *)

Lemma bctx_dom_narrowing_eq : forall Γ1 Γ2 x A B,
  bctx_dom (Γ1,' x : A,,' Γ2) = bctx_dom (Γ1,' x : B,,' Γ2).
intros.
  induction Γ2.
  - auto.
  - simpl. rewrite IHΓ2. auto.
Qed.

Hint Rewrite bctx_dom_narrowing_eq : bctx.


Lemma bidir_narrowing_lc_helper : forall Γ1 Γ2 x A B k,
  lc_bcontext (Γ1,' x : B,,' Γ2) ->
  Γ1 ⊢ A <: B ⇒ ⧼ k ⧽' ->
  lc_bcontext (Γ1,' x : A,,' Γ2).
Proof.
  intros.
  replace (Γ1,' x : B,,' Γ2) with (Γ1,' x : B,,' Γ2,,' bctx_nil) in H by auto.
  apply lc_bmiddle in H. 
  replace (Γ1,' x : A,,' Γ2) with (Γ1,' x : A,,' Γ2,,' bctx_nil) by auto.
  apply lc_binsert_middle; apply busub_all_lc in H0; simpl; intuition.
Qed.

Scheme  busub_narrowing_mut       := Induction for busub       Sort Prop
  with  wf_bcontext_narrowing_mut := Induction for wf_bcontext Sort Prop
  with  greduce_narrowing_mut     := Induction for greduce     Sort Prop
  with  infer_app_narrowing_mut   := Induction for infer_app   Sort Prop.

(* Theorem bidir_narrowing : forall Γ1 x B Γ2 e1 e2 d C,
  busub (Γ1,' x : B,,' Γ2) e1 e2 d C -> 
  forall A k, Γ1 ⊢ A <: B ⇒ ⧼ k ⧽' -> 
  busub (Γ1,' x : A,,' Γ2) e1 e2 d C.
Proof with autorewrite with bctx; eauto.
  intros. remember (Γ1,' x : B,,' Γ2) as Γ.
  generalize dependent HeqΓ. generalize dependent Γ2. 
  pattern Γ, e1, e2, d, C, H.
    
  eapply busub_narrowing_mut with 
  (P := fun Γ e1 e2 d C (_ : busub Γ e1 e2 d C) =>
    forall Γ2, 
     Γ = Γ1 ,' x : B ,,' Γ2 ->
     busub (Γ1 ,' x : A ,,' Γ2) e1 e2 d C
  )
  (P0 := fun Γ (_ : wf_bcontext Γ) => 
    forall Γ2, 
      Γ = Γ1,' x : B,,' Γ2 -> 
      ⫦ Γ1,' x : A,,' Γ2
  )
  (P1 := fun Γ C D (_ : Γ ⊢ C ⟼ D) => 
    forall Γ2, 
      Γ = Γ1,' x:B,,' Γ2 ->
      Γ1,' x : A,,' Γ2 ⊢ C ⟼ D
  )
  (P2 := fun Γ C F (_ : infer_app Γ C F) =>
    forall Γ2, 
      Γ = Γ1,' x:B,,' Γ2 ->
      infer_app (Γ1,' x : A,,' Γ2) C F
  )
  ; intros; auto; subst.
  - destruct (x==x0).
    + subst. assert (A0=B) by admit. subst. econstructor. admit. admit.
    + econstructor. admit. admit.
  - eauto.
  - eapply bs_abs with (L:=L); eauto; intros; inst_cofinites_with x0; eauto... 
  - eapply bs_pi with (L:=L); eauto; intros; inst_cofinites_with x0; eauto...
  - eauto. 
  - eapply bs_bind with (L:=L); eauto; intros; inst_cofinites_with x0; eauto...
  - eauto.
  - eauto. 
  - eapply bs_forall_l with (L:=L); eauto; intros; inst_cofinites_with x0; eauto...
  - eapply bs_forall_r with (L:=L); eauto.
    intros. inst_cofinites_with x. eauto...
  - eapply bs_forall with (L:=L); eauto; intros.
    inst_cofinites_with x. eauto...
  - eauto.
  - eauto.

  (* P0 *)
  - destruct Γ2; inversion H1.
  - destruct Γ2.
    + dependent destruction H3. simpl. econstructor; auto.
      eapply bidir_refl_l in H0. eauto.
    + dependent destruction H3. simpl. econstructor; eauto.
      replace (bctx_dom (Γ1,' x : A,,' Γ2)) with (bctx_dom (Γ1,' x : B,,' Γ2)); auto.
      eapply bctx_dom_narrowing_eq.

  (* P1 *)
  - admit. 
  (* dependent destruction b; econstructor; eauto; eapply bidir_narrowing_lc_helper; eauto. *)
  - eapply gr_all; eauto. 

  (* P2 *)
  - econstructor; eauto. eapply bidir_narrowing_lc_helper; eauto.
  - econstructor; eauto.
Admitted. 


Hint Resolve bidir_narrowing : bidir. *)

(* Theorem bidir_elab_narrowing : forall Γ1' x B' Γ2' e1' e2' d C' Γ1 B Γ2 e1 e2 C,
  busub_elab (Γ1',' x : B',,' Γ2') e1' e2' d C' (Γ1, x : B,, Γ2) e1 e2 C ->
  forall A A' k, Γ1' ⊢ A' <: B' ⇒ ⧼ k ⧽' ->
  busub_elab (Γ1',' x : A',,' Γ2') e1' e2' d C' (Γ1, x : A,, Γ2) e1 e2 C.
Proof.
Admitted. *)
