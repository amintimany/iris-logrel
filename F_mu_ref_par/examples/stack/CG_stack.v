From iris.proofmode Require Import invariants ghost_ownership tactics.
From F_mu_ref_par Require Import lang examples.lock typing
     logrel_binary fundamental_binary rules_binary rules.
Import uPred.

Section CG_Stack.
  Context {Σ : gFunctors} {iS : cfgSG Σ}.

  Definition CG_StackType τ :=
    (TRec (TSum TUnit (TProd τ.[ren (+1)] (TVar 0)))).

  (* Coarse-grained push *)
  Definition CG_push (st : expr) : expr :=
    Lam (App (Lam (Store st.[ren (+ 4)] (Fold (InjR (Pair (Var 3) (Var 1))))))
             (Load st.[ren (+ 2)])).

  Lemma CG_push_type st Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ (CG_push st) (TArrow τ TUnit).
  Proof.
    intros H1. repeat econstructor.
    eapply (context_weakening [_; _; _; _]); eauto.
    repeat constructor; by asimpl.
    eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma CG_push_closed (st : expr) :
    (∀ f, st.[f] = st) → ∀ f, (CG_push st).[f] = CG_push st.
  Proof. intros H f. unfold CG_push. asimpl. rewrite ?H; trivial. Qed.

  Lemma CG_push_subst (st : expr) f :
  (CG_push st).[f] = CG_push st.[f].
  Proof. unfold CG_push; asimpl; trivial. Qed.

  Lemma steps_CG_push N E ρ j K st v w :
    nclose N ⊆ E →
    ((Spec_ctx N ρ ★ st ↦ₛ v ★
               j ⤇ (fill K (App (CG_push (Loc st)) (# w))))%I)
      ⊢ |={E}=>(j ⤇ (fill K (Unit)) ★ st ↦ₛ (FoldV (InjRV (PairV w v))))%I.
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold CG_push.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    iPvs (step_load _ _ _ j (K ++ [AppRCtx (LamV _)])
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    iPvs (step_store _ _ _ j K _ _ _ _ _
          with "[Hj Hx]") as "[Hj Hx]"; eauto.
    iFrame "Hspec Hj"; trivial.
    iPvsIntro. iFrame "Hj Hx"; trivial.
    Unshelve.
    all: try match goal with |- to_val _ = _ => auto using to_of_val end.
    simpl; by rewrite ?to_of_val.
  Qed.

  Global Opaque CG_push.

  Definition CG_locked_push (st l : expr) :=
    with_lock (CG_push st) l.
  Definition CG_locked_pushV (st l : expr) : val :=
    with_lockV (CG_push st) l.

  Lemma CG_locked_push_to_val st l :
    to_val (CG_locked_push st l) = Some (CG_locked_pushV st l).
  Proof. trivial. Qed.

  Lemma CG_locked_push_of_val st l :
    of_val (CG_locked_pushV st l) = CG_locked_push st l.
  Proof. trivial. Qed.

  Global Opaque CG_locked_pushV.

  Lemma CG_locked_push_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_locked_push st l) (TArrow τ TUnit).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; auto using CG_push_type.
  Qed.

  Lemma CG_locked_push_closed (st l : expr) :
    (∀ f, st.[f] = st) → (∀ f, l.[f] = l) →
    ∀ f, (CG_locked_push st l).[f] = CG_locked_push st l.
  Proof.
    intros H1 H2 f. asimpl. unfold CG_locked_push.
    rewrite with_lock_closed; trivial. apply CG_push_closed; trivial.
  Qed.

  Lemma CG_locked_push_subst (st l : expr) f :
  (CG_locked_push st l).[f] = CG_locked_push st.[f] l.[f].
  Proof. by rewrite with_lock_subst CG_push_subst. Qed.

  Lemma steps_CG_locked_increment N E ρ j K st w v l :
    nclose N ⊆ E →
    ((Spec_ctx N ρ ★ st ↦ₛ v ★ l ↦ₛ (♭v false)
               ★ j ⤇ (fill K (App (CG_locked_push (Loc st) (Loc l)) (# w))))%I)
      ⊢ |={E}=>(j ⤇ (fill K (Unit)) ★ st ↦ₛ (FoldV (InjRV (PairV w v)))
                 ★ l ↦ₛ (♭v false))%I.
  Proof.
    intros HNE. iIntros "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_push.
    iPvs (steps_with_lock
            _ _ _ j K _ _ _ _ UnitV _ _ _ with "[Hj Hx Hl]") as "Hj"; eauto.
    - intros K'.
      iIntros "[#Hspec [Hx Hj]]".
      iApply steps_CG_push; eauto. iFrame "Hspec Hj Hx"; trivial.
    - iFrame "Hspec Hj Hx"; trivial.
      Unshelve. all: trivial.
  Qed.

  Global Opaque CG_locked_push.

    (* Coarse-grained pop *)
  Definition CG_pop (st : expr) : expr :=
    Lam (App (Lam (App (Lam
                          (
                            Case (Var 1)
                                 (InjL Unit)
                                 (
                                   App (Lam (InjR (Fst (Var 2))))
                                       (Store st.[ren (+ 7)] (Snd (Var 0)))
                                 )
                          )
                       )
                       (Unfold (Var 1))
                  )
             )
             (Load st.[ren (+ 2)])
        ).

  Lemma CG_pop_type st Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ (CG_pop st) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    intros H1.
    do 2 econstructor;
      [|econstructor; eapply (context_weakening [_; _]); eauto].
    do 2 econstructor. 2: repeat constructor. asimpl.
    repeat econstructor.
    eapply (context_weakening [_; _; _; _; _; _; _]); eauto.
  Qed.

  Lemma CG_pop_closed (st : expr) :
    (∀ f, st.[f] = st) → ∀ f, (CG_pop st).[f] = CG_pop st.
  Proof. intros H f. unfold CG_pop. asimpl. rewrite ?H; trivial. Qed.

  Lemma CG_pop_subst (st : expr) f :
  (CG_pop st).[f] = CG_pop st.[f].
  Proof. unfold CG_pop; asimpl; trivial. Qed.

  Lemma steps_CG_pop_suc N E ρ j K st v w :
    nclose N ⊆ E →
    ((Spec_ctx N ρ ★ st ↦ₛ (FoldV (InjRV (PairV w v))) ★
               j ⤇ (fill K (App (CG_pop (Loc st)) Unit)))%I)
      ⊢ |={E}=>(j ⤇ (fill K (InjR (# w))) ★ st ↦ₛ v)%I.
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold CG_pop.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    iPvs (step_load _ _ _ j (K ++ [AppRCtx (LamV _)])
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    iPvs (step_Fold _ _ _ j (K ++ [AppRCtx (LamV _)])
                    _ _ _ _ with "[Hj]") as "Hj"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    iPvs (step_case_inr _ _ _ j K _ _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    iPvs (step_snd _ _ _ j (K ++ [AppRCtx (LamV _); StoreRCtx (LocV _)]) _ _ _ _
                   _ _ with "[Hj]") as "Hj"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    iPvs (step_store _ _ _ j (K ++ [AppRCtx (LamV _)]) _ _ _ _ _ _
          with "[Hj Hx]") as "[Hj Hx]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    iPvs (step_fst _ _ _ j (K ++ [InjRCtx]) _ _ _ _ _ _
          with "[Hj]") as "Hj"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial. asimpl.
    rewrite ?fill_app. simpl.
    iPvsIntro. iFrame "Hj Hx"; trivial.
    Unshelve.
    all: try match goal with |- to_val _ = _ => simpl; by rewrite ?to_of_val end.
    all: trivial.
  Qed.

  Lemma steps_CG_pop_fail N E ρ j K st :
    nclose N ⊆ E →
    ((Spec_ctx N ρ ★ st ↦ₛ (FoldV (InjLV UnitV)) ★
               j ⤇ (fill K (App (CG_pop (Loc st)) Unit)))%I)
      ⊢ |={E}=>(j ⤇ (fill K (InjL Unit)) ★ st ↦ₛ (FoldV (InjLV UnitV)))%I.
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold CG_pop.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    iPvs (step_load _ _ _ j (K ++ [AppRCtx (LamV _)])
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    iPvs (step_Fold _ _ _ j (K ++ [AppRCtx (LamV _)])
                    _ _ _ _ with "[Hj]") as "Hj"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    iPvs (step_case_inl _ _ _ j K _ _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    iPvsIntro. iFrame "Hj Hx"; trivial.
    Unshelve.
    all: try match goal with |- to_val _ = _ => simpl; by rewrite ?to_of_val end.
    all: trivial.
  Qed.

  Global Opaque CG_pop.

  Definition CG_locked_pop (st l : expr) :=
    with_lock (CG_pop st) l.
  Definition CG_locked_popV (st l : expr) : val :=
    with_lockV (CG_pop st) l.

  Lemma CG_locked_pop_to_val st l :
    to_val (CG_locked_pop st l) = Some (CG_locked_popV st l).
  Proof. trivial. Qed.

  Lemma CG_locked_pop_of_val st l :
    of_val (CG_locked_popV st l) = CG_locked_pop st l.
  Proof. trivial. Qed.

  Global Opaque CG_locked_popV.

  Lemma CG_locked_pop_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_locked_pop st l) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; auto using CG_pop_type.
  Qed.

  Lemma CG_locked_pop_closed (st l : expr) :
    (∀ f, st.[f] = st) → (∀ f, l.[f] = l) →
    ∀ f, (CG_locked_pop st l).[f] = CG_locked_pop st l.
  Proof.
    intros H1 H2 f. asimpl. unfold CG_locked_pop.
    rewrite with_lock_closed; trivial. apply CG_pop_closed; trivial.
  Qed.

  Lemma CG_locked_pop_subst (st l : expr) f :
  (CG_locked_pop st l).[f] = CG_locked_pop st.[f] l.[f].
  Proof. by rewrite with_lock_subst CG_pop_subst. Qed.

  Lemma steps_CG_locked_pop_suc N E ρ j K st v w l :
    nclose N ⊆ E →
    ((Spec_ctx N ρ ★ st ↦ₛ (FoldV (InjRV (PairV w v))) ★ l ↦ₛ (♭v false)
               ★ j ⤇ (fill K (App (CG_locked_pop (Loc st) (Loc l)) Unit)))%I)
      ⊢ |={E}=>(j ⤇ (fill K (InjR (# w))) ★ st ↦ₛ v
                 ★ l ↦ₛ (♭v false))%I.
  Proof.
    intros HNE. iIntros "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_pop.
    iPvs (steps_with_lock _ _ _ j K _ _ _ _ (InjRV w) UnitV _ _
          with "[Hj Hx Hl]") as "Hj"; eauto.
    - intros K'.
      iIntros "[#Hspec [Hx Hj]]".
      iApply steps_CG_pop_suc; eauto. iFrame "Hspec Hj Hx"; trivial.
    - iFrame "Hspec Hj Hx"; trivial.
      Unshelve. all: trivial.
  Qed.

  Lemma steps_CG_locked_pop_fail N E ρ j K st l :
    nclose N ⊆ E →
    ((Spec_ctx N ρ ★ st ↦ₛ (FoldV (InjLV UnitV)) ★ l ↦ₛ (♭v false)
               ★ j ⤇ (fill K (App (CG_locked_pop (Loc st) (Loc l)) Unit)))%I)
      ⊢ |={E}=>(j ⤇ (fill K (InjL Unit)) ★ st ↦ₛ (FoldV (InjLV UnitV))
                 ★ l ↦ₛ (♭v false))%I.
  Proof.
    intros HNE. iIntros "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_pop.
    iPvs (steps_with_lock _ _ _ j K _ _ _ _ (InjLV UnitV) UnitV _ _
          with "[Hj Hx Hl]") as "Hj"; eauto.
    - intros K'.
      iIntros "[#Hspec [Hx Hj]]". simpl.
      iApply steps_CG_pop_fail; eauto. iFrame "Hspec Hj Hx"; trivial.
    - iFrame "Hspec Hj Hx"; trivial.
      Unshelve. all: trivial.
  Qed.

  Global Opaque CG_locked_pop.

End CG_Stack.