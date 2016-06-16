From iris.proofmode Require Import invariants ghost_ownership tactics.
From iris_logrel.F_mu_ref_par Require Import lang examples.lock typing
     rules_binary rules.
Import uPred.

Section CG_Stack.
  Context {Σ : gFunctors} {iS : cfgSG Σ}.

  Definition CG_StackType τ :=
    (TRec (TSum TUnit (TProd τ.[ren (+1)] (TVar 0)))).

  (* Coarse-grained push *)
  Definition CG_push (st : expr) : expr :=
    Lam (Store
           (st.[ren (+2)]) (Fold (InjR (Pair (Var 1) (Load st.[ren (+ 2)]))))).

  Lemma CG_push_type st Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ (CG_push st) (TArrow τ TUnit).
  Proof.
    intros H1. repeat econstructor.
    eapply (context_weakening [_; _]); eauto.
    repeat constructor; asimpl; trivial.
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
    asimpl.
    iPvs (step_load _ _ _ j (K ++ [StoreRCtx (LocV _); FoldCtx;
                                   InjRCtx; PairRCtx _])
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_store _ _ _ j K _ _ _ _ _
          with "[Hj Hx]") as "[Hj Hx]"; eauto.
    iFrame "Hspec Hj"; trivial.
    iPvsIntro. by iFrame.
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

  Lemma steps_CG_locked_push N E ρ j K st w v l :
    nclose N ⊆ E →
    ((Spec_ctx N ρ ★ st ↦ₛ v ★ l ↦ₛ (♭v false)
               ★ j ⤇ (fill K (App (CG_locked_push (Loc st) (Loc l)) (# w))))%I)
      ⊢ |={E}=>(j ⤇ (fill K (Unit)) ★ st ↦ₛ (FoldV (InjRV (PairV w v)))
                 ★ l ↦ₛ (♭v false))%I.
  Proof.
    intros HNE. iIntros "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_push.
    iPvs (steps_with_lock
            _ _ _ j K _ _ _ _ UnitV _ _ _ with "[Hj Hx Hl]") as "Hj"; last done.
    - iIntros {K'} "[#Hspec [Hx Hj]]".
      iApply steps_CG_push; first done. iFrame "Hspec Hj Hx"; trivial.
    - iFrame "Hspec Hj Hx"; trivial.
      Unshelve. all: trivial.
  Qed.

  Global Opaque CG_locked_push.

  (* Coarse-grained pop *)
  Definition CG_pop (st : expr) : expr :=
    Lam (Case (Unfold (Load st.[ren (+ 2)]))
              (InjL Unit)
              (
                App (Lam (InjR (Fst (Var 2))))
                    (Store st.[ren (+ 3)] (Snd (Var 0)))
              )
        ).

  Lemma CG_pop_type st Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ (CG_pop st) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    intros H1.
    econstructor.
    eapply (Case_typed _ _ _ _ TUnit);
      [| repeat constructor
       | repeat econstructor; eapply (context_weakening [_; _; _]); eauto].
    replace (TSum TUnit (TProd τ (CG_StackType τ))) with
    ((TSum TUnit (TProd τ.[ren (+1)] (TVar 0))).[(CG_StackType τ)/])
      by (by asimpl).
    repeat econstructor.
    eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma CG_pop_closed (st : expr) :
    (∀ f, st.[f] = st) → ∀ f, (CG_pop st).[f] = CG_pop st.
  Proof. intros H f. unfold CG_pop. asimpl. rewrite ?H; trivial. Qed.

  Lemma CG_pop_subst (st : expr) f : (CG_pop st).[f] = CG_pop st.[f].
  Proof. unfold CG_pop; asimpl; trivial. Qed.

  Lemma steps_CG_pop_suc N E ρ j K st v w :
    nclose N ⊆ E →
    Spec_ctx N ρ ★ st ↦ₛ FoldV (InjRV (PairV w v)) ★
               j ⤇ fill K (App (CG_pop (Loc st)) Unit)
      ={E}=> j ⤇ fill K (InjR (# w)) ★ st ↦ₛ v.
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold CG_pop.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iPvs (step_load _ _ _ j (K ++ [CaseCtx _ _; UnfoldCtx])
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_Fold _ _ _ j (K ++ [CaseCtx _ _])
                    _ _ _ _ with "[Hj]") as "Hj"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_case_inr _ _ _ j K _ _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
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
    asimpl.
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
    Spec_ctx N ρ ★ st ↦ₛ FoldV (InjLV UnitV) ★
               j ⤇ fill K (App (CG_pop (Loc st)) Unit)
      ={E}=> j ⤇ fill K (InjL Unit) ★ st ↦ₛ FoldV (InjLV UnitV).
  Proof.
    iIntros {HNE} "[#Hspec [Hx Hj]]". unfold CG_pop.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iPvs (step_load _ _ _ j (K ++ [CaseCtx _ _; UnfoldCtx])
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_Fold _ _ _ j (K ++ [CaseCtx _ _])
                    _ _ _ _ with "[Hj]") as "Hj"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_case_inl _ _ _ j K _ _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
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
    Spec_ctx N ρ ★ st ↦ₛ FoldV (InjRV (PairV w v)) ★ l ↦ₛ (♭v false)
               ★ j ⤇ fill K (App (CG_locked_pop (Loc st) (Loc l)) Unit)
      ={E}=> j ⤇ fill K (InjR (# w)) ★ st ↦ₛ v ★ l ↦ₛ (♭v false).
  Proof.
    iIntros {HNE} "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_pop.
    iPvs (steps_with_lock _ _ _ j K _ _ _ _ (InjRV w) UnitV _ _
          with "[Hj Hx Hl]") as "Hj"; last done.
    - iIntros {K'} "[#Hspec [Hx Hj]]".
      iApply steps_CG_pop_suc; first done. iFrame "Hspec Hj Hx"; trivial.
    - iFrame "Hspec Hj Hx"; trivial.
      Unshelve. all: trivial.
  Qed.

  Lemma steps_CG_locked_pop_fail N E ρ j K st l :
    nclose N ⊆ E →
    Spec_ctx N ρ ★ st ↦ₛ FoldV (InjLV UnitV) ★ l ↦ₛ (♭v false)
               ★ j ⤇ fill K (App (CG_locked_pop (Loc st) (Loc l)) Unit)
      ={E}=> j ⤇ fill K (InjL Unit) ★ st ↦ₛ FoldV (InjLV UnitV) ★ l ↦ₛ (♭v false).
  Proof.
    iIntros {HNE} "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_pop.
    iPvs (steps_with_lock _ _ _ j K _ _ _ _ (InjLV UnitV) UnitV _ _
          with "[Hj Hx Hl]") as "Hj"; last done.
    - iIntros {K'} "[#Hspec [Hx Hj]]". simpl.
      iApply steps_CG_pop_fail; first done. iFrame "Hspec Hj Hx"; trivial.
    - iFrame "Hspec Hj Hx"; trivial.
      Unshelve. all: trivial.
  Qed.

  Global Opaque CG_locked_pop.

  Definition CG_snap (st l : expr) :=
    with_lock (Lam (Load st.[ren (+2)])) l.
  Definition CG_snapV (st l : expr) : val :=
    with_lockV (Lam (Load st.[ren (+2)])) l.

  Lemma CG_snap_to_val st l :
    to_val (CG_snap st l) = Some (CG_snapV st l).
  Proof. trivial. Qed.

  Lemma CG_snap_of_val st l :
    of_val (CG_snapV st l) = CG_snap st l.
  Proof. trivial. Qed.

  Global Opaque CG_snapV.

  Lemma CG_snap_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_snap st l) (TArrow TUnit (CG_StackType τ)).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; trivial. do 2 constructor.
    eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma CG_snap_closed (st l : expr) :
    (∀ f, st.[f] = st) → (∀ f, l.[f] = l) →
    ∀ f, (CG_snap st l).[f] = CG_snap st l.
  Proof.
    intros H1 H2 f. asimpl. unfold CG_snap.
    rewrite with_lock_closed; trivial.
    intros f'. by asimpl; rewrite ?H1.
  Qed.

  Lemma CG_snap_subst (st l : expr) f :
    (CG_snap st l).[f] = CG_snap st.[f] l.[f].
  Proof. unfold CG_snap; rewrite ?with_lock_subst. by asimpl. Qed.

  Lemma steps_CG_snap N E ρ j K st v l :
    nclose N ⊆ E →
    Spec_ctx N ρ ★ st ↦ₛ v ★ l ↦ₛ (♭v false)
               ★ j ⤇ fill K (App (CG_snap (Loc st) (Loc l)) Unit)
      ={E}=> j ⤇ (fill K (# v)) ★ st ↦ₛ v ★ l ↦ₛ (♭v false).
  Proof.
    iIntros {HNE} "[#Hspec [Hx [Hl Hj]]]". unfold CG_snap.
    iPvs (steps_with_lock _ _ _ j K _ _ _ _ v UnitV _ _
          with "[Hj Hx Hl]") as "Hj"; last done; [|by iFrame "Hspec Hx Hl Hj"].
    iIntros {K'} "[#Hspec [Hx Hj]]".
    iPvs (step_lam _ _ _ j K' _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iPvs (step_load _ _ _ j K' _ _ _ _
          with "[Hj Hx]") as "[Hj Hx]"; eauto.
    - by iFrame "Hspec Hj Hx".
    - iPvsIntro. by iFrame "Hj Hx".
      Unshelve.
      all: try match goal with |- to_val _ = _ => simpl; by rewrite ?to_of_val end.
      all: trivial.
  Qed.

  Global Opaque CG_snap.

  (* Coarse-grained iter *)
  Definition CG_iter (f : expr) : expr :=
    Lam (Case (Unfold (Var 1))
              Unit
              (
                App (Lam (App (Var 3) (Snd (Var 2))))
                    (App f.[ren (+3)] (Fst (Var 0)))
              )
        ).

  Lemma CG_iter_folding (f : expr) :
    CG_iter f =
    Lam (Case (Unfold (Var 1))
              Unit
              (
                App (Lam (App (Var 3) (Snd (Var 2))))
                    (App f.[ren (+3)] (Fst (Var 0)))
              )
        ).
  Proof. trivial. Qed.

  Lemma CG_iter_type f Γ τ :
    typed Γ f (TArrow τ TUnit) →
    typed Γ (CG_iter f) (TArrow (CG_StackType τ) TUnit).
  Proof.
    intros H1.
    econstructor.
    eapply (Case_typed _ _ _ _ TUnit);
      [| repeat constructor
       | repeat econstructor; eapply (context_weakening [_; _; _]); eauto].
    replace (TSum TUnit (TProd τ (CG_StackType τ))) with
    ((TSum TUnit (TProd τ.[ren (+1)] (TVar 0))).[(CG_StackType τ)/])
      by (by asimpl).
    repeat econstructor.
  Qed.

  Definition CG_iterV (f : expr) : val :=
    LamV (Case (Unfold (Var 1))
              Unit
              (
                App (Lam (App (Var 3) (Snd (Var 2))))
                    (App f.[ren (+3)] (Fst (Var 0)))
              )
        ).

  Lemma CG_iter_to_val f : to_val (CG_iter f) = Some (CG_iterV f).
  Proof. trivial. Qed.

  Lemma CG_iter_of_val f : of_val (CG_iterV f) = CG_iter f.
  Proof. trivial. Qed.

  Global Opaque CG_iterV.

  Lemma CG_iter_closed (f : expr) :
    (∀ g, f.[g] = f) → ∀ g, (CG_iter f).[g] = CG_iter f.
  Proof. intros H g. unfold CG_iter. asimpl. rewrite ?H; trivial. Qed.

  Lemma CG_iter_subst (f : expr) g :
  (CG_iter f).[g] = CG_iter f.[g].
  Proof. unfold CG_iter; asimpl; trivial. Qed.

  Lemma steps_CG_iter N E ρ j K f v w :
    nclose N ⊆ E →
    Spec_ctx N ρ
        ★ j ⤇ fill K (App (CG_iter (# f)) (Fold (InjR (Pair (# w) (# v)))))
      ={E}=>
    j ⤇ fill K
          (App
             (Lam
                (App ((CG_iter (# f)).[ren (+2)])
                     (Snd (Pair ((# w).[ren (+2)]) (# v).[ren (+2)]))))
             (App (# f) (# w))).
  Proof.
    iIntros {HNE} "[#Hspec Hj]". unfold CG_iter.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    rewrite -CG_iter_folding. Opaque CG_iter. asimpl.
    iPvs (step_Fold _ _ _ j (K ++ [CaseCtx _ _])
                    _ _ _ with "[Hj]") as "Hj"; eauto.
    rewrite ?fill_app /=.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. asimpl.
    iPvs (step_case_inr _ _ _ j K _ _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iPvs (step_fst _ _ _ j (K ++ [AppRCtx (LamV _); AppRCtx f]) _ _ _ _
                   _ _ with "[Hj]") as "Hj"; eauto.
    rewrite ?fill_app /=.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    by iPvsIntro.
    Unshelve.
    all: try match goal with |- to_val _ = _ => simpl; by rewrite ?to_of_val end.
  Qed.

  Transparent CG_iter.

  Lemma steps_CG_iter_end N E ρ j K f :
    nclose N ⊆ E →
    Spec_ctx N ρ ★ j ⤇ fill K (App (CG_iter (# f)) (Fold (InjL Unit)))
      ={E}=> j ⤇ fill K Unit.
  Proof.
    iIntros {HNE} "[#Hspec Hj]". unfold CG_iter.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    rewrite -CG_iter_folding. Opaque CG_iter. asimpl.
    iPvs (step_Fold _ _ _ j (K ++ [CaseCtx _ _])
                    _ _ _ with "[Hj]") as "Hj"; eauto.
    rewrite ?fill_app /=.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. asimpl.
    iPvs (step_case_inl _ _ _ j K _ _ _ _ _ with "[Hj]") as "Hj"; eauto.
    Unshelve.
    all: try match goal with |- to_val _ = _ => simpl; by rewrite ?to_of_val end.
  Qed.

  Global Opaque CG_iter.

  Definition CG_snap_iter (st l : expr) : expr :=
    Lam (App (CG_iter (Var 1)) (App (CG_snap st.[ren (+2)] l.[ren (+2)]) Unit)).

  Lemma CG_snap_iter_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_snap_iter st l)
          (TArrow (TArrow τ TUnit) TUnit).
  Proof.
    intros H1 H2; repeat econstructor.
    - eapply CG_iter_type; by constructor.
    - eapply CG_snap_type; by eapply (context_weakening [_;_]).
  Qed.

  Lemma CG_snap_iter_closed (st l : expr) :
    (∀ f, st.[f] = st) →
    (∀ f, l.[f] = l) →
    ∀ f, (CG_snap_iter st l).[f] = CG_snap_iter st l.
  Proof.
    intros H1 H2 f. unfold CG_snap_iter. asimpl. rewrite H1 H2.
    rewrite CG_snap_closed; auto.
  Qed.

  Lemma CG_snap_iter_subst (st l : expr) g :
  (CG_snap_iter st l).[g] = CG_snap_iter st.[g] l.[g].
  Proof.
    unfold CG_snap_iter; asimpl.
    rewrite CG_snap_subst CG_iter_subst. by asimpl.
  Qed.

  Definition CG_stack_body (st l : expr) : expr :=
    Pair (Pair (CG_locked_push st l) (CG_locked_pop st l))
         (CG_snap_iter st l).

  Lemma CG_stack_body_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_stack_body st l)
          (TProd
             (TProd (TArrow τ TUnit) (TArrow TUnit (TSum TUnit τ)))
             (TArrow (TArrow τ TUnit) TUnit)
          ).
  Proof.
    intros H1 H2.
    repeat (econstructor; eauto using CG_locked_push_type,
                          CG_locked_pop_type, CG_snap_iter_type).
  Qed.

  Opaque CG_snap_iter.

  Lemma CG_stack_body_closed (st l : expr) :
    (∀ f, st.[f] = st) →
    (∀ f, l.[f] = l) →
    ∀ f, (CG_stack_body st l).[f] = CG_stack_body st l.
  Proof.
    intros H1 H2 f. unfold CG_stack_body. asimpl.
    rewrite CG_locked_push_closed; trivial.
    rewrite CG_locked_pop_closed; trivial.
    by rewrite CG_snap_iter_closed.
  Qed.

  Definition CG_stack : expr :=
    TLam (App (Lam (App (Lam (CG_stack_body (Var 1) (Var 3)))
                  (Alloc (Fold (InjL Unit))))) newlock).

  Lemma CG_stack_type Γ :
    typed Γ (CG_stack)
          (TForall
             (TProd
                (TProd
                   (TArrow (TVar 0) TUnit)
                   (TArrow TUnit (TSum TUnit (TVar 0)))
                )
                (TArrow (TArrow (TVar 0) TUnit) TUnit)
          )).
  Proof.
    repeat econstructor.
    - eapply CG_locked_push_type; constructor; simpl; eauto.
    - eapply CG_locked_pop_type; constructor; simpl; eauto.
    - eapply CG_snap_iter_type; constructor; by simpl.
    - asimpl. repeat constructor.
    - eapply newlock_type.
  Qed.

  Lemma CG_stack_closed f :
    CG_stack.[f] = CG_stack.
  Proof.
    unfold CG_stack.
    asimpl; rewrite ?CG_locked_push_subst ?CG_locked_pop_subst.
    asimpl. rewrite ?CG_snap_iter_subst. by asimpl.
  Qed.

  Transparent CG_snap_iter.
End CG_Stack.
