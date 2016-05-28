From iris.proofmode Require Import invariants ghost_ownership tactics.
From iris.program_logic Require Import auth namespaces.
From iris_logrel.F_mu_ref_par Require Import lang examples.lock
     examples.stack.CG_stack examples.stack.FG_stack examples.stack.stack_rules
     typing logrel_binary fundamental_binary rules_binary rules.
Import uPred.

Section CG_Counter.
  Context {Σ : gFunctors} {iS : cfgSG Σ} {iI : heapIG Σ}
          {iSTK : authG lang Σ stackR}.

  Ltac prove_disj N n n' :=
    let Hneq := fresh "Hneq" in
    let Hdsj := fresh "Hdsj" in
    assert (Hneq : n ≠ n') by omega;
    set (Hdsj := ndot_ne_disjoint N n n' Hneq); set_solver_ndisj.

  Lemma FG_CG_counter_refinement N Δ
        {HΔ : context_interp_Persistent Δ}
    :
      (@bin_log_related _ _ _ N Δ [] FG_stack CG_stack
                        (TForall
                           (TProd
                              (TProd
                                 (TArrow (TVar 0) TUnit)
                                 (TArrow TUnit (TSum TUnit (TVar 0)))
                              )
                              (TArrow (TArrow (TVar 0) TUnit) TUnit)
                        )) HΔ).
  Proof.
    (* executing the preambles *)
    intros vs Hlen. destruct vs; [|inversion Hlen].
    cbn -[FG_stack CG_stack].
    intros ρ j K. iIntros "[#Hheap [#Hspec [_ Hj]]]".
    rewrite ?empty_env_subst.
    unfold CG_stack, FG_stack.
    iApply wp_value; eauto.
    iExists (TLamV _); iFrame "Hj".
    iExists (_, _); iSplit; eauto.
    iIntros {τi}. destruct τi as [τi Hτ]; simpl.
    iAlways. iNext. clear j K. iIntros {j K} "Hj".
    iPvs (steps_newlock _ _ _ j (K ++ [AppRCtx (LamV _)]) _ with "[Hj]")
      as {l} "[Hj Hl]"; eauto.
    rewrite fill_app; simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite fill_app; simpl.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. simpl.
    rewrite CG_locked_push_subst CG_locked_pop_subst
            CG_iter_subst CG_snap_subst. simpl. asimpl.
    iPvs (step_alloc _ _ _ j (K ++ [AppRCtx (LamV _)]) _ _ _ _ with "[Hj]")
      as {stk'} "[Hj Hstk']"; eauto.
    rewrite fill_app; simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite fill_app; simpl.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. simpl.
    rewrite CG_locked_push_subst CG_locked_pop_subst
            CG_iter_subst CG_snap_subst. simpl. asimpl.
    Unshelve.
    all: try match goal with |- to_val _ = _ => auto using to_of_val end.
    all: trivial.
    iApply (@wp_bind _ _ _ [AppRCtx (LamV _); AllocCtx; FoldCtx]);
      iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
    iApply wp_alloc; trivial; iFrame "Hheap"; iNext; iIntros {istk} "Histk".
    iApply (@wp_bind _ _ _ [AppRCtx (LamV _)]);
      iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
    iApply wp_alloc; trivial; iFrame "Hheap"; iNext; iIntros {stk} "Hstk".
    simpl. iApply wp_lam; trivial. iNext. simpl.
    rewrite FG_push_subst FG_pop_subst FG_iter_subst. simpl. asimpl.
    (* establishing the invariant *)
    iPvs (own_alloc (● (∅ : stackR))) as "Hemp".
    { constructor; eauto. eapply cmra_unit_valid. }
    iDestruct "Hemp" as {γ} "Hemp".
    set (istkG := StackG _ _ γ).
    change γ with (@stack_name _ istkG).
    change iSTK with (@stack_inG _ istkG).
    clearbody istkG. clear γ.
    iAssert (@stack_owns _ istkG _ ∅) as "Hoe" with "[Hemp]".
    { unfold stack_owns; rewrite big_sepM_empty; iFrame "Hemp"; trivial. }
    iPvs (stack_owns_alloc ⊤ _ _ _ with "[Hoe Histk]") as "[Hoe Hls]".
    { by iFrame "Hoe Histk". }
    iAssert (StackLink τi (LocV istk, FoldV (InjLV UnitV)))
      as "HLK" with "[Hls]".
    { rewrite StackLink_unfold.
      iExists _, _. iSplitR; simpl; trivial.
      iFrame "Hls". iLeft. iSplit; trivial.
    }
    iAssert ((∃ istk v h, (stack_owns h)
                         ★ stk' ↦ₛ v
                         ★ stk ↦ᵢ (FoldV (LocV istk))
                         ★ StackLink τi (LocV istk, v)
                         ★ l ↦ₛ (♭v false)
             )%I) as "Hinv" with "[Hoe Hstk Hstk' HLK Hl]".
    { iExists _, _, _. by iFrame "Hoe Hstk' Hstk Hl HLK". }
    iPvs (inv_alloc (N .@ 4) with "[Hinv]") as "#Hinv"; trivial.
    { iNext; iExact "Hinv". }
    clear istk.
    Opaque stack_owns.
    (* splitting *)
    iApply wp_value; simpl; trivial.
    iExists (PairV (PairV (CG_locked_pushV _ _) (CG_locked_popV _ _)) (LamV _)).
    simpl. rewrite CG_locked_push_of_val CG_locked_pop_of_val. iFrame "Hj".
    iExists (_, _), (_, _); iSplit; eauto.
    iSplit.
    (* refinement of push and pop *)
    - iExists (_, _), (_, _); iSplit; eauto. iSplit.
      + (* refinement of push *)
        iAlways. clear j K. iIntros {j K v}. destruct v as [v1 v2].
        iIntros "[#Hrel Hj]". simpl.
        rewrite -(FG_push_folding (Loc stk)).
        iLöb as "Hlat".
        rewrite -> (FG_push_folding (Loc stk)) at 2.
        iApply wp_lam; auto using to_of_val.
        iNext.
        rewrite -(FG_push_folding (Loc stk)).
        asimpl.
        iApply (@wp_bind _ _ _ [AppRCtx (LamV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
        iInv (N .@4) as {istk v h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
        iApply (wp_load _ _ _ _ _ _ _). iFrame "Hheap Hstk".
        iNext. iIntros "Hstk".
        iSplitL "Hoe Hstk' HLK Hl Hstk".
        iNext. iExists _, _, _; by iFrame "Hoe Hstk' HLK Hl Hstk".
        clear v h.
        iApply wp_lam; auto using to_of_val.
        iNext. asimpl.
        iApply (@wp_bind _ _ _ [IfCtx _ _; CasRCtx (LocV _) (FoldV (LocV _));
                                FoldCtx]);
          iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
        iApply wp_alloc; simpl; trivial; [by rewrite to_of_val|].
        iFrame "Hheap". iNext. iIntros {ltmp} "Hltmp".
        iApply (@wp_bind _ _ _ [IfCtx _ _]);
          iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
        iInv (N .@4) as {istk2 v h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
        (* deciding whether CAS will succeed or fail *)
        destruct (decide (istk = istk2)) as [|Hneq]; subst.
        * (* CAS succeeds *)
          (* In this case, the specification pushes *)
          iTimeless "Hstk'". iTimeless "Hl".
          iPvs (steps_CG_locked_push _ _ _ j K _ _ _ _ _ with "[Hj Hl Hstk']")
            as "[Hj [Hstk' Hl]]".
          { rewrite CG_locked_push_of_val. by iFrame "Hspec Hstk' Hj". }
          iApply wp_pvs.
          iApply (wp_cas_suc _ _ _ _ _ _ _ _ _ _ _); simpl; trivial.
          iFrame "Hheap Hstk". iNext. iIntros "Hstk".
          iSplitR "Hj".
          { iPvs (stack_owns_alloc with "[Hoe Hltmp]") as "[Hoe Hpt]".
            { by iFrame "Hoe". }
            iPvsIntro. iNext. iExists ltmp, _, _.
            iFrame "Hoe Hstk' Hstk Hl".
            do 2 rewrite StackLink_unfold.
            rewrite -StackLink_unfold.
            iExists _, _. iSplit; trivial.
            iFrame "Hpt". iRight. iExists _, _, _, _.
            repeat iSplitR; trivial.
            iNext; trivial.
          }
          iPvsIntro.
          iApply wp_if_true. iNext; iApply wp_value; trivial.
          iExists UnitV. iFrame "Hj"; by iSplit.
        * iApply (wp_cas_fail _ _ _ _ _ _ _ _ _ _ _ _ _ _); simpl; trivial.
          iFrame "Hheap Hstk". iNext. iIntros "Hstk".
          iSplitR "Hj".
          { iNext. iExists _, _, _. by iFrame "Hoe Hstk' Hstk Hl". }
          iApply wp_if_false. iNext. iApply "Hlat". by iNext.
      + (* refinement of pop *)
        iAlways. clear j K. iIntros {j K v}. destruct v as [v1 v2].
        iIntros "[#Hrel Hj]". simpl.
        iTimeless "Hrel". iDestruct "Hrel" as "[% %]". subst.
        rewrite -(FG_pop_folding (Loc stk)).
        iLöb as "Hlat".
        rewrite -> (FG_pop_folding (Loc stk)) at 2.
        iApply wp_lam; auto using to_of_val.
        iNext.
        rewrite -(FG_pop_folding (Loc stk)).
        asimpl.
        iApply (@wp_bind _ _ _ [AppRCtx (LamV _); UnfoldCtx]);
          iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
        iInv (N .@4) as {istk v h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
        iApply (wp_load _ _ _ _ _ _ _). iFrame "Hheap Hstk".
        iNext. iIntros "Hstk".
        iDestruct (StackLink_dup with "[HLK]") as "[HLK HLK']"; trivial.
        iSplitL "Hoe Hstk' HLK Hl Hstk".
        iNext. iExists _, _, _; by iFrame "Hoe Hstk' HLK Hl Hstk".
        clear h.
        iApply (@wp_bind _ _ _ [AppRCtx (LamV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
        iApply wp_Fold; simpl; auto using to_of_val.
        iNext. iApply wp_lam; auto using to_of_val. iNext. asimpl.
        iApply (@wp_bind _ _ _ [AppRCtx (LamV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
        iInv (N .@4) as {istk2 w h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
        iAssert ((▷ ∃ w, istk ↦ᵢ w ★ (istk ↦ᵢ w -★ stack_owns h))%I)
          as "Hpromise" with "[HLK' Hoe]".
        { iNext.
          rewrite StackLink_unfold.
          iDestruct "HLK'" as {istk3 w2} "[Heq [Hpt HLK']]".
          iDestruct "Heq" as %Heq. simpl in Heq; inversion Heq; subst.
          iDestruct (stack_owns_open with "[Hoe Hpt]")
            as "[Hh [Hm [Histk Hpt]]]".
          { by iFrame "Hoe Hpt". }
          iExists _. iFrame "Histk". iIntros "Histk".
          iSplitL "Histk".
          - iExists _; by iFrame "Histk".
          - iDestruct (stack_owns_close with "[Hh Hm Hpt]") as "Howns".
            { iFrame "Hh Hm" }



          
        iApply (wp_load _ _ _ _ _ _ _). iFrame "Hheap".
        iNext.
        rewrite StackLink_unfold.
        iDestruct "HLK'" as {istk3 w2} "[Heq [Hpt HLK']]".
        iDestruct "Heq" as %Heq. simpl in Heq; inversion Heq; subst.
        iDestruct (stack_owns_open with "[Hoe Hpt]") as "[Hh [Hm [Histk3 Hpt]]]".
        { by iFrame "Hoe Hpt". }
        iFrame "Histk3".


        
        iApply wp_load; simpl; auto using to_of_val.

        
        iApply (@wp_bind _ _ _ [IfCtx _ _; CasRCtx (LocV _) (FoldV (LocV _));
                                FoldCtx]);
          iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
        iApply wp_alloc; simpl; trivial; [by rewrite to_of_val|].
        iFrame "Hheap". iNext. iIntros {ltmp} "Hltmp".
        iApply (@wp_bind _ _ _ [IfCtx _ _]);
          iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
        iInv (N .@4) as {istk2 v h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
        (* deciding whether CAS will succeed or fail *)
        destruct (decide (istk = istk2)) as [|Hneq]; subst.
        * (* CAS succeeds *)
          (* In this case, the specification pushes *)
          iTimeless "Hstk'". iTimeless "Hl".
          iPvs (steps_CG_locked_push _ _ _ j K _ _ _ _ _ with "[Hj Hl Hstk']")
            as "[Hj [Hstk' Hl]]".
          { rewrite CG_locked_push_of_val. by iFrame "Hspec Hstk' Hj". }
          iApply wp_pvs.
          iApply (wp_cas_suc _ _ _ _ _ _ _ _ _ _ _); simpl; trivial.
          iFrame "Hheap Hstk". iNext. iIntros "Hstk".
          iSplitR "Hj".
          { iPvs (stack_owns_alloc with "[Hoe Hltmp]") as "[Hoe Hpt]".
            { by iFrame "Hoe". }
            iPvsIntro. iNext. iExists ltmp, _, _.
            iFrame "Hoe Hstk' Hstk Hl".
            do 2 rewrite StackLink_unfold.
            rewrite -StackLink_unfold.
            iExists _, _. iSplit; trivial.
            iFrame "Hpt". iRight. iExists _, _, _, _.
            repeat iSplitR; trivial.
            iNext; trivial.
          }
          iPvsIntro.
          iApply wp_if_true. iNext; iApply wp_value; trivial.
          iExists UnitV. iFrame "Hj"; by iSplit.
        * iApply (wp_cas_fail _ _ _ _ _ _ _ _ _ _ _ _ _ _); simpl; trivial.
          iFrame "Hheap Hstk". iNext. iIntros "Hstk".
          iSplitR "Hj".
          { iNext. iExists _, _, _. by iFrame "Hoe Hstk' Hstk Hl". }
          iApply wp_if_false. iNext. iApply "Hlat". by iNext.






















        
