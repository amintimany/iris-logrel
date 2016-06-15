From iris.proofmode Require Import invariants ghost_ownership tactics.
From iris.program_logic Require Import auth namespaces.
From iris_logrel.F_mu_ref_par Require Import lang examples.lock
     examples.stack.CG_stack examples.stack.FG_stack examples.stack.stack_rules
     typing logrel_binary fundamental_binary rules_binary rules
context_refinement soundness_binary.
Import uPred.

Section Stack_refinement.
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
    iIntros {τi}. destruct τi as [τi Hτ]; simpl.
    iAlways. clear j K. iIntros {j K} "Hj".
    iPvs (step_Tlam _ _ _ j K with "[Hj]")
      as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial.
    iApply wp_TLam; iNext.
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
          iApply wp_if_false. iNext. by iApply "Hlat".
      + (* refinement of pop *)
        iAlways. clear j K. iIntros {j K v}. destruct v as [v1 v2].
        iIntros "[#Hrel Hj]". simpl.
        iDestruct "Hrel" as "[% %]". subst.
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
        iApply wp_pvs.
        iApply (wp_load _ _ _ _ _ _ _). iFrame "Hheap Hstk".
        iNext. iIntros "Hstk".
        (* Checking whether the stack is empty *)
        iDestruct (StackLink_dup with "[HLK]") as "[HLK HLK']"; trivial.
        rewrite -> StackLink_unfold at 2.
        iDestruct "HLK'" as {istk2 w} "[HH [Hmpt HLK']]".
        iDestruct "HH" as %HH. inversion HH; simpl in *; subst.
        iDestruct "HLK'" as "[[% %]|HLK']".
        * (* The stack is empty *)
          simpl in *; subst.
          iPvs (steps_CG_locked_pop_fail _ _ _ _ _ _ _ _ with "[Hj Hstk' Hl]")
            as "[Hj [Hstk' Hl]]".
          { by iFrame "Hspec Hstk' Hl Hj". }
          iPvsIntro.
          iSplitR "Hj Hmpt".
          { iNext. iExists _, _, _. by iFrame "Hoe Hstk' Hstk Hl". }
          iApply (@wp_bind _ _ _ [AppRCtx (LamV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
          iApply wp_Fold; simpl; auto using to_of_val.
          iNext. iApply wp_lam; auto using to_of_val. iNext. asimpl.
          clear h.
          iApply (@wp_bind _ _ _ [AppRCtx (LamV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
          iInv (N .@4) as {istk3 w h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
          iDestruct (stack_owns_later_open_close with "[Hmpt Hoe]")
            as "[Histk HLoe]".
          { by iFrame "Hmpt". }
          iApply (wp_load _ _ _ _ _ _ _). iFrame "Hheap Histk".
          iNext. iIntros "Histk".
          iSplitR "Hj".
          { iNext. iExists _, _, _. iFrame "Hstk' Hstk HLK Hl".
            iDestruct ("HLoe" with "[Histk]") as "[Hh _]"; trivial.
          }
          iApply wp_lam; simpl; trivial.
          iNext. asimpl.
          iApply wp_case_inl; trivial.
          iNext. iApply wp_value; simpl; trivial. iExists (InjLV UnitV).
          iSplit; trivial. iLeft. iExists (_, _); repeat iSplit; simpl; trivial.
        * (* The stack is not empty *)
          iPvsIntro. iSplitR "Hj Hmpt HLK'".
          { iNext. iExists _, _, _. by iFrame "Hstk' Hstk HLK Hl". }
          iApply (@wp_bind _ _ _ [AppRCtx (LamV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w'} "Hw"; iExact "Hw"|].
          iApply wp_Fold; simpl; auto using to_of_val.
          iNext. iApply wp_lam; auto using to_of_val. iNext. asimpl.
          clear h.
          iApply (@wp_bind _ _ _ [AppRCtx (LamV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w'} "Hw"; iExact "Hw"|].
          iInv (N .@4) as {istk3 w' h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
          iDestruct (stack_owns_later_open_close with "[Hmpt Hoe]")
            as "[Histk HLoe]".
          { by iFrame "Hmpt". }
          iApply (wp_load _ _ _ _ _ _ _). iFrame "Hheap Histk".
          iNext. iIntros "Histk".
          iDestruct ("HLoe" with "[Histk]") as "[Hh Hmpt]"; trivial.
          iSplitR "Hj Hmpt HLK'".
          { iNext. iExists _, _, _. by iFrame "Hstk' Hstk HLK Hl". }
          iApply wp_lam; auto using to_of_val.
          iNext. asimpl.
          iDestruct "HLK'" as {y1 z1 y2 z2} "[% HLK']". subst. simpl.
          iApply wp_case_inr; [simpl; by rewrite ?to_of_val |].
          iNext.
          iApply (@wp_bind _ _ _ [IfCtx _ _; CasRCtx (LocV _) (FoldV (LocV _))]);
            iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
          asimpl. iApply wp_snd; [simpl; by rewrite ?to_of_val |
                                  simpl; by rewrite ?to_of_val |].
          simpl. iNext.
          iApply (@wp_bind _ _ _ [IfCtx _ _]);
            iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
          clear istk3 h. asimpl.
          iInv (N .@4) as {istk3 w h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
          { by simpl; rewrite ?to_of_val; simpl. }
          (* deciding whether CAS will succeed or fail *)
          destruct (decide (istk2 = istk3)) as [|Hneq]; subst.
          -- (* CAS succeeds *)
            (* In this case, the specification pushes *)
            iApply wp_pvs.
            iApply (wp_cas_suc _ _ _ _ _ _ _ _ _ _ _).
            iFrame "Hheap Hstk". iNext. iIntros "Hstk".
            iClear "HLK'".
            iDestruct (StackLink_dup with "[HLK]") as "[HLK HLK']"; trivial.
            rewrite -> StackLink_unfold at 2.
            iDestruct "HLK'" as {istk4 w2} "[HH [Hmpt' HLK']]".
            iDestruct "HH" as %HH'. inversion HH'; simpl in *; subst.
            iDestruct (stack_mapstos_agree with "[Hmpt Hmpt']")
              as "[Hmpt [Hmpt' %]]".
            { by iFrame "Hmpt Hmpt'". }
            subst.
            iDestruct "HLK'" as "[[Heq1 Heq2]|HLK']".
            ++ iDestruct "Heq1" as %Heq1. inversion Heq1.
            ++ iDestruct "HLK'" as {yn1 yn2 zn1 zn2}
                                     "[Heq1 [Heq2 [#Hrel HLK'']]]".
               iDestruct "Heq1" as %Heq1. iDestruct "Heq2" as %Heq2.
               inversion Heq1; subst.
               (* Now we have proven that specification can also pop. *)
               rewrite CG_locked_pop_of_val.
               iPvs (steps_CG_locked_pop_suc _ _ _ _ _ _ _ _ _ _
                     with "[Hj Hstk' Hl]") as "[Hj [Hstk' Hl]]".
               { by iFrame "Hspec Hstk' Hl Hj". }
               iPvsIntro. iSplitR "Hj".
               { iNext.
                 iClear "Hmpt Hmpt' HLK". rewrite StackLink_unfold.
                 iDestruct "HLK''" as {istk5 w2} "[% [Hmpt HLK]]".
                 simpl in *; subst.
                 iExists istk5, _, _. iFrame "Hoe Hstk' Hstk Hl".
                 rewrite StackLink_unfold.
                 iExists _, _; iSplitR; trivial.
                 by iFrame "HLK".
               }
               iApply wp_if_true. iNext.
               iApply (@wp_bind _ _ _ [InjRCtx]); iApply wp_wand_l;
                 iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
               iApply wp_fst; [simpl; by rewrite ?to_of_val |
                               simpl; by rewrite ?to_of_val |].
               iNext. iApply wp_value; simpl.
               { by rewrite to_of_val. }
               iExists (InjRV _); iFrame "Hj".
               iRight. iExists (_, _). iSplit; trivial.
          -- (* CAS will fail *)
            iApply (wp_cas_fail _ _ _ _ _ _ _ _ _ _ _ _ _ _).
            iFrame "Hheap Hstk". iNext. iIntros "Hstk".
            iSplitR "Hj".
            { iNext. iExists _, _, _. by iFrame "Hoe Hstk' Hstk HLK Hl". }
            iApply wp_if_false. iNext. by iApply "Hlat".
    - (* refinement of iter *)
      iAlways. clear j K. iIntros {j K f}. destruct f as [f1 f2]. simpl.
      iIntros "[#Hfs Hj]".
      iApply wp_lam; auto using to_of_val. iNext.
      iPvs (step_lam _ _ _ _ _ _ _ _ _ _ with "[Hj]") as "Hj".
      { by iFrame "Hspec Hj". }
      asimpl. rewrite FG_iter_subst CG_snap_subst CG_iter_subst. asimpl.
      replace (FG_iter (# f1)) with (# (FG_iterV (# f1)))
        by (by rewrite FG_iter_of_val).
      replace (CG_iter (# f2)) with (# (CG_iterV (# f2)))
        by (by rewrite CG_iter_of_val).
      iApply (@wp_bind _ _ _ [AppRCtx _]); iApply wp_wand_l;
        iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
      iInv (N .@4) as {istk3 w h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
      (* coarse-grained stack takes a snapshot *)
      iTimeless "Hstk'"; iTimeless "Hl".
      iPvs (steps_CG_snap _ _ _ _ (K ++ [AppRCtx _]) _ _ _ _
            with "[Hstk' Hj Hl]") as "[Hj [Hstk' Hl]]".
      { rewrite ?fill_app. simpl. by iFrame "Hspec Hstk' Hl Hj". }
      iApply (wp_load _ _ _ _ _ _ _).
      iFrame "Hheap Hstk". iNext. iIntros "Hstk".
      iDestruct (StackLink_dup with "HLK") as "[HLK HLK']".
      iSplitR "Hj HLK'".
      { iNext. iExists _, _, _; by iFrame "Hoe Hstk' Hstk HLK Hl". }
      clear h.
      rewrite ?fill_app. simpl.
      rewrite -FG_iter_folding.
      iRevert {istk3 w} "Hj HLK'". iLöb as "Hlat".
      iIntros {istk3 w} "Hj". iIntros "HLK". (* A bug in iIntros? *)
      rewrite -> FG_iter_folding at 1.
      iApply wp_lam; simpl; trivial.
      rewrite -FG_iter_folding. asimpl. rewrite FG_iter_subst.
      iNext.
      iApply (@wp_bind _ _ _ [CaseCtx _ _; LoadCtx]); iApply wp_wand_l;
        iSplitR; [iIntros {v} "Hw"; iExact "Hw"|].
      iApply wp_Fold; simpl; trivial.
      iNext. simpl.
      iApply (@wp_bind _ _ _ [CaseCtx _ _]); iApply wp_wand_l;
        iSplitR; [iIntros {v} "Hw"; iExact "Hw"|].
      rewrite -> StackLink_unfold at 1.
      iDestruct "HLK" as {istk4 v} "[Heq [Hmpt HLK']]".
      iDestruct "Heq" as %Heq. inversion Heq; subst.
      iInv (N .@4) as {istk5 v' h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
      iDestruct (stack_owns_later_open_close with "[Hmpt Hoe]")
            as "[Histk HLoe]".
      { by iFrame "Hmpt". }
      iApply wp_pvs.
      iApply (wp_load _ _ _ _ _ _ _). iFrame "Hheap Histk".
      iNext. iIntros "Histk".
      iDestruct ("HLoe" with "[Histk]") as "[Hh Hmpt]"; trivial.
      iDestruct "HLK'" as "[[Heq1 Heq2]|HLK']".
      * iDestruct "Heq1" as %Heq1. inversion Heq1.
        iDestruct "Heq2" as %Heq2. inversion Heq2.
        rewrite CG_iter_of_val.
        iPvs (steps_CG_iter_end _ _ _ _ _ _ _ with "[Hj]") as "Hj".
        { by iFrame "Hspec Hj". }
        iPvsIntro. iSplitR "Hj".
        { iNext. iExists _, _, _. by iFrame "Hh Hstk' Hstk HLK". }
        iApply wp_case_inl; trivial.
        iNext. iApply wp_value; trivial. iExists UnitV. iSplitL; trivial.
          by iSplit.
      * iDestruct "HLK'" as {yn1 yn2 zn1 zn2}
                              "[Heq1 [Heq2 [#Hrel HLK'']]]".
        iDestruct "Heq1" as %Heq1. inversion Heq1.
        iDestruct "Heq2" as %Heq2. inversion Heq2.
        rewrite CG_iter_of_val.
        iPvs (steps_CG_iter _ _ _ _ _ _ _ _ _ with "[Hj]") as "Hj".
        { by iFrame "Hspec Hj". }
        iPvsIntro. iSplitR "Hj HLK''".
        { iNext. iExists _, _, _. by iFrame "Hh Hstk' Hstk HLK". }
        simpl.
        iApply wp_case_inr; simpl; rewrite ?to_of_val; trivial.
        rewrite FG_iter_subst CG_iter_subst. asimpl.
        iNext.
        iApply (@wp_bind _ _ _ [AppRCtx (LamV _); AppRCtx _]);
          iApply wp_wand_l; iSplitR; [iIntros {w'} "Hw"; iExact "Hw"|].
        iApply wp_fst; simpl; rewrite ?to_of_val; trivial. iNext.
        iApply (@wp_bind _ _ _ [AppRCtx (LamV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w'} "Hw"; iExact "Hw"|].
        rewrite -> StackLink_unfold at 1.
        iDestruct "HLK''" as {istk6 w'} "[% HLK]".
        simpl in *; subst.
        iSpecialize ("Hfs" $! _ (K ++ [AppRCtx (LamV _)]) (yn1, zn1)).
        rewrite fill_app; simpl.
        iApply wp_wand_l; iSplitR "Hj"; [|iApply "Hfs"; by iFrame "Hrel Hj"].
        iIntros {u}; simpl.
        iIntros "Hj". iDestruct "Hj" as {z} "[Hj [% %]]".
        rewrite fill_app; simpl. subst. asimpl.
        iPvs (step_lam _ _ _ _ _ _ _ _ _ _ with "[Hj]") as "Hj".
        { by iFrame "Hspec Hj". } asimpl. rewrite CG_iter_subst. asimpl.
        replace (CG_iter (# f2)) with (# (CG_iterV (# f2)))
          by (by rewrite CG_iter_of_val).
        iPvs (step_snd _ _ _ _ (K ++ [AppRCtx _]) _ _ _ _ _ _ _ with "[Hj]")
          as "Hj".
        { rewrite fill_app; simpl. by iFrame "Hspec Hj". }
        rewrite fill_app; simpl.
        iApply wp_lam; simpl; trivial.
        iNext. rewrite FG_iter_subst. asimpl.
        replace (FG_iter (# f1)) with (# (FG_iterV (# f1)))
          by (by rewrite FG_iter_of_val).
        iApply (@wp_bind _ _ _ [AppRCtx _]);
          iApply wp_wand_l; iSplitR; [iIntros {w''} "Hw"; iExact "Hw"|].
        iApply (wp_snd _ _ _ _ _ _); auto using to_of_val.
        simpl. iNext. rewrite -FG_iter_folding.
        iSpecialize ("Hlat" $! istk6 zn2).
        iApply ("Hlat" with "[Hj] [HLK]"); trivial.
        rewrite -> StackLink_unfold at 2.
        iExists _, _; iSplitR; trivial.
        Unshelve.
        all: try match goal with
                   |- to_val _ = _ => simpl; by rewrite ?to_of_val
                 end.
        all: trivial.
        all: try match goal with
                   |- _ ≠ _ => let H := fresh "H" in intros H; inversion H; auto
                 end.
        (* This seems to be a bug in all: mechanism!? *)
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
        match goal with
          |- @subseteq
              _ _ (nclose (N .@ ?A))
              (@difference _ _ ⊤ (nclose (N .@ ?B))) =>
          abstract (prove_disj N A B)
        end.
  Qed.

End Stack_refinement.

Definition Σ := #[authGF heapR; authGF cfgR; authGF stackR].

Theorem stack_context_refinement :
  context_refines
    [] FG_stack CG_stack
    (TForall
       (TProd
          (TProd
             (TArrow (TVar 0) TUnit)
             (TArrow TUnit (TSum TUnit (TVar 0)))
          )
          (TArrow (TArrow (TVar 0) TUnit) TUnit)
       )
    ).
Proof.
  eapply (@Binary_Soundness Σ);
    eauto using FG_stack_closed, CG_stack_closed.
  all: try typeclasses eauto.
  intros. apply FG_CG_counter_refinement.
Qed.