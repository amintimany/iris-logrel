From iris.program_logic Require Import auth.
From iris_logrel.F_mu_ref_conc Require Import soundness_binary.
From iris_logrel.F_mu_ref_conc.examples Require Import lock.
From iris_logrel.F_mu_ref_conc.examples.stack Require Import
  CG_stack FG_stack stack_rules.
From iris.proofmode Require Import invariants ghost_ownership tactics.

Definition stackN : namespace := nroot .@ "stack".

Section Stack_refinement.
  Context `{cfgSG Σ, heapIG Σ, authG lang Σ stackUR}.
  Notation D := (prodC valC valC -n> iPropG lang Σ).
  Implicit Types Δ : listC D.

  Lemma FG_CG_counter_refinement :
    [] ⊨ FG_stack ≤log≤ CG_stack : TForall (TProd (TProd
           (TArrow (TVar 0) TUnit)
           (TArrow TUnit (TSum TUnit (TVar 0))))
           (TArrow (TArrow (TVar 0) TUnit) TUnit)).
  Proof.
    (* executing the preambles *)
    iIntros { Δ [|??] ρ ? } "#(Hheap & Hspec & HΓ)"; iIntros {j K} "Hj"; last first.
    { iDestruct (interp_env_length with "HΓ") as %[=]. } 
    iClear "HΓ". cbn -[FG_stack CG_stack].
    rewrite ?empty_env_subst /CG_stack /FG_stack.
    iApply wp_value; eauto.
    iExists (TLamV _); iFrame "Hj".
    clear j K. iAlways. iIntros {τi} "%". iIntros {j K} "Hj /=".
    iPvs (step_tlam _ _ j K with "[Hj]") as "Hj"; eauto.
    iApply wp_tlam; iNext.
    iPvs (steps_newlock _ _ j (K ++ [AppRCtx (RecV _)]) _ with "[Hj]")
      as {l} "[Hj Hl]"; eauto.
    { rewrite fill_app; simpl. iFrame "Hspec Hj"; trivial. }
    rewrite fill_app; simpl.
    iPvs (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    simpl.
    rewrite CG_locked_push_subst CG_locked_pop_subst
            CG_iter_subst CG_snap_subst. simpl. asimpl.
    iPvs (step_alloc  _ _ j (K ++ [AppRCtx (RecV _)]) _ _ _ _ with "[Hj]")
      as {stk'} "[Hj Hstk']"; eauto.
    rewrite fill_app; simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite fill_app; simpl.
    iPvs (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    simpl.
    rewrite CG_locked_push_subst CG_locked_pop_subst
            CG_iter_subst CG_snap_subst. simpl. asimpl.
    Unshelve.
    all: try match goal with |- to_val _ = _ => auto using to_of_val end.
    all: trivial.
    iApply (@wp_bind _ _ _ [AppRCtx (RecV _); AllocCtx; FoldCtx]);
      iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
    iApply wp_alloc; trivial; iFrame "Hheap"; iNext; iIntros {istk} "Histk".
    iPvsIntro. iApply (@wp_bind _ _ _ [AppRCtx (RecV _)]);
      iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
    iApply wp_alloc; trivial; iFrame "Hheap"; iNext; iIntros {stk} "Hstk".
    simpl. iApply wp_rec; trivial. iPvsIntro. iNext. simpl.
    rewrite FG_push_subst FG_pop_subst FG_iter_subst. simpl. asimpl.
    (* establishing the invariant *)
    iPvs (own_alloc (● (∅ : stackUR))) as {γ} "Hemp".
    { constructor; eauto. eapply ucmra_unit_valid. }
    set (istkG := StackG _ _ γ).
    change γ with (@stack_name _ istkG).
    change H1 with (@stack_inG _ istkG).
    clearbody istkG. clear γ.
    iAssert (@stack_owns _ istkG _ ∅) with "[Hemp]" as "Hoe".
    { unfold stack_owns; rewrite big_sepM_empty; iFrame "Hemp"; trivial. }
    iPvs (stack_owns_alloc ⊤ _ _ _ with "[Hoe Histk]") as "[Hoe Hls]".
    { by iFrame "Hoe Histk". }
    iAssert (StackLink τi (LocV istk, FoldV (InjLV UnitV))) with "[Hls]" as "HLK".
    { rewrite StackLink_unfold.
      iExists _, _. iSplitR; simpl; trivial.
      iFrame "Hls". iLeft. iSplit; trivial.
    }
    iAssert ((∃ istk v h, (stack_owns h)
                         ★ stk' ↦ₛ v
                         ★ stk ↦ᵢ (FoldV (LocV istk))
                         ★ StackLink τi (LocV istk, v)
                         ★ l ↦ₛ (♭v false)
             )%I) with "[Hoe Hstk Hstk' HLK Hl]" as "Hinv".
    { iExists _, _, _. by iFrame "Hoe Hstk' Hstk Hl HLK". }
    iPvs (inv_alloc stackN with "[Hinv]") as "#Hinv"; trivial.
    { iNext; iExact "Hinv". }
    clear istk.
    Opaque stack_owns.
    (* splitting *)
    iApply wp_value; simpl; trivial.
    iExists (PairV (PairV (CG_locked_pushV _ _) (CG_locked_popV _ _)) (RecV _)).
    simpl. rewrite CG_locked_push_of_val CG_locked_pop_of_val. iFrame "Hj".
    iExists (_, _), (_, _); iSplit; eauto.
    iSplit.
    (* refinement of push and pop *)
    - iExists (_, _), (_, _); iSplit; eauto. iSplit.
      + (* refinement of push *)
        iAlways. clear j K. iIntros { [v1 v2] } "#Hrel". iIntros {j K} "Hj /=".
        rewrite -(FG_push_folding (Loc stk)).
        iLöb as "Hlat".
        rewrite {2}(FG_push_folding (Loc stk)).
        iApply wp_rec; auto using to_of_val.
        iNext.
        rewrite -(FG_push_folding (Loc stk)).
        asimpl.
        iApply (@wp_bind _ _ _ [AppRCtx (RecV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
        iInv stackN as {istk v h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
        iApply (wp_load _ _ _ _ _ _).
        iIntros "{$Hheap $Hstk} > Hstk". iPvsIntro.
        iSplitL "Hoe Hstk' HLK Hl Hstk".
        iNext. iExists _, _, _; by iFrame "Hoe Hstk' HLK Hl Hstk".
        clear v h.
        iApply wp_rec; auto using to_of_val.
        iNext. asimpl.
        iApply (@wp_bind _ _ _ [IfCtx _ _; CasRCtx (LocV _) (FoldV (LocV _));
                                FoldCtx]);
          iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
        iApply wp_alloc; simpl; trivial; [by rewrite to_of_val|].
        iFrame "Hheap". iNext. iIntros {ltmp} "Hltmp". iPvsIntro.
        iApply (@wp_bind _ _ _ [IfCtx _ _]);
          iApply wp_wand_l; iSplitR; [by iIntros {w} "$"|].
        iInv stackN as {istk2 v h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
        (* deciding whether CAS will succeed or fail *)
        destruct (decide (istk = istk2)) as [|Hneq]; subst.
        * (* CAS succeeds *)
          (* In this case, the specification pushes *)
          iTimeless "Hstk'". iTimeless "Hl".
          iPvs (steps_CG_locked_push _ _ j K _ _ _ _ _ with "[Hj Hl Hstk']")
            as "[Hj [Hstk' Hl]]".
          { rewrite CG_locked_push_of_val. by iFrame "Hspec Hstk' Hj". }
          iApply (wp_cas_suc _ _ _ _ _ _ _ _ _ _); simpl; trivial.
          iIntros "{$Hheap $Hstk} > Hstk". iSplitR "Hj".
          { iPvs (stack_owns_alloc with "[Hoe Hltmp]") as "[Hoe Hpt]".
            { by iFrame "Hoe". }
            iPvsIntro. iNext. iExists ltmp, _, _.
            iFrame "Hoe Hstk' Hstk Hl".
            do 2 rewrite StackLink_unfold.
            rewrite -StackLink_unfold.
            iExists _, _. iSplit; trivial.
            iFrame "Hpt". eauto 10. }
          iPvsIntro.
          iApply wp_if_true. iNext; iApply wp_value; trivial.
          iExists UnitV; eauto.
        * iApply (wp_cas_fail _ _ _ _ _ _ _ _ _ _ _ _ _); simpl; trivial.
          iIntros "{$Hheap $Hstk} > Hstk". iPvsIntro.
          iSplitR "Hj".
          { iNext. iExists _, _, _. by iFrame "Hoe Hstk' Hstk Hl". }
          iApply wp_if_false. iNext. by iApply "Hlat".
      + (* refinement of pop *)
        iAlways. clear j K. iIntros { [v1 v2] } "[% %]".
        iIntros {j K} "Hj /="; simplify_eq/=.
        rewrite -(FG_pop_folding (Loc stk)).
        iLöb as "Hlat".
        rewrite {2}(FG_pop_folding (Loc stk)).
        iApply wp_rec; auto using to_of_val.
        iNext.
        rewrite -(FG_pop_folding (Loc stk)).
        asimpl.
        iApply (@wp_bind _ _ _ [AppRCtx (RecV _); UnfoldCtx]);
          iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
        iInv stackN as {istk v h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
        iApply (wp_load _ _ _ _ _ _). iIntros "{$Hheap $Hstk} > Hstk".
        (* Checking whether the stack is empty *)
        iDestruct (StackLink_dup with "[HLK]") as "[HLK HLK']"; trivial.
        rewrite {2}StackLink_unfold.
        iDestruct "HLK'" as {istk2 w} "[% [Hmpt [[% %]|HLK']]]"; simplify_eq/=.
        * (* The stack is empty *)
          iPvs (steps_CG_locked_pop_fail _ _ _ _ _ _ _ with "[Hj Hstk' Hl]")
            as "[Hj [Hstk' Hl]]".
          { by iFrame "Hspec Hstk' Hl Hj". }
          iPvsIntro.
          iSplitR "Hj Hmpt".
          { iNext. iExists _, _, _. by iFrame "Hoe Hstk' Hstk Hl". }
          iApply (@wp_bind _ _ _ [AppRCtx (RecV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
          iApply wp_fold; simpl; auto using to_of_val.
          iNext. iPvsIntro. iApply wp_rec; auto using to_of_val. iNext. asimpl.
          clear h.
          iApply (@wp_bind _ _ _ [AppRCtx (RecV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
          iInv stackN as {istk3 w h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
          iDestruct (stack_owns_later_open_close with "[Hmpt Hoe]")
            as "[Histk HLoe]".
          { by iFrame "Hmpt". }
          iApply (wp_load _ _ _ _ _ _). iFrame "Hheap Histk".
          iIntros "> Histk". iPvsIntro. iSplitR "Hj".
          { iNext. iExists _, _, _. iFrame "Hstk' Hstk HLK Hl".
            iDestruct ("HLoe" with "[Histk]") as "[Hh _]"; trivial.
          }
          iApply wp_rec; simpl; trivial.
          iNext. asimpl.
          iApply wp_case_inl; trivial.
          iNext. iApply wp_value; simpl; trivial. iExists (InjLV UnitV).
          iSplit; trivial. iLeft. iExists (_, _); repeat iSplit; simpl; trivial.
        * (* The stack is not empty *)
          iPvsIntro. iSplitR "Hj Hmpt HLK'".
          { iNext. iExists _, _, _. by iFrame "Hstk' Hstk HLK Hl". }
          iApply (@wp_bind _ _ _ [AppRCtx (RecV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w'} "Hw"; iExact "Hw"|].
          iApply wp_fold; simpl; auto using to_of_val.
          iNext. iApply wp_rec; auto using to_of_val. iPvsIntro. iNext. asimpl.
          clear h.
          iApply (@wp_bind _ _ _ [AppRCtx (RecV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w'} "Hw"; iExact "Hw"|].
          iInv stackN as {istk3 w' h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
          iDestruct (stack_owns_later_open_close with "[Hmpt Hoe]")
            as "[Histk HLoe]".
          { by iFrame "Hmpt". }
          iApply (wp_load _ _ _ _ _ _). iFrame "Hheap Histk".
          iIntros "> Histk". iPvsIntro.
          iDestruct ("HLoe" with "[Histk]") as "[Hh Hmpt]"; trivial.
          iSplitR "Hj Hmpt HLK'".
          { iNext. iExists _, _, _. by iFrame "Hstk' Hstk HLK Hl". }
          iApply wp_rec; auto using to_of_val.
          iNext. asimpl.
          iDestruct "HLK'" as {y1 z1 y2 z2} "[% HLK']". subst. simpl.
          iApply wp_case_inr; [simpl; by rewrite ?to_of_val |].
          iNext.
          iApply (@wp_bind _ _ _ [IfCtx _ _; CasRCtx (LocV _) (FoldV (LocV _))]);
            iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
          asimpl. iApply wp_snd; [simpl; by rewrite ?to_of_val |
                                  simpl; by rewrite ?to_of_val |].
          simpl. iNext. iPvsIntro.
          iApply (@wp_bind _ _ _ [IfCtx _ _]);
            iApply wp_wand_l; iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
          clear istk3 h. asimpl.
          iInv stackN as {istk3 w h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
          { by simpl; rewrite ?to_of_val; simpl. }
          (* deciding whether CAS will succeed or fail *)
          destruct (decide (istk2 = istk3)) as [|Hneq]; subst.
          -- (* CAS succeeds *)
            (* In this case, the specification pushes *)
            iApply (wp_cas_suc _ _ _ _ _ _ _ _ _ _).
            iIntros "{$Hheap $Hstk} > Hstk {HLK'}".
            iDestruct (StackLink_dup with "[HLK]") as "[HLK HLK']"; trivial.
            rewrite {2}StackLink_unfold.
            iDestruct "HLK'" as {istk4 w2} "[% [Hmpt' HLK']]"; simplify_eq/=.
            iDestruct (stack_mapstos_agree with "[Hmpt Hmpt']")
              as "[Hmpt [Hmpt' %]]".
            { by iFrame "Hmpt Hmpt'". }
            iDestruct "HLK'" as "[[% %]|HLK']"; simplify_eq/=.
            iDestruct "HLK'" as {yn1 yn2 zn1 zn2}
                                   "[% [% [#Hrel HLK'']]]"; simplify_eq/=.
             (* Now we have proven that specification can also pop. *)
             rewrite CG_locked_pop_of_val.
             iPvs (steps_CG_locked_pop_suc _ _ _ _ _ _ _ _ _
                   with "[Hj Hstk' Hl]") as "[Hj [Hstk' Hl]]".
             { by iFrame "Hspec Hstk' Hl Hj". }
             iPvsIntro. iSplitR "Hj".
             { iIntros "{Hmpt Hmpt' HLK} >". rewrite StackLink_unfold.
               iDestruct "HLK''" as {istk5 w2} "[% [Hmpt HLK]]"; simplify_eq/=.
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
             iNext. iPvsIntro. iApply wp_value; simpl.
             { by rewrite to_of_val. }
             iExists (InjRV _); iFrame "Hj".
             iRight. iExists (_, _). iSplit; trivial.
          -- (* CAS will fail *)
            iApply (wp_cas_fail  _ _ _ _ _ _ _ _ _ _ _ _ _).
            iIntros "{$Hheap $Hstk} > Hstk". iPvsIntro. iSplitR "Hj".
            { iNext. iExists _, _, _. by iFrame "Hoe Hstk' Hstk HLK Hl". }
            iApply wp_if_false. iNext. by iApply "Hlat".
    - (* refinement of iter *)
      iAlways. clear j K. iIntros { [f1 f2] } "/= #Hfs". iIntros {j K} "Hj".
      iApply wp_rec; auto using to_of_val. iNext.
      iPvs (step_rec _ _ _ _ _ _ _ _ _ with "[Hj]") as "Hj".
      { by iFrame "Hspec Hj". }
      asimpl. rewrite FG_iter_subst CG_snap_subst CG_iter_subst. asimpl.
      replace (FG_iter (# f1)) with (# (FG_iterV (# f1)))
        by (by rewrite FG_iter_of_val).
      replace (CG_iter (# f2)) with (# (CG_iterV (# f2)))
        by (by rewrite CG_iter_of_val).
      iApply (@wp_bind _ _ _ [AppRCtx _]); iApply wp_wand_l;
        iSplitR; [iIntros {w} "Hw"; iExact "Hw"|].
      iInv stackN as {istk3 w h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
      (* coarse-grained stack takes a snapshot *)
      iTimeless "Hstk'"; iTimeless "Hl".
      iPvs (steps_CG_snap _ _ _ (K ++ [AppRCtx _]) _ _ _ _
            with "[Hstk' Hj Hl]") as "[Hj [Hstk' Hl]]".
      { rewrite ?fill_app. simpl. by iFrame "Hspec Hstk' Hl Hj". }
      iApply (wp_load _ _ _ _ _ _).
      iIntros "{$Hheap $Hstk} > Hstk". iPvsIntro.
      iDestruct (StackLink_dup with "HLK") as "[HLK HLK']".
      iSplitR "Hj HLK'".
      { iNext. iExists _, _, _; by iFrame "Hoe Hstk' Hstk HLK Hl". }
      clear h.
      rewrite ?fill_app /= -FG_iter_folding.
      iLöb {istk3 w} as "Hlat".
      rewrite {2}FG_iter_folding.
      iApply wp_rec; simpl; trivial.
      rewrite -FG_iter_folding. asimpl. rewrite FG_iter_subst.
      iNext.
      iApply (@wp_bind _ _ _ [CaseCtx _ _; LoadCtx]); iApply wp_wand_l;
        iSplitR; [iIntros {v} "Hw"; iExact "Hw"|].
      iApply wp_fold; simpl; trivial.
      iNext. iPvsIntro. simpl.
      iApply (@wp_bind _ _ _ [CaseCtx _ _]); iApply wp_wand_l;
        iSplitR; [iIntros {v} "Hw"; iExact "Hw"|].
      rewrite StackLink_unfold.
      iDestruct "HLK'" as {istk4 v} "[% [Hmpt HLK']]"; simplify_eq/=.
      iInv stackN as {istk5 v' h} "[Hoe [Hstk' [Hstk [HLK Hl]]]]".
      iDestruct (stack_owns_later_open_close with "[Hmpt Hoe]")
            as "[Histk HLoe]".
      { by iFrame "Hmpt". }
      iApply (wp_load _ _ _ _ _ _). iIntros "{$Hheap $Histk} > Histk".
      iDestruct ("HLoe" with "[Histk]") as "[Hh Hmpt]"; trivial.
      iDestruct "HLK'" as "[[% %]|HLK']"; simplify_eq/=.
      * rewrite CG_iter_of_val.
        iPvs (steps_CG_iter_end _ _ _ _ _ _ with "[Hj]") as "Hj".
        { by iFrame "Hspec Hj". }
        iPvsIntro. iSplitR "Hj".
        { iNext. iExists _, _, _. by iFrame "Hh Hstk' Hstk HLK". }
        iApply wp_case_inl; trivial.
        iNext. iApply wp_value; trivial. iExists UnitV; eauto.
      * iDestruct "HLK'" as {yn1 yn2 zn1 zn2}
                              "[% [% [#Hrel HLK'']]]"; simplify_eq/=.
        rewrite CG_iter_of_val.
        iPvs (steps_CG_iter _ _ _ _ _ _ _ _ with "[Hj]") as "Hj".
        { by iFrame "Hspec Hj". }
        iPvsIntro. iSplitR "Hj HLK''".
        { iNext. iExists _, _, _. by iFrame "Hh Hstk' Hstk HLK". }
        simpl.
        iApply wp_case_inr; simpl; rewrite ?to_of_val; trivial.
        rewrite FG_iter_subst CG_iter_subst. asimpl.
        iNext.
        iApply (@wp_bind _ _ _ [AppRCtx (RecV _); AppRCtx _]);
          iApply wp_wand_l; iSplitR; [iIntros {w'} "Hw"; iExact "Hw"|].
        iApply wp_fst; simpl; rewrite ?to_of_val; trivial. iNext. iPvsIntro.
        iApply (@wp_bind _ _ _ [AppRCtx (RecV _)]);
          iApply wp_wand_l; iSplitR; [iIntros {w'} "Hw"; iExact "Hw"|].
        rewrite StackLink_unfold.
        iDestruct "HLK''" as {istk6 w'} "[% HLK]"; simplify_eq/=.
        iSpecialize ("Hfs" $! (yn1, zn1) with "Hrel").
        iSpecialize ("Hfs" $! _ (K ++ [AppRCtx (RecV _)])).
        rewrite fill_app; simpl.
        iApply wp_wand_l; iSplitR "Hj"; [|iApply "Hfs"; by iFrame "Hj"].
        iIntros {u} "/="; iDestruct 1 as {z} "[Hj [% %]]".
        rewrite fill_app; simpl. subst. asimpl.
        iPvs (step_rec _ _ _ _ _ _ _ _ _ with "[Hj]") as "Hj".
        { by iFrame "Hspec Hj". } asimpl. rewrite CG_iter_subst. asimpl.
        replace (CG_iter (# f2)) with (# (CG_iterV (# f2)))
          by (by rewrite CG_iter_of_val).
        iPvs (step_snd _ _ _ (K ++ [AppRCtx _]) _ _ _ _ _ _ _ with "[Hj]")
          as "Hj".
        { rewrite fill_app; simpl. by iFrame "Hspec Hj". }
        rewrite fill_app; simpl.
        iApply wp_rec; simpl; trivial.
        iNext. rewrite FG_iter_subst. asimpl.
        replace (FG_iter (# f1)) with (# (FG_iterV (# f1)))
          by (by rewrite FG_iter_of_val).
        iApply (@wp_bind _ _ _ [AppRCtx _]);
          iApply wp_wand_l; iSplitR; [iIntros {w''} "Hw"; iExact "Hw"|].
        iApply (wp_snd _ _ _ _ _); auto using to_of_val.
        simpl. iNext. rewrite -FG_iter_folding.
        iApply ("Hlat" $! istk6 zn2 with "[Hj] [HLK]"); trivial.
        rewrite StackLink_unfold; eauto.
        Unshelve.
        all: try match goal with
                   |- to_val _ = _ => simpl; by rewrite ?to_of_val
                 end.
        all: trivial.
        all: try match goal with |- _ ≠ _ => congruence end.
        all: unfold heapN, specN, stackN, specN; solve_ndisj.
  Qed.
End Stack_refinement.

Theorem stack_ctx_refinement :
  [] ⊨ FG_stack ≤ctx≤ CG_stack : TForall (TProd (TProd
        (TArrow (TVar 0) TUnit)
        (TArrow TUnit (TSum TUnit (TVar 0))))
        (TArrow (TArrow (TVar 0) TUnit) TUnit)).
Proof.
  set (Σ := #[authGF heapUR; authGF cfgUR; authGF stackUR]).
  eapply (@binary_soundness Σ);
    eauto using FG_stack_closed, CG_stack_closed.
  all: try typeclasses eauto.
  intros. apply FG_CG_counter_refinement.
Qed.
