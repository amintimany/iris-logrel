From iris_logrel.F_mu_ref Require Export logrel.
From iris.proofmode Require Import tactics pviewshifts invariants.
From iris_logrel.F_mu_ref Require Import rules.
From iris.algebra Require Export upred_big_op.

Section typed_interp.
  Context `{heapG Σ}.
  Notation D := (valC -n> iPropG lang Σ).
  Implicit Types Δ : listC D.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (@wp_bind _ _ _ [ctx]);
    iApply wp_wand_l;
    iSplitL; [|iApply Hp; trivial]; [iIntros {v} Hv|iSplit; trivial]; cbn.

  Local Ltac value_case := iApply wp_value; [cbn; rewrite ?to_of_val; trivial|].

  Theorem fundamental Δ Γ vs e τ (HΔ : env_PersistentP Δ) :
    Γ ⊢ₜ e : τ →
    heap_ctx ∧ ⟦ Γ ⟧* Δ vs ⊢ ⟦ τ ⟧ₑ Δ e.[env_subst vs].
  Proof.
    intros Htyped; revert Δ vs HΔ.
    induction Htyped; iIntros {Δ vs HΔ} "#[Hheap HΓ] /=".
    - (* var *)
      iDestruct (interp_env_Some_l with "HΓ") as {v} "[% ?]"; first done.
      rewrite /env_subst. simplify_option_eq. by value_case.
    - (* unit *) by value_case.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) v "#Hv" IHHtyped1.
      smart_wp_bind (PairRCtx v) v' "# Hv'" IHHtyped2.
      value_case; eauto 10.
   - (* fst *)
      smart_wp_bind (FstCtx) v "# Hv" IHHtyped; cbn.
      iDestruct "Hv" as {w1 w2} "#[% [H2 H3]]"; subst.
      iApply wp_fst; eauto using to_of_val.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" IHHtyped; cbn.
      iDestruct "Hv" as {w1 w2} "#[% [H2 H3]]"; subst.
      iApply wp_snd; eauto using to_of_val.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHHtyped; cbn.
      value_case; eauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHHtyped; cbn.
      value_case; eauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v "#Hv" IHHtyped1; cbn.
      iDestruct (interp_env_length with "HΓ") as %?.
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as {w} "[% Hw]"; simplify_eq/=.
      + iApply wp_case_inl; auto 1 using to_of_val; asimpl. iNext.
        erewrite typed_subst_head_simpl by naive_solver.
        iApply (IHHtyped2 Δ (w :: vs)). iSplit; [|iApply interp_env_cons]; auto.
      + iApply wp_case_inr; auto 1 using to_of_val; asimpl. iNext.
        erewrite typed_subst_head_simpl by naive_solver.
        iApply (IHHtyped3 Δ (w :: vs)). iSplit; [|iApply interp_env_cons]; auto.
    - (* lam *)
      value_case; iAlways; iIntros {w} "#Hw".
      iDestruct (interp_env_length with "HΓ") as %?.
      iApply wp_lam; auto 1 using to_of_val. iNext.
      asimpl. erewrite typed_subst_head_simpl by naive_solver.
      iApply (IHHtyped Δ (w :: vs)). iFrame "Hheap". iApply interp_env_cons; auto.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHHtyped2.
      iApply wp_mono; [|iApply "Hv"]; auto.
    - (* TLam *)
      value_case.
      iAlways; iIntros { τi } "%". iApply wp_TLam; iNext.
      iApply IHHtyped. iFrame "Hheap". by iApply interp_env_ren.
    - (* TApp *)
      smart_wp_bind TAppCtx v "#Hv" IHHtyped; cbn.
      iApply wp_wand_r; iSplitL; [iApply ("Hv" $! (interp  τ' Δ)); iPureIntro; apply _|].
      iIntros {w} "?". by rewrite interp_subst.
    - (* Fold *)
      iApply (@wp_bind _ _ _ [FoldCtx]);
        iApply wp_wand_l; iSplitL; [|iApply (IHHtyped Δ vs); auto].
      iIntros {v} "#Hv". value_case.
      rewrite /= -interp_subst fixpoint_unfold /=.
      iAlways; eauto.
    - (* Unfold *)
      iApply (@wp_bind _ _ _ [UnfoldCtx]);
        iApply wp_wand_l; iSplitL; [|iApply IHHtyped; auto].
      iIntros {v} "#Hv". rewrite /= fixpoint_unfold.
      change (fixpoint _) with (interp  (TRec τ) Δ); simpl.
      iDestruct "Hv" as {w} "#[% Hw]"; subst.
      iApply wp_Fold; cbn; auto using to_of_val.
      iNext; iPvsIntro. by rewrite -interp_subst.
    - (* Alloc *)
      smart_wp_bind AllocCtx v "#Hv" IHHtyped; cbn. iClear "HΓ".
      iApply wp_atomic; cbn; trivial; [rewrite to_of_val; auto|].
      iPvsIntro.
      iApply wp_alloc; auto 1 using to_of_val.
      iFrame "Hheap". iNext. iIntros {l} "Hl". iPvsIntro.
      iPvs (inv_alloc _ with "[Hl]") as "HN";
        [| | iPvsIntro; iExists _; iSplit; trivial]; eauto.
    - (* Load *)
      smart_wp_bind LoadCtx v "#Hv" IHHtyped; cbn. iClear "HΓ".
      iDestruct "Hv" as {l} "[% #Hv]"; subst.
      iApply wp_atomic; cbn; eauto using to_of_val.
      iPvsIntro.
      iInv (logN .@ l) as {w} "[Hw1 #Hw2]".
      iApply (wp_load _ _ 1); [|iFrame "Hheap"]; trivial. solve_ndisj.
      iIntros "{$Hw1} > Hw1". iPvsIntro. iSplitL; eauto.
    - (* Store *)
      smart_wp_bind (StoreLCtx _) v "#Hv" IHHtyped1; cbn.
      smart_wp_bind (StoreRCtx _) w "#Hw" IHHtyped2; cbn. iClear "HΓ".
      iDestruct "Hv" as {l} "[% #Hv]"; subst.
      iApply wp_atomic; cbn; [trivial| rewrite ?to_of_val; auto |].
      iPvsIntro.
      iInv (logN .@ l) as {z} "[Hz1 #Hz2]".
      eapply bool_decide_spec; eauto using to_of_val.
      iApply wp_store; auto using to_of_val. solve_ndisj.
      iIntros "{$Hheap $Hz1} > Hz1". iPvsIntro.
      iSplitL; eauto 10.
  Qed.
End typed_interp.
