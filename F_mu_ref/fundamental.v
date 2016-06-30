From iris_logrel.F_mu_ref Require Export logrel.
From iris.proofmode Require Import tactics pviewshifts invariants.
From iris_logrel.F_mu_ref Require Import rules.
From iris.algebra Require Export upred_big_op.

Section typed_interp.
  Context {Σ : gFunctors} `{i : heapG Σ} {L : namespace}.
  Implicit Types P Q R : iPropG lang Σ.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (@wp_bind _ _ _ [ctx]);
    iApply wp_wand_l;
    iSplitL; [|iApply Hp; trivial]; [iIntros {v} Hv|iSplit; trivial]; cbn.

  Local Ltac value_case := iApply wp_value; [cbn; rewrite ?to_of_val; trivial|].

  Lemma typed_interp N (Δ : varC -n> valC -n> iPropG lang Σ) Γ vs e τ
      (HNLdisj : ∀ l : loc, N ⊥ L .@ l)
      (Htyped : typed Γ e τ)
      (HΔ : ∀ x v, PersistentP (Δ x v)) :
    length Γ = length vs →
    heap_ctx N ∧ [∧] zip_with (λ τ, interp L τ Δ) Γ vs
    ⊢ WP e.[env_subst vs] {{ interp L τ Δ }}.
  Proof.
    revert Δ HΔ vs.
    induction Htyped; intros Δ HΔ vs Hlen; iIntros "#[Hheap HΓ]"; cbn.
    - (* var *)
      destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
      { by rewrite -Hlen; apply lookup_lt_Some with τ. }
      rewrite /env_subst Hv; value_case.
      iApply (big_and_elem_of with "HΓ").
      apply elem_of_list_lookup_2 with x.
      rewrite lookup_zip_with; simplify_option_eq; trivial.
    - (* unit *) value_case; trivial.
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
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as {w} "[% Hw]"; subst.
      + iApply wp_case_inl; auto 1 using to_of_val; asimpl.
        specialize (IHHtyped2 Δ HΔ (w::vs)).
        erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto).
        iNext; iApply IHHtyped2; cbn; auto.
      + iApply wp_case_inr; auto 1 using to_of_val; asimpl.
        specialize (IHHtyped3 Δ HΔ (w::vs)).
        erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto).
        iNext; iApply IHHtyped3; cbn; auto.
    - (* lam *)
      value_case; iAlways; iIntros {w} "#Hw".
      iApply wp_lam; auto 1 using to_of_val.
      asimpl; erewrite typed_subst_head_simpl; [|eauto|cbn]; eauto.
      iNext; iApply (IHHtyped Δ HΔ (w :: vs)); cbn; auto.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHHtyped2.
      iApply wp_mono; [|iApply "Hv"]; auto.
    - (* TLam *)
      value_case. iIntros {τi} "! %".
      iApply wp_TLam; iNext. simpl.
      iApply (IHHtyped (extend_context_interp_fun1 τi Δ)); [rewrite map_length|]; trivial.
       rewrite -zip_with_context_interp_subst. auto.
    - (* TApp *)
      smart_wp_bind TAppCtx v "#Hv" IHHtyped; cbn.
      iApply wp_wand_r; iSplitL; [iApply ("Hv" $! (interp L τ' Δ)); iPureIntro; apply _|]; cbn.
      iIntros {w} "?"; rewrite interp_subst; trivial.
    - (* Fold *)
      rewrite map_length in IHHtyped.
      iApply (@wp_bind _ _ _ [FoldCtx]).
        iApply wp_wand_l.
        iSplitL; [|iApply (IHHtyped (extend_context_interp ((interp L (TRec τ)) Δ) Δ));
                 trivial].
      + iIntros {v} "#Hv".
        value_case.
        rewrite fixpoint_unfold; cbn.
        iAlways; eauto.
      + rewrite zip_with_context_interp_subst; auto.
    - (* Unfold *)
      iApply (@wp_bind _ _ _ [UnfoldCtx]);
        iApply wp_wand_l; iSplitL; [|iApply IHHtyped; auto].
      iIntros {v}.
      cbn [interp interp_rec cofe_mor_car].
      rewrite fixpoint_unfold.
      iIntros "#Hv"; cbn.
      change (fixpoint _) with (interp L (TRec τ) Δ).
      iDestruct "Hv" as {w} "[% #Hw]"; subst.
      iApply wp_Fold; cbn; auto using to_of_val.
      rewrite -interp_subst; auto.
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
      iInv (L .@ l) as {w} "[Hw1 #Hw2]".
      iApply (wp_load _ _ _ 1); [|iFrame "Hheap"]; trivial.
      specialize (HNLdisj l); set_solver_ndisj.
      iFrame "Hw1". iIntros "> Hw1". iPvsIntro. iSplitL; eauto.
    - (* Store *)
      smart_wp_bind (StoreLCtx _) v "#Hv" IHHtyped1; cbn.
      smart_wp_bind (StoreRCtx _) w "#Hw" IHHtyped2; cbn. iClear "HΓ".
      iDestruct "Hv" as {l} "[% #Hv]"; subst.
      iApply wp_atomic; cbn; [trivial| rewrite ?to_of_val; auto |].
      iPvsIntro.
      iInv (L .@ l) as {z} "[Hz1 #Hz2]".
      eapply bool_decide_spec; eauto using to_of_val.
      iApply (wp_store N); auto using to_of_val.
      specialize (HNLdisj l); set_solver_ndisj.
      iFrame "Hheap Hz1".
      iIntros "> Hz1". iPvsIntro.
      iSplitL; [|iPvsIntro; trivial]. eauto.
  Qed.
End typed_interp.
