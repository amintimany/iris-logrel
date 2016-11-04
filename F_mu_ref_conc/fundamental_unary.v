From iris_logrel.F_mu_ref_conc Require Export logrel_unary.
From iris_logrel.F_mu_ref_conc Require Import rules.
From iris.base_logic Require Export big_op invariants.
From iris.proofmode Require Import tactics.

Definition log_typed `{heapIG Σ} (Γ : list type) (e : expr) (τ : type) := ∀ Δ vs,
  env_PersistentP Δ →
  heapI_ctx ∧ ⟦ Γ ⟧* Δ vs ⊢ ⟦ τ ⟧ₑ Δ e.[env_subst vs].
Notation "Γ ⊨ e : τ" := (log_typed Γ e τ) (at level 74, e, τ at next level).

Section typed_interp.
  Context `{heapIG Σ}.
  Notation D := (valC -n> iProp Σ).

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (wp_bind [ctx]);
    iApply wp_wand_l;
    iSplitL; [| iApply Hp; trivial]; [iIntros (v) Hv|iSplit; trivial]; cbn.

  Local Ltac value_case := iApply wp_value; [cbn; rewrite ?to_of_val; trivial|].

  Theorem fundamental Γ e τ : Γ ⊢ₜ e : τ → Γ ⊨ e : τ.
  Proof.
    induction 1; iIntros (Δ vs HΔ) "#[Hheap HΓ] /=".
    - (* var *)
      iDestruct (interp_env_Some_l with "HΓ") as (v) "[% ?]"; first done.
      rewrite /env_subst. simplify_option_eq. by value_case.
    - (* unit *) value_case; trivial.
    - (* nat *) value_case; simpl; eauto.
    - (* bool *) value_case; simpl; eauto.
    - (* nat bin op *)
      smart_wp_bind (BinOpLCtx _ e2.[env_subst vs]) v "#Hv" IHtyped1.
      smart_wp_bind (BinOpRCtx _ v) v' "# Hv'" IHtyped2.
      iDestruct "Hv" as (n) "%"; iDestruct "Hv'" as (n') "%"; simplify_eq/=.
      iApply wp_nat_binop. iNext. iIntros "!> {Hheap HΓ}".
      destruct op; simpl; try destruct eq_nat_dec;
        try destruct le_dec; try destruct lt_dec; eauto 10.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) v "#Hv" IHtyped1.
      smart_wp_bind (PairRCtx v) v' "# Hv'" IHtyped2.
      value_case; eauto.
    - (* fst *)
      smart_wp_bind (FstCtx) v "# Hv" IHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_fst; eauto using to_of_val.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" IHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_snd; eauto using to_of_val.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHtyped; cbn.
      value_case; eauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHtyped; cbn.
      value_case; eauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v "#Hv" IHtyped1; cbn.
      iDestruct (interp_env_length with "HΓ") as %?.
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[% Hw]"; simplify_eq/=.
      + iApply wp_case_inl; auto 1 using to_of_val; asimpl. iNext.
        erewrite typed_subst_head_simpl by naive_solver.
        iApply (IHtyped2 Δ (w :: vs)). iSplit; [|iApply interp_env_cons]; auto.
      + iApply wp_case_inr; auto 1 using to_of_val; asimpl. iNext.
        erewrite typed_subst_head_simpl by naive_solver.
        iApply (IHtyped3 Δ (w :: vs)). iSplit; [|iApply interp_env_cons]; auto.
    - (* If *)
      smart_wp_bind (IfCtx _ _) v "#Hv" IHtyped1; cbn.
      iDestruct "Hv" as ([]) "%"; subst; simpl;
        [iApply wp_if_true| iApply wp_if_false]; iNext;
      [iApply IHtyped2| iApply IHtyped3]; auto.
    - (* Rec *)
      value_case; iAlways. simpl. iLöb as "IH"; iIntros (w) "#Hw".
      iDestruct (interp_env_length with "HΓ") as %?.
      iApply wp_rec; auto 1 using to_of_val. iNext.
      asimpl. change (Rec _) with (of_val (RecV e.[upn 2 (env_subst vs)])) at 2.
      erewrite typed_subst_head_simpl_2 by naive_solver.
      iApply (IHtyped Δ (_ :: w :: vs)). iSplit; [done|].
      iApply interp_env_cons; iSplit; [|iApply interp_env_cons]; auto.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHtyped2.
      iApply wp_mono; [|iApply "Hv"]; auto.
    - (* TLam *)
      value_case.
      iAlways; iIntros (τi) "%". iApply wp_tlam; iNext.
      iApply IHtyped. iFrame "Hheap". by iApply interp_env_ren.
    - (* TApp *)
      smart_wp_bind TAppCtx v "#Hv" IHtyped; cbn.
      iApply wp_wand_r; iSplitL; [iApply ("Hv" $! (⟦ τ' ⟧ Δ)); iPureIntro; apply _|]; cbn.
      iIntros (w) "?". by iApply interp_subst.
    - (* Fold *)
      iApply (wp_bind [FoldCtx]);
        iApply wp_wand_l; iSplitL; [|iApply (IHtyped Δ vs); auto].
      iIntros (v) "#Hv". value_case.
      rewrite /= -interp_subst fixpoint_unfold /=.
      iAlways; eauto.
    - (* Unfold *)
      iApply (wp_bind [UnfoldCtx]);
        iApply wp_wand_l; iSplitL; [|iApply IHtyped; auto].
      iIntros (v) "#Hv". rewrite /= fixpoint_unfold.
      change (fixpoint _) with (⟦ TRec τ ⟧ Δ); simpl.
      iDestruct "Hv" as (w) "#[% Hw]"; subst.
      iApply wp_fold; cbn; auto using to_of_val.
      iNext; iModIntro. by iApply interp_subst.
    - (* Fork *)
      iApply wp_fork. iNext; iSplitL; trivial.
      iApply wp_wand_l. iSplitL; [|iApply IHtyped; auto]; auto.
    - (* Alloc *)
      smart_wp_bind AllocCtx v "#Hv" IHtyped; cbn. iClear "HΓ". iApply wp_fupd.
      iApply (wp_alloc with "Hheap []"); auto 1 using to_of_val.
      iNext; iIntros (l) "Hl".
      iMod (inv_alloc _ with "[Hl]") as "HN";
        [| iModIntro; iExists _; iSplit; trivial]; eauto.
    - (* Load *)
      smart_wp_bind LoadCtx v "#Hv" IHtyped; cbn. iClear "HΓ".
      iDestruct "Hv" as (l) "[% #Hv]"; subst.
      iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
      iApply ((wp_load _ _ 1) with "[Hw1] [Hclose]"); [|iFrame "Hheap"|];
      trivial. solve_ndisj. iNext.
      iIntros "Hw1". iMod ("Hclose" with "[-]"); eauto.
    - (* Store *)
      smart_wp_bind (StoreLCtx _) v "#Hv" IHtyped1; cbn.
      smart_wp_bind (StoreRCtx _) w "#Hw" IHtyped2; cbn. iClear "HΓ".
      iDestruct "Hv" as (l) "[% #Hv]"; subst.
      iInv (logN .@ l) as (z) "[Hz1 #Hz2]" "Hclose".
      iApply (wp_store with "[Hz1] [Hclose]"); [| |iFrame "Hheap Hz1"|].
      by rewrite to_of_val. solve_ndisj. iNext.
      iIntros "Hz1". iMod ("Hclose" with "[-]"); eauto.
    - (* CAS *)
      smart_wp_bind (CasLCtx _ _) v1 "#Hv1" IHtyped1; cbn.
      smart_wp_bind (CasMCtx _ _) v2 "#Hv2" IHtyped2; cbn.
      smart_wp_bind (CasRCtx _ _) v3 "#Hv3" IHtyped3; cbn. iClear "HΓ".
      iDestruct "Hv1" as (l) "[% Hinv]"; subst.
      iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
      destruct (decide (v2 = w)) as [|Hneq]; subst.
      + iApply (wp_cas_suc with "[Hw1] [Hclose]"); [| | |iFrame "Hheap Hw1"|];
          eauto using to_of_val. solve_ndisj. iNext.
        iIntros "Hw1". iMod ("Hclose" with "[-]"); eauto.
      + iApply (wp_cas_fail with "[Hw1] [Hclose]"); [| | | |iFrame "Hheap Hw1"|];
          eauto using to_of_val. solve_ndisj. iNext.
        iIntros "Hw1". iMod ("Hclose" with "[-]"); eauto.
  Qed.
End typed_interp.
