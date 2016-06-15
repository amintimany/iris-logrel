Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import iris_logrel.F_mu_ref_par.lang iris_logrel.F_mu_ref_par.typing
        iris_logrel.F_mu_ref_par.rules iris_logrel.F_mu_ref_par.logrel_unary.
From iris.program_logic Require Export lifting.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
Require Import iris.proofmode.tactics iris.proofmode.invariants.
Import uPred.

Section typed_interp.
  Context {Σ : gFunctors} `{i : heapIG Σ} `{L : namespace}.

  Implicit Types P Q R : iPropG lang Σ.
  Notation "# v" := (of_val v) (at level 20).

  Local Hint Extern 1 =>
  match goal with
    |-
    (_
       --------------------------------------□
       ∃ _ : ?A, _) => let W := fresh "W" in evar (W : A); iExists W; unfold W; clear W
  end : itauto.

  Local Hint Extern 1 =>
  match goal with
    |-
    (_
       --------------------------------------□
       ▷ _) => iNext
  end : itauto.

  Local Hint Extern 1 =>
  match goal with
    |-
    (_
       --------------------------------------□
       □ _) => eapply (@always_intro _ _ _ _)
  end : itauto.

  Local Hint Extern 1 =>
  match goal with
    |-
    (_
       --------------------------------------□
       (_ ∧ _)) => iSplit
  end : itauto.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (@wp_bind _ _ _ [ctx]);
    iApply wp_impl_l;
    iSplit; [| iApply Hp; trivial];
    [apply (always_intro _ _); iIntros {v} Hv|iSplit; trivial]; cbn.

  Local Ltac value_case := iApply wp_value; [cbn; rewrite ?to_of_val; trivial|].

  Lemma typed_interp N Δ Γ vs e τ
        (HNLdisj : ∀ l : loc, N ⊥ L .@ l)
        (Htyped : typed Γ e τ)
        (HΔ : context_interp_Persistent Δ)
    : List.length Γ = List.length vs →
      (heapI_ctx N ∧ Π∧ zip_with (λ τ v, (@interp Σ i L) τ Δ v) Γ vs)%I ⊢
                  WP (e.[env_subst vs]) @ ⊤ {{ λ v, (@interp Σ i L) τ Δ v }}.
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
    - (* nat *) value_case; iExists _ ; trivial.
    - (* bool *) value_case; iExists _ ; trivial.
    - (* nat bin op *)
      smart_wp_bind (NBOPLCtx _ e2.[env_subst vs]) v "#Hv" IHHtyped1.
      smart_wp_bind (NBOPRCtx _ v) v' "# Hv'" IHHtyped2.
      iDestruct "Hv" as {n} "%"; iDestruct "Hv'" as {n'} "%"; subst. simpl.
      iApply wp_nat_bin_op. iNext; destruct op; simpl;
      try destruct eq_nat_dec; try destruct le_dec; try destruct lt_dec;
        eauto 10 with itauto.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) v "#Hv" IHHtyped1.
      smart_wp_bind (PairRCtx v) v' "# Hv'" IHHtyped2.
      value_case; eauto 10 with itauto.
    - (* fst *)
      smart_wp_bind (FstCtx) v "# Hv" IHHtyped; cbn.
      iApply double_exists; [|trivial].
      intros w w'; cbn; iIntros "#[% [H2 H3]]"; rewrite H; cbn.
      iApply wp_fst; try iNext; eauto using to_of_val; cbn.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" IHHtyped; cbn.
      iApply double_exists; [|trivial].
      intros w w'; cbn; iIntros "#[% [H2 H3]]"; rewrite H; cbn.
      iApply wp_snd; try iNext; eauto using to_of_val; cbn.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHHtyped; cbn.
      value_case; iLeft; auto with itauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHHtyped; cbn.
      value_case; iRight; auto with itauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v "#Hv" IHHtyped1; cbn.
      iDestruct "Hv" as "[Hv|Hv]";
      iDestruct "Hv" as {w} "[% Hw]"; rewrite H;
        [iApply wp_case_inl|iApply wp_case_inr];
        auto 1 using to_of_val;
        asimpl;
        [specialize (IHHtyped2 Δ HΔ (w::vs)) |
         specialize (IHHtyped3 Δ HΔ (w::vs))];
        erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto); iNext;
          [iApply IHHtyped2 | iApply IHHtyped3]; cbn; auto with itauto.
    - (* If *)
      smart_wp_bind (IfCtx _ _) v "#Hv" IHHtyped1; cbn.
      iDestruct "Hv" as {b} "%"; subst; destruct b; simpl;
        [iApply wp_if_true| iApply wp_if_false]; iNext;
      [iApply IHHtyped2| iApply IHHtyped3]; auto with itauto.
    - (* lam *)
      value_case. iApply löb. rewrite -always_later.
      iIntros "#Hlat". iAlways. iIntros {w} "#Hw".
      iApply wp_lam; auto 1 using to_of_val.
      asimpl. change (Lam _) with (# (LamV e.[upn 2 (env_subst vs)])).
      erewrite typed_subst_head_simpl_2; [|eauto|cbn]; eauto.
      iNext; iApply (IHHtyped Δ HΔ (_ :: w :: vs)); cbn; auto.
      repeat iSplit; trivial.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHHtyped2.
      iApply wp_mono; [|iApply "Hv"]; auto with itauto.
    - (* TLam *)
      value_case.
      iIntros {τi}; destruct τi as [τi τiPr].
      iRevert "Hheap".
      iPoseProof (always_intro with "HΓ") as "HP"; try typeclasses eauto;
        try (iApply always_impl; iExact "HP").
      iIntros "#HΓ #Hheap".
      iApply wp_TLam; iNext.
      iApply IHHtyped; [rewrite map_length|]; trivial.
      iSplit; trivial.
      iRevert "Hheap HΓ". rewrite zip_with_context_interp_subst.
      iIntros "#Hheap #HΓ"; trivial.
    - (* TApp *)
      smart_wp_bind TAppCtx v "#Hv" IHHtyped; cbn.
      iSpecialize ("Hv" $! ((interp τ' Δ) ↾ _)); cbn.
      iApply always_elim. iApply always_mono; [|trivial].
      apply wp_mono => w. by rewrite -interp_subst; simpl.
    - (* Fold *)
      specialize (IHHtyped Δ HΔ vs Hlen).
      setoid_rewrite <- interp_subst in IHHtyped.
      iApply (@wp_bind _ _ _ [FoldCtx]).
      iApply wp_impl_l.
      iSplit; [eapply (@always_intro _ _ _ _)| iApply IHHtyped; trivial].
      + iIntros {v} "#Hv".
        value_case.
        rewrite fixpoint_unfold; cbn.
        auto with itauto.
      + iFrame "Hheap HΓ"; trivial.
    - (* Unfold *)
      iApply (@wp_bind _ _ _ [UnfoldCtx]);
        iApply wp_impl_l;
        iSplit; [eapply (@always_intro _ _ _ _)|
                 iApply IHHtyped;
                 auto with itauto].
      iIntros {v}.
      cbn [interp interp_rec cofe_mor_car].
      rewrite fixpoint_unfold.
      iIntros "#Hv"; cbn.
      change (fixpoint _) with (@interp _ _ L (TRec τ) Δ).
      iDestruct "Hv" as {w} "[% #Hw]"; rewrite H.
      iApply wp_Fold; cbn; auto using to_of_val.
      rewrite -interp_subst; auto with itauto.
    - (* Fork *)
      iApply wp_fork.
      iNext; iSplitL; trivial.
      iApply wp_impl_l.
      iSplit; [|iApply IHHtyped]; trivial.
      { iApply always_intro; trivial. iIntros "#Hheap % #Hv"; trivial. }
      iSplit; trivial.
    - (* Alloc *)
      smart_wp_bind AllocCtx v "#Hv" IHHtyped; cbn. iClear "HΓ".
      iApply wp_atomic; cbn; trivial; [rewrite to_of_val; auto|].
      iPvsIntro.
      iApply wp_alloc; auto 1 using to_of_val.
      iFrame "Hheap". iNext.
      iIntros {l} "Hl".
      iPvs (inv_alloc _ with "[Hl]") as "HN";
        [| | iPvsIntro; iExists _; iSplit; trivial].
      trivial.
      iNext; iExists _; iFrame "Hl"; trivial.
    - (* Load *)
      smart_wp_bind LoadCtx v "#Hv" IHHtyped; cbn. iClear "HΓ".
      iRevert "Hheap". iApply exist_elim; [|iExact "Hv"].
      iIntros {l} "[% #Hv] #Hheap"; rewrite H.
      iApply wp_atomic; cbn; eauto using to_of_val.
      iPvsIntro.
      iInv (L .@ l) as {w} "[Hw1 #Hw2]".
      iApply (wp_load _ _ _ 1); [|iFrame "Hheap"]; trivial.
      specialize (HNLdisj l); set_solver_ndisj.
      iFrame "Hw1". iNext.
      iIntros "Hw1". iSplitL; trivial.
      iNext; iExists _. iFrame "Hw1"; trivial.
    - (* Store *)
      smart_wp_bind (StoreLCtx _) v "#Hv" IHHtyped1; cbn.
      smart_wp_bind (StoreRCtx _) w "#Hw" IHHtyped2; cbn. iClear "HΓ".
      iRevert "Hheap Hw". iApply exist_elim; [|iExact "Hv"].
      iIntros {l} "#[% Hl] #Hheap #Hw"; rewrite H.
      iApply wp_atomic; cbn; [trivial| rewrite ?to_of_val; auto |].
      iPvsIntro.
      iInv (L .@ l) as {z} "[Hz1 #Hz2]".
      eapply bool_decide_spec; eauto using to_of_val.
      iApply (wp_store N); auto using to_of_val.
      specialize (HNLdisj l); set_solver_ndisj.
      iFrame "Hheap Hz1".
      iNext.
      iIntros "Hz1".
      iSplitL; [|iPvsIntro; trivial].
      iNext; iExists _. iFrame "Hz1"; trivial.
    - (* CAS *)
      smart_wp_bind (CasLCtx _ _) v1 "#Hv1" IHHtyped1; cbn.
      smart_wp_bind (CasMCtx _ _) v2 "#Hv2" IHHtyped2; cbn.
      smart_wp_bind (CasRCtx _ _) v3 "#Hv3" IHHtyped3; cbn. iClear "HΓ".
      iDestruct "Hv1" as {l} "[% Hinv]"; subst.
      iApply wp_atomic; cbn; eauto 10 using to_of_val.
      iPvsIntro.
      iInv (L .@ l) as {w} "[Hw1 #Hw2]"; [cbn; eauto 10 using to_of_val|].
      destruct (val_dec_eq v2 w) as [|Hneq]; subst.
      + iApply (wp_cas_suc N); eauto using to_of_val.
        specialize (HNLdisj l); set_solver_ndisj.
        iFrame "Hheap Hw1".
        iNext. iIntros "Hw1".
        iSplitL.
        * iNext; iExists _; iSplitL; trivial.
        * iPvsIntro. iExists _; auto with itauto.
      + iApply (wp_cas_fail N); eauto using to_of_val.
        clear Hneq. specialize (HNLdisj l); set_solver_ndisj.
        (* Weird that Hneq above makes set_solver_ndisj diverge or
           take exceptionally long!?!? *)
        iFrame "Hheap Hw1".
        iNext. iIntros "Hw1".
        iSplitL.
        * iNext; iExists _; iSplitL; trivial.
        * iPvsIntro. iExists _; auto with itauto.
      (* unshelving *)
      Unshelve.
      cbn; typeclasses eauto.
  Qed.

End typed_interp.