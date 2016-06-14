Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import iris_logrel.F_mu_ref.lang iris_logrel.F_mu_ref.typing
        iris_logrel.F_mu_ref.rules iris_logrel.F_mu_ref.logrel.
From iris.program_logic Require Export lifting.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
Require Import iris.proofmode.tactics iris.proofmode.invariants.
Import uPred.

Section typed_interp.
  Context {Σ : gFunctors} `{i : heapG Σ} `{L : namespace}.

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

  Lemma later_exist_turnstile (M : cmraT) (A : Type) :
    Inhabited A → ∀ Φ : A → uPred M, (▷ (∃ a : A, Φ a))%I ⊢ (∃ a : A, ▷ Φ a)%I.
  Proof. intros H Φ. rewrite later_exist; trivial. Qed.

  Lemma typed_interp N Δ Γ vs e τ
        (HNLdisj : ∀ l : loc, N ⊥ L .@ l)
        (Htyped : typed Γ e τ)
        (HΔ : context_interp_Persistent Δ)
    : List.length Γ = List.length vs →
      (heap_ctx N ∧ Π∧ zip_with (λ τ v, (@interp Σ i L) τ Δ v) Γ vs)%I ⊢
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
    - (* lam *)
      value_case; apply (always_intro _ _); iIntros {w} "#Hw".
      iApply wp_lam; auto 1 using to_of_val.
      asimpl; erewrite typed_subst_head_simpl; [|eauto|cbn]; eauto.
      iNext; iApply (IHHtyped Δ HΔ (w :: vs)); cbn; auto with itauto.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHHtyped2.
      iApply wp_mono; [|iApply "Hv"]; auto with itauto.
    - (* TLam *)
      value_case; iApply exist_intro; iSplit; trivial.
      iIntros {τi}; destruct τi as [τi τiPr].
      iRevert "Hheap".
      iPoseProof (always_intro with "HΓ") as "HP"; try typeclasses eauto;
        try (iApply always_impl; iExact "HP").
      iIntros "#HΓ #Hheap".
      iApply IHHtyped; [rewrite map_length|]; trivial.
      iSplit; trivial.
      iRevert "Hheap HΓ". rewrite zip_with_context_interp_subst.
      iIntros "#Hheap #HΓ"; trivial.
    - (* TApp *)
      smart_wp_bind TAppCtx v "#Hv" IHHtyped; cbn.
      iDestruct "Hv" as {e'} "[% He']"; rewrite H.
      iApply wp_TLam.
      iSpecialize ("He'" $! ((interp τ' Δ) ↾ _)); cbn.
      iApply always_elim. iApply always_mono; [|trivial].
      iIntros "He'"; iNext.
      iApply wp_mono; [|trivial].
      iIntros {w} "#H". rewrite -interp_subst; trivial.
    - (* Fold *)
      rewrite map_length in IHHtyped.
      iApply (@wp_bind _ _ _ [FoldCtx]).
        iApply wp_impl_l.
        iSplit; [eapply (@always_intro _ _ _ _)|
                 iApply (IHHtyped (extend_context_interp ((interp (TRec τ)) Δ) Δ));
                 trivial].
      + iIntros {v} "#Hv".
        value_case.
        rewrite fixpoint_unfold; cbn.
        auto with itauto.
      + iRevert "Hheap HΓ"; rewrite zip_with_context_interp_subst;
          iIntros "#Hheap #HΓ"; auto with itauto.
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
      (* unshelving *)
      Unshelve.
      cbn; typeclasses eauto.
  Qed.

End typed_interp.