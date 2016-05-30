Require Import iris.proofmode.invariants iris.proofmode.weakestpre
        iris.proofmode.tactics.
Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.auth iris.algebra.dec_agree iris.algebra.frac
        iris.algebra.upred_big_op.
From iris_logrel.F_mu_ref_par Require Import lang typing rules_binary
        rules logrel_binary fundamental_binary context_refinement.
Require Import iris.program_logic.adequacy.
Import uPred.

Section Soundness.
  Context {Σ : gFunctors}
          {Hhp : auth.authG lang Σ heapR}
          {Hcfg : auth.authG lang Σ cfgR}.

  Definition free_type_context : varC -n> bivalC -n> iPropG lang Σ :=
    {| cofe_mor_car := λ x, {| cofe_mor_car := λ y, (True)%I |} |}.

  Local Notation Δφ := free_type_context.

  Local Opaque to_heap.

  Global Instance free_context_interp_Persistent : context_interp_Persistent Δφ.
  Proof. intros x v; apply const_persistent. Qed.

  Lemma wp_basic_soundness e e' τ :
    (∀ H H' N Δ HΔ , @bin_log_related Σ H H' N Δ [] e e' τ HΔ) →
     (@ownership.ownP lang (globalF Σ) ∅)
      ⊢ WP e
      {{_, ■ (∃ thp' h v, rtc step ([e'], ∅) ((# v) :: thp', h))}}.
  Proof.
    iIntros {H1} "Hemp".
    iDestruct (heap_alloc (nroot .@ "Fμ,ref,par" .@ 2) _ _ _ _ with "Hemp")
      as "Hp".
    iPvs "Hp" as {H} "[#Hheap _]".
    iPvs (own_alloc
            (● ((to_cfg ([e'], ∅) : cfgR))
                  ⋅ ◯ (({[ 0 := Frac 1 (DecAgree e' : dec_agreeR _) ]} : tpoolR,
                       ∅ : heapR): cfgR))) as "Hcfg".
    { constructor; eauto.
      - intros n; simpl. exists ∅. unfold to_cfg; simpl. rewrite to_empty_heap.
          by rewrite cmra_unit_left_id cmra_unit_right_id.
      - repeat constructor; simpl; auto.
    }
    iDestruct "Hcfg" as {γ} "Hcfg". rewrite own_op.
    iDestruct "Hcfg" as "[Hcfg1 Hcfg2]".
    iAssert (@auth.auth_inv _ Σ _ _ _ γ (Spec_inv (to_cfg ([e'], ∅))))
      as "Hinv" with "[Hcfg1]".
    { iExists _; iFrame "Hcfg1". apply const_intro; constructor. }
    iPvs (inv_alloc (nroot .@ "Fμ,ref,par" .@ 3) with "[Hinv]") as "#Hcfg";
      trivial.
    { iNext. iExact "Hinv". }
    iPoseProof (H1 H (@CFGSG _ _ γ) _ Δφ _ [] _ _ 0 []
                with "[Hcfg2]") as "HBR".
    { unfold Spec_ctx, auth.auth_ctx, tpool_mapsto, auth.auth_own.
      simpl. rewrite empty_env_subst. by iFrame "Hheap Hcfg Hcfg2". }
    simpl. rewrite empty_env_subst.
    iApply wp_pvs.
    iApply wp_wand_l; iSplitR; [|iApply "HBR"].
    iIntros {v} "H". iDestruct "H" as {v'} "[Hj #Hinterp]".
    iInv> (nroot .@ "Fμ,ref,par" .@ 3) as {ρ} "[Hown #Hp]".
    iDestruct "Hp" as %Hp.
    unfold tpool_mapsto, auth.auth_own; simpl.
    iCombine "Hj" "Hown" as "Hown".
    iDestruct (@own_valid _ Σ (authR cfgR) _ γ _ with "Hown !")
      as "#Hvalid".
    iDestruct (auth_validI _ with "Hvalid") as "[Ha' #Hb]";
      simpl; iClear "Hvalid".
    iDestruct "Hb" as %Hb.
    iDestruct "Ha'" as {ρ'} "Ha'"; iDestruct "Ha'" as %Ha'.
    rewrite ->(right_id _ _) in Ha'; setoid_subst.
    iPvsIntro; iSplitL.
    - iExists _. rewrite own_op. iDestruct "Hown" as "[Ho1 Ho2]".
      iSplitL; trivial.
    - iApply const_intro; eauto.
      rewrite from_to_cfg in Hp.
      destruct ρ' as [th hp]; unfold op, cmra_op in *; simpl in *.
      unfold prod_op, of_cfg in *; simpl in *.
      destruct th as [|r th]; simpl in *; eauto.
      destruct Hb as [Hx1 Hx2]. simpl in *.
      destruct r as [q r|]; simpl in *; eauto.
      inversion Hx1 as [|? ? Hx]; subst.
      apply frac_valid_inv_l in Hx. inversion Hx.
      Unshelve. all: trivial.
  Qed.

  Lemma basic_soundness e e' τ :
    (∀ H H' N Δ HΔ , @bin_log_related Σ H H' N Δ [] e e' τ HΔ) →
    ∀ v thp hp,
      rtc step ([e], ∅) ((# v) :: thp, hp) →
      (∃ thp' hp' v', rtc step ([e'], ∅) ((# v') :: thp', hp')).
  Proof.
    intros H1 v thp hp H2.
    match goal with
      |- ?A =>
      eapply (@wp_adequacy_result lang _ ⊤ (λ _, A) e v thp ∅ ∅ hp); eauto
    end.
    - apply cmra_unit_valid.
    - iIntros "[Hp Hg]".
      iApply wp_wand_l; iSplitR; [| by iApply wp_basic_soundness].
        by iIntros {w} "H".
  Qed.

  Lemma Binary_Soundness Γ e e' τ :
    (∀ f, e.[iter (List.length Γ) up f] = e) →
    (∀ f, e'.[iter (List.length Γ) up f] = e') →
    (∀ H H' N Δ HΔ , @bin_log_related Σ H H' N Δ Γ e e' τ HΔ) →
    context_refines Γ e e' τ.
  Proof.
    intros H1 K HK htp hp v Hstp Hc Hc'.
    eapply basic_soundness; eauto.
    intros H H' N Δ HΔ.
    eapply (bin_log_related_under_typed_context _ _ _ _ []); eauto.
  Qed.

End Soundness.