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
          {Hhp : auth.authG lang Σ heapUR}
          {Hcfg : auth.authG lang Σ cfgUR}.

  Definition free_type_context : varC -n> bivalC -n> iPropG lang Σ :=
    {| cofe_mor_car := λ x, {| cofe_mor_car := λ y, (True)%I |} |}.

  Local Notation Δφ := free_type_context.

  Local Opaque to_heap.

  Lemma wp_basic_soundness e e' τ :
    (∀ H H' N Δ HΔ , @bin_log_related Σ H H' N Δ [] e e' τ HΔ) →
     (@ownership.ownP lang (globalF Σ) ∅)
      ⊢ WP e
      {{_, ■ (∃ thp' h v, rtc step ([e'], ∅) ((# v) :: thp', h))}}.
  Proof.
    iIntros {H1} "Hemp".
    iPvs (heap_alloc (nroot .@ "Fμ,ref,par" .@ 2) _ _ _ _ with "Hemp")
      as {H} "[#Hheap _]".
    iPvs (own_alloc (● (to_cfg ([e'], ∅) : cfgUR)
                  ⋅ ◯ (({[ 0 := Excl' e' ]} : tpoolUR, ∅) : cfgUR))) as "Hcfg".
    { constructor; eauto.
      - intros n; simpl. exists ∅. unfold to_cfg; simpl. rewrite to_empty_heap.
          by rewrite left_id right_id.
      - repeat constructor; simpl; by auto.
    }
    iDestruct "Hcfg" as {γ} "[Hcfg1 Hcfg2]".
    iAssert (@auth.auth_inv _ Σ _ _ γ (Spec_inv ([e'], ∅)))
      with "[Hcfg1]" as "Hinv".
    { iExists _; iFrame "Hcfg1".
      apply const_intro. rewrite from_to_cfg; constructor.
    }
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
    iIntros {v}; iDestruct 1 as {v'} "[Hj #Hinterp]".
    iInv> (nroot .@ "Fμ,ref,par" .@ 3) as {ρ} "[Hown #Hp]".
    iDestruct "Hp" as %Hp.
    unfold tpool_mapsto, auth.auth_own; simpl.
    iCombine "Hj" "Hown" as "Hown".
    iDestruct (@own_valid _ Σ (authR cfgUR) _ γ _ with "#Hown")
      as "#Hvalid".
    iDestruct (auth_validI _ with "Hvalid") as "[Ha' #Hb]";
      simpl; iClear "Hvalid".
    iDestruct "Hb" as %Hb.
    iDestruct "Ha'" as {ρ'} "Ha'"; iDestruct "Ha'" as %Ha'.
    rewrite ->(right_id _ _) in Ha'; setoid_subst.
    iPvsIntro; iSplitL.
    - iExists _. rewrite own_op. iDestruct "Hown" as "[Ho1 Ho2]".
      iSplitL; trivial.
    - iPureIntro.
      destruct ρ' as [th hp]; unfold op, cmra_op in *; simpl in *.
      unfold prod_op, of_cfg in *; simpl in *.
      destruct th as [|r th]; simpl in *; eauto.
      destruct Hb as [Hx1 Hx2]. simpl in *.
      destruct r as [q r|]; simpl in *; eauto.
      inversion Hx1 as [|? ? Hx]; subst.
      destruct q as [?|]. by move: Hx=> [/exclusive_r ??]. done.
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
    - apply ucmra_unit_valid.
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
