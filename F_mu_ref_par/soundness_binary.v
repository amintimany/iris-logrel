From iris_logrel.F_mu_ref_par Require Export context_refinement.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Import tactics pviewshifts invariants.
From iris.program_logic Require Import ownership adequacy.

Section soundness.
  Context `{authG lang Σ heapUR, authG lang Σ cfgUR}.
  Notation D := (prodC valC valC -n> iPropG lang Σ).
  Implicit Types Δ : listC D.

  Local Opaque to_heap.

  Lemma wp_basic_soundness e e' τ :
    (∀ `{heapIG Σ, cfgSG Σ} Δ (HΔ : env_PersistentP Δ), Δ ∥ [] ⊨ e ≤log≤ e' : τ) →
    ownP (Σ:=globalF Σ) ∅
    ⊢ WP e {{ _, ■ ∃ thp' h v, rtc step ([e'], ∅) (# v :: thp', h) }}.
  Proof.
    iIntros {H1} "Hemp".
    iPvs (heap_alloc with "Hemp") as {h} "[#Hheap _]"; first solve_ndisj.
    iPvs (own_alloc (● (to_cfg ([e'], ∅) : cfgUR)
      ⋅ ◯ (({[ 0 := Excl' e' ]} : tpoolUR, ∅) : cfgUR))) as {γ} "[Hcfg1 Hcfg2]".
    { constructor; eauto.
      - intros n; simpl. exists ∅. unfold to_cfg; simpl. rewrite to_empty_heap.
          by rewrite left_id right_id.
      - repeat constructor; simpl; by auto. }
    iAssert (@auth.auth_inv _ Σ _ _ γ (spec_inv ([e'], ∅)))
      with "[Hcfg1]" as "Hinv".
    { iExists _; iFrame "Hcfg1".
      iPureIntro. rewrite from_to_cfg; constructor. }
    iPvs (inv_alloc specN with "[Hinv]") as "#Hcfg"; trivial.
    { iNext. iExact "Hinv". }
    iPoseProof (bin_log_related_alt (H1 h (@CFGSG _ _ γ) [] _) [] _ 0 [] with "[Hcfg2]") as "HBR".
    { rewrite /spec_ctx /auth_ctx /tpool_mapsto /auth_own empty_env_subst /=.
      iFrame "Hheap Hcfg Hcfg2". by rewrite -interp_env_nil. }
    rewrite /= empty_env_subst.
    iApply wp_pvs. iApply wp_wand_l; iSplitR; [|iApply "HBR"].
    iIntros {v}; iDestruct 1 as {v'} "[Hj #Hinterp]".
    iInv> specN as {ρ} "[Hown #Hp]".
    iDestruct "Hp" as %Hp.
    unfold tpool_mapsto, auth.auth_own; simpl.
    iCombine "Hj" "Hown" as "Hown".
    iDestruct (@own_valid _ Σ (authR cfgUR) _ γ with "#Hown") as "#Hvalid".
    iDestruct (auth_validI _ with "Hvalid") as "[Ha' #Hb]";
      simpl; iClear "Hvalid".
    iDestruct "Hb" as %Hb.
    iDestruct "Ha'" as {ρ'} "Ha'"; iDestruct "Ha'" as %Ha'.
    rewrite ->(right_id _ _) in Ha'; setoid_subst.
    iPvsIntro; iSplitL.
    - iDestruct "Hown" as "[Ho1 Ho2]". iExists _.
      iSplitL; trivial.
    - iPureIntro.
      destruct ρ' as [th hp]; unfold op, cmra_op in *; simpl in *.
      unfold prod_op, of_cfg in *; simpl in *.
      destruct th as [|r th]; simpl in *; eauto.
      destruct Hb as [Hx1 Hx2]. simpl in *.
      destruct r as [q r|]; simpl in *; eauto.
      inversion Hx1 as [|? ? Hx]; subst.
      destruct q as [?|]. by move: Hx=> [/exclusive_r ??]. done.
  Qed.

  Lemma basic_soundness e e' τ v thp hp :
    (∀ `{heapIG Σ, cfgSG Σ} Δ (HΔ : env_PersistentP Δ), Δ ∥ [] ⊨ e ≤log≤ e' : τ) →
    rtc step ([e], ∅) (# v :: thp, hp) →
    (∃ thp' hp' v', rtc step ([e'], ∅) (# v' :: thp', hp')).
  Proof.
    intros H1 H2.
    match goal with
      |- ?A =>
      eapply (@wp_adequacy_result lang _ ⊤ (λ _, A) e v thp ∅ ∅ hp); eauto
    end.
    - apply ucmra_unit_valid.
    - iIntros "[Hp Hg]".
      iApply wp_wand_l; iSplitR; [| iApply wp_basic_soundness]; auto.
      by iIntros {w} "H".
  Qed.

  Lemma binary_soundness Γ e e' τ :
    (∀ f, e.[base.iter (length Γ) up f] = e) →
    (∀ f, e'.[base.iter (length Γ) up f] = e') →
    (∀ `{heapIG Σ, cfgSG Σ} Δ (HΔ : env_PersistentP Δ), Δ ∥ Γ ⊨ e ≤log≤ e' : τ) →
    Γ ⊨ e ≤ctx≤ e' : τ.
  Proof.
    intros H1 K HK htp hp v Hstp Hc Hc'.
    eapply basic_soundness; eauto.
    intros H' H'' N Δ HΔ.
    eapply (bin_log_related_under_typed_ctx _ _ _ _ []); eauto.
  Qed.
End soundness.
