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
          {iI : heapIG Σ} {iS : cfgSG Σ}
          {N : namespace}.

  Lemma bin_log_related_under_typed_context Γ e e' τ Γ' τ' K :
    (∀ f, e.[iter (List.length Γ) up f] = e) →
    (∀ f, e'.[iter (List.length Γ) up f] = e') →
    typed_context K Γ τ Γ' τ' →
    (∀ Δ {HΔ : context_interp_Persistent Δ},
        @bin_log_related _ _ _ N Δ Γ e e' τ HΔ) →
    ∀ Δ {HΔ : context_interp_Persistent Δ},
      @bin_log_related _ _ _ N Δ Γ' (fill_ctx K e) (fill_ctx K e') τ' HΔ.
  Proof.
    revert Γ τ Γ' τ' e e'.
    induction K as [|k K]=> Γ τ Γ' τ' e e' H1 H2; simpl.
    - inversion_clear 1; trivial.
    - inversion_clear 1 as [|? ? ? ? ? ? ? ? Hx1 Hx2]. intros H3 Δ HΔ.
      specialize (IHK _ _ _ _ e e' H1 H2 Hx2 H3).
      inversion Hx1; subst; simpl.
      + eapply typed_binary_interp_Lam; eauto;
          match goal with
            H : _ |- _ => eapply (typed_context_n_closed _ _ _ _ _ _ _ H)
          end.
      + eapply typed_binary_interp_App; eauto using typed_binary_interp.
      + eapply typed_binary_interp_App; eauto using typed_binary_interp.
      + eapply typed_binary_interp_Pair; eauto using typed_binary_interp.
      + eapply typed_binary_interp_Pair; eauto using typed_binary_interp.
      + eapply typed_binary_interp_Fst; eauto.
      + eapply typed_binary_interp_Snd; eauto.
      + eapply typed_binary_interp_InjL; eauto.
      + eapply typed_binary_interp_InjR; eauto.
      + match goal with
          H : typed_context_item _ _ _ _ _ |- _ => inversion H; subst
        end.
        eapply typed_binary_interp_Case;
          eauto using typed_binary_interp;
          match goal with
            H : _ |- _ => eapply (typed_n_closed _ _ _ H)
          end.
      + match goal with
          H : typed_context_item _ _ _ _ _ |- _ => inversion H; subst
        end.
        eapply typed_binary_interp_Case;
          eauto using typed_binary_interp;
          try match goal with
                H : _ |- _ => eapply (typed_n_closed _ _ _ H)
              end;
          match goal with
            H : _ |- _ => eapply (typed_context_n_closed _ _ _ _ _ _ _ H)
          end.
      + match goal with
          H : typed_context_item _ _ _ _ _ |- _ => inversion H; subst
        end.
        eapply typed_binary_interp_Case;
          eauto using typed_binary_interp;
          try match goal with
                H : _ |- _ => eapply (typed_n_closed _ _ _ H)
              end;
          match goal with
            H : _ |- _ => eapply (typed_context_n_closed _ _ _ _ _ _ _ H)
          end.
      + eapply typed_binary_interp_If;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_If;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_If;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_nat_bin_op;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_nat_bin_op;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_Fold; eauto.
      + eapply typed_binary_interp_Unfold; eauto.
      + eapply typed_binary_interp_TLam; eauto.
      + eapply typed_binary_interp_TApp; trivial.
      + eapply typed_binary_interp_Fork; trivial.
      + eapply typed_binary_interp_Alloc; trivial.
      + eapply typed_binary_interp_Load; trivial.
      + eapply typed_binary_interp_Store; eauto using typed_binary_interp.
      + eapply typed_binary_interp_Store; eauto using typed_binary_interp.
      + eapply typed_binary_interp_CAS; eauto using typed_binary_interp.
      + eapply typed_binary_interp_CAS; eauto using typed_binary_interp.
      + eapply typed_binary_interp_CAS; eauto using typed_binary_interp.
        Unshelve. all: trivial.
  Qed.

  Definition free_type_context : varC -n> bivalC -n> iPropG lang Σ :=
    {| cofe_mor_car := λ x, {| cofe_mor_car := λ y, (True)%I |} |}.

  Local Notation Δφ := free_type_context.

  Global Instance free_context_interp_Persistent : context_interp_Persistent Δφ.
  Proof. intros x v; apply const_persistent. Qed.

  Lemma wp_basic_soundness e e' τ :
    @bin_log_related _ _ _ N Δφ [] e e' τ _ →
    ((heapI_ctx (N .@ 2) ★ Spec_ctx (N .@ 3) (to_cfg ([e'], ∅)) ★ 0 ⤇ e')%I)
      ⊢ WP e {{_, ■ (∃ thp' h v, rtc step ([e'], ∅) ((# v) :: thp', h))}}.
  Proof.
    intros H1.
    specialize (H1 [] Logic.eq_refl (to_cfg ([e'], ∅)) 0 []); simpl in H1.
    rewrite ?empty_env_subst in H1.
    iIntros "[#Hheap [#Hspec Hj]]".
    iApply wp_pvs.
    iApply wp_wand_l; iSplitR; [|iApply H1; iFrame "Hheap Hspec Hj"; trivial].
    iIntros {v} "H". iDestruct "H" as {v'} "[Hj _]".
    unfold Spec_ctx, auth.auth_ctx, auth.auth_inv, Spec_inv, tpool_mapsto,
    auth.auth_own.
    iInv> (N .@ 3) as {ρ} "[Hown %]".
    iCombine "Hj" "Hown" as "Hown".
    iDestruct (own_valid _ with "Hown !") as "Hvalid".
    iDestruct (auth_validI _ with "Hvalid") as "[Ha' %]";
      simpl; iClear "Hvalid".
    iDestruct "Ha'" as {ρ'} "Ha'"; iDestruct "Ha'" as %Ha'.
    rewrite ->(right_id _ _) in Ha'; setoid_subst.
    iPvsIntro; iSplitL.
    - iExists _. rewrite own_op. iDestruct "Hown" as "[Ho1 Ho2]".
      iSplitL; trivial.
    - iApply const_intro; eauto.
      rewrite from_to_cfg in H.
      destruct ρ' as [th hp]; unfold op, cmra_op in *; simpl in *.
      unfold prod_op, of_cfg in *; simpl in *.
      destruct th as [|r th]; simpl in *; eauto.
      destruct H0 as [Hx1 Hx2]. simpl in *.
      destruct r as [q r|]; simpl in *; eauto.
      inversion Hx1 as [|? ? Hx]; subst.
      apply frac_valid_inv_l in Hx. inversion Hx.
  Qed.

  Local Arguments of_heap : simpl never.

  Lemma basic_soundness e e' τ :
    @bin_log_related _ _ _ N Δφ [] e e' τ _ →
    ∀ v thp hp,
      rtc step ([e], ∅) ((# v) :: thp, hp) →
      (∃ thp' hp' v', rtc step ([e'], ∅) ((# v') :: thp', hp')).
  Proof.
    rewrite -of_empty_heap.
    intros H1 v thp hp H2.
    match goal with
      |- ?A =>
      eapply (@wp_adequacy_result
                lang _ ⊤ (λ _, A) e v thp (of_heap ∅)
                (to_globalF heapI_name (● (∅ : heapR))
                            ⋅ to_globalF cfg_name
                            (◯ ({[ 0 := Frac 1 (DecAgree e') ]},
                                ∅ : heapR) ⋅
                            ● ({[ 0 := Frac 1 (DecAgree e') ]},
                                ∅ : heapR))
                ) hp); eauto
    end.
    - admit.
    - iIntros "[Hp Hg]".
      rewrite ownership.ownG_op.
      repeat
        match goal with
          |- context [ (ownership.ownG (to_globalF ?gn ?A))] =>
          change (ownership.ownG (to_globalF gn A)) with
          (ghost_ownership.own gn A)
        end.
      rewrite own_op.
      iDestruct "Hg" as "[Hg1 [Hg2 Hg3]]".
      iPvs (inv_alloc (N .@ 2) _ (auth.auth_inv heapI_name heapI_inv)
            with "[Hg1 Hp]") as "#Hheap"; auto.
      + iNext. iExists _; iFrame "Hp". unfold ghost_ownership.own; trivial.
      + rewrite of_empty_heap.
        iPvs (inv_alloc (N .@ 3) _ (auth.auth_inv cfg_name
                                                  (Spec_inv (to_cfg ([e'], ∅))))
            with "[Hg3]") as "#Hspec"; auto.
        * iNext. iExists _. iFrame "Hg3".
          iApply const_intro; eauto.
          rewrite from_to_cfg.
          unfold of_cfg; simpl; rewrite of_empty_heap; constructor.
        * iApply wp_basic_soundness; eauto.
          unfold heapI_ctx, Spec_ctx, auth.auth_ctx, tpool_mapsto,
          auth.auth_own. iFrame "Hheap Hspec Hg2"; trivial.
  Admitted.

  Lemma Binary_Soundness Γ e e' τ :
    (∀ f, e.[iter (List.length Γ) up f] = e) →
    (∀ f, e'.[iter (List.length Γ) up f] = e') →
    (∀ Δ {HΔ : context_interp_Persistent Δ},
        @bin_log_related _ _ _ N Δ Γ e e' τ HΔ) →
    context_refines Γ e e' τ.
  Proof.
    intros H1 K HK htp hp v Hstp Hc Hc'.
    eapply basic_soundness; eauto.
    eapply bin_log_related_under_typed_context; eauto.
  Qed.

End Soundness.