From iris_logrel.F_mu_ref_par Require Export fundamental_unary.
From iris.proofmode Require Import tactics pviewshifts.
From iris.program_logic Require Import adequacy.

Section Soundness.
  Definition Σ := #[ auth.authGF heapUR ].

  Definition free_type_context: varC -n> valC -n> iPropG lang Σ := λne x y,
    True%I.

  Lemma wp_soundness e τ :
    typed [] e τ →
    ownership.ownP ∅ ⊢ WP e {{v, ∃ H : heapIG Σ,
      interp (nroot .@ "Fμ,ref,par" .@ 1) τ free_type_context v }}.
  Proof.
    iIntros {H1} "Hemp".
    iPvs (heap_alloc (nroot .@ "Fμ,ref,par" .@ 2) _ _ _ _ with "Hemp")
      as {H} "[Hheap Hemp]".
    iApply wp_wand_l. iSplitR.
    { iIntros {v} "HΦ". iExists H. iExact "HΦ". }
    rewrite -(empty_env_subst e).
    iApply (@typed_interp _ H (nroot .@ "Fμ,ref,par" .@ 1)
                              (nroot .@ "Fμ,ref,par" .@ 2) _ _ []); eauto.
    intros l; apply ndot_preserve_disjoint_r, ndot_ne_disjoint; auto.
      Unshelve. all: trivial.
  Qed.

  Theorem Soundness e τ :
    typed [] e τ →
    ∀ e' thp h, rtc step ([e], (of_heap ∅)) (e' :: thp, h) →
              ¬reducible e' h → is_Some (to_val e').
  Proof.
    intros H1 e' thp h Hstp Hnr.
    eapply wp_soundness in H1; eauto.
    edestruct (@wp_adequacy_reducible lang (globalF Σ) ⊤ (λ v, (∃ H,
        @interp Σ H (nroot .@ "Fμ,ref,par" .@ 1) τ free_type_context v)%I)
      e e' (e' :: thp) ∅ ∅ h) as [Ha|Ha]; eauto; try tauto.
    - apply ucmra_unit_valid.
    - iIntros "[Hp Hg]". by iApply H1.
    - by rewrite of_empty_heap in Hstp.
    - constructor.
  Qed.
End Soundness.
