From iris_logrel.F_mu_ref Require Export fundamental.
From iris.proofmode Require Import tactics pviewshifts.
From iris.program_logic Require Import ownership adequacy.

Section Soundness.
  Definition Σ := #[ auth.authGF heapUR ].

  Lemma empty_env_subst e : e.[env_subst []] = e.
  Proof. change (env_subst []) with (@ids expr _). by asimpl. Qed.

  Definition free_type_context: varC -n> valC -n> iPropG lang Σ :=
    λne x y, True%I.

  Lemma wp_soundness e τ :
    [] ⊢ₜ e : τ →
    ownP ∅ ⊢ WP e {{ v, ∃ H : heapG Σ,
      interp (nroot .@ "Fμ,ref" .@ 1) τ free_type_context v}}.
  Proof.
    iIntros {H1} "Hemp".
    iPvs (heap_alloc (nroot .@ "Fμ,ref" .@ 2) with "Hemp")
      as {H} "[Hheap Hemp]"; first solve_ndisj.
    iApply wp_wand_l. iSplitR.
    { iIntros {v} "HΦ". iExists H. iExact "HΦ". }
    rewrite -(empty_env_subst e).
    iApply (@typed_interp _ _ (nroot .@ "Fμ,ref" .@ 1)
                              (nroot .@ "Fμ,ref" .@ 2) _ _ []); eauto.
    solve_ndisj.
  Qed.

  Local Arguments of_heap : simpl never.

  Theorem Soundness e τ :
    [] ⊢ₜ e : τ →
    ∀ e' thp h, rtc step ([e], (of_heap ∅)) (e' :: thp, h) →
              ¬ reducible e' h → is_Some (to_val e').
  Proof.
    intros H1 e' thp h Hstp Hnr.
    eapply wp_soundness in H1; eauto.
    edestruct (@wp_adequacy_reducible lang (globalF Σ) ⊤
                                     (λ v, (∃ H : heapG Σ,
                                         @interp Σ H (nroot .@ "Fμ,ref" .@ 1)
                                                 τ free_type_context v)%I)
                                     e e' (e' :: thp) ∅ ∅ h)
      as [Ha|Ha]; eauto; try tauto.
    - done.
    - iIntros "[Hp Hg]". by iApply H1.
    - by rewrite of_empty_heap in Hstp.
    - constructor.
  Qed.
End Soundness.
