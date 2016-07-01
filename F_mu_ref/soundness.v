From iris_logrel.F_mu_ref Require Export fundamental.
From iris.proofmode Require Import tactics pviewshifts.
From iris.program_logic Require Import ownership adequacy.

Section soundness.
  Let Σ := #[ auth.authGF heapUR ].

  Lemma wp_soundness e τ σ :
    [] ⊢ₜ e : τ →
    ownP σ ⊢ WP e {{ v, ∃ H : heapG Σ, interp τ [] v}}.
  Proof.
    iIntros {H1} "Hemp".
    iPvs (heap_alloc with "Hemp") as {H} "[Hheap Hemp]"; first solve_ndisj.
    iApply wp_wand_l. iSplitR.
    { iIntros {v} "HΦ". iExists H. iExact "HΦ". }
    rewrite -(empty_env_subst e). iApply typed_interp; eauto.
  Qed.

  Theorem soundness e τ e' thp σ σ' :
    [] ⊢ₜ e : τ → rtc step ([e], σ) (e' :: thp, σ') →
    is_Some (to_val e') ∨ reducible e' σ'.
  Proof.
    intros ??. eapply wp_adequacy_reducible; eauto using ucmra_unit_valid.
    - iIntros "[??]". by iApply wp_soundness.
    - constructor.
  Qed.
End soundness.
