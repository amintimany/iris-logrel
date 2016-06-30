From iris_logrel.stlc Require Export fundamental.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.

Section soundness.
  Let Σ := #[].

  Lemma empty_env_subst e : e.[env_subst []] = e.
  Proof. change (env_subst []) with ids. by asimpl. Qed.

  Lemma wp_soundness e τ : [] ⊢ₜ e : τ → True ⊢ WP e {{ @interp (globalF Σ) τ }}.
  Proof.
    iIntros {H} "".
    rewrite -(empty_env_subst e).
    iApply typed_interp; eauto.
  Qed.

  Theorem Soundness e τ :
    [] ⊢ₜ e : τ →
    ∀ e' thp, rtc step ([e], tt) (e' :: thp, tt) →
              ¬ reducible e' tt → is_Some (to_val e').
  Proof.
    intros H1 e' thp Hstp Hnr.
    apply wp_soundness in H1.
    edestruct(@wp_adequacy_reducible lang (globalF Σ) ⊤
                                     (interp τ) e e' (e' :: thp) tt ∅)
      as [Ha|Ha]; eauto using ucmra_unit_valid; try tauto.
    - iIntros "H". iApply H1.
    - constructor.
  Qed.
End soundness.
