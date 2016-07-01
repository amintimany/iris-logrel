From iris_logrel.stlc Require Export fundamental.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.

Section soundness.
  Let Σ := #[].

  Lemma wp_soundness e τ : [] ⊢ₜ e : τ → True ⊢ WP e {{ @interp (globalF Σ) τ }}.
  Proof.
    iIntros {H} "". rewrite -(empty_env_subst e). iApply typed_interp; eauto.
  Qed.

  Theorem soundness e τ e' thp :
    [] ⊢ₜ e : τ → rtc step ([e], ()) (e' :: thp, ()) →
    is_Some (to_val e') ∨ reducible e' ().
  Proof.
    intros. eapply wp_adequacy_reducible; eauto using ucmra_unit_valid.
    - iIntros "H". by iApply wp_soundness.
    - constructor.
  Qed.
End soundness.
