From iris_logrel.stlc Require Export fundamental.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.

Lemma wp_soundness `{irisG lang Σ} e τ :
  [] ⊢ₜ e : τ → (True : iProp Σ) ⊢ WP e {{ ⟦ τ ⟧ }}.
Proof.
  iIntros (?) "". rewrite -(empty_env_subst e). iApply fundamental; eauto.
Qed.

Theorem soundness e τ e' thp :
  [] ⊢ₜ e : τ → rtc step ([e], ()) (thp, ()) → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' ().
Proof.
  intros. set (Σ := #[irisΣ state]).
  cut (adequate e () (λ _, True)); first (intros [_ Hsafe]; eauto).
  eapply (wp_adequacy Σ); iIntros (?) "Hσ".
  iApply wp_wand_l; iSplitR; [|by iApply wp_soundness]; eauto.
Qed.
