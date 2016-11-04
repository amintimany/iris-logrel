From iris_logrel.F_mu Require Export fundamental.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.

Theorem soundness Σ `{irisPreG lang Σ} e τ e' thp σ σ' :
  (∀ `{irisG lang Σ}, log_typed [] e τ) →
  rtc step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ??. cut (adequate e σ (λ _, True)); first (intros [_ ?]; eauto).
  eapply (wp_adequacy Σ); iIntros (?) "Hσ". rewrite -(empty_env_subst e).
  iApply wp_wand_l; iSplitR; [|iApply Hlog]; eauto. by iApply interp_env_nil.
Qed.

Corollary type_soundness e τ e' thp σ σ' :
  [] ⊢ₜ e : τ →
  rtc step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros ??. set (Σ := #[irisΣ state]).
  eapply (soundness Σ); eauto using fundamental.
Qed.
