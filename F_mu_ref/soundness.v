From iris_logrel.F_mu_ref Require Export fundamental.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import auth.

Theorem soundness Σ `{irisPreG lang Σ, HAG: authG Σ heapUR} e τ e' thp σ σ' :
  (∀ `{heapG Σ}, log_typed [] e τ) →
  rtc step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ??. cut (adequate e σ (λ _, True)); first (intros [_ ?]; eauto).
  eapply (wp_adequacy Σ); iIntros (?) "Hσ". rewrite -(empty_env_subst e).
  iMod (auth_alloc to_heap ownP heapN _ σ with "[Hσ]") as (γ) "[??]".
  - auto using to_heap_valid.
  - by iNext.
  - iApply wp_wand_l; iSplitR; [|iApply (Hlog (HeapG _ _ _ γ))]; eauto.
    iSplit. by rewrite /heap_ctx. iApply (@interp_env_nil _ (HeapG _ _ _ γ)).
Qed.

Corollary type_soundness e τ e' thp σ σ' :
  [] ⊢ₜ e : τ →
  rtc step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros ??. set (Σ := #[irisΣ state ; authΣ heapUR ]).
  eapply (soundness Σ); eauto using fundamental.
Qed.
