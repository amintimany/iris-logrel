From iris_logrel.F_mu_ref_conc Require Export fundamental_unary.
From iris.proofmode Require Import tactics pviewshifts.
From iris.program_logic Require Import ownership adequacy auth.

Theorem soundness Σ `{irisPreG lang Σ, authG Σ heapUR} e τ e' thp σ σ' :
  (∀ `{heapIG Σ}, log_typed [] e τ) →
  rtc step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ??. cut (adequate e σ (λ _, True)); first (intros [_ ?]; eauto).
  eapply (wp_adequacy Σ); iIntros (?) "Hσ". rewrite -(empty_env_subst e).
  iVs (auth_alloc (ownP ∘ of_heap) heapN _ (to_heap σ) with "[Hσ]") as (γ) "[??]".
  - auto using to_heap_valid.
  - rewrite /= (from_to_heap σ); auto.
  - iApply wp_wand_l; iSplitR; [|iApply (Hlog (HeapIG _ _ _ γ))]; eauto.
    iSplit. by rewrite /heapI_ctx. iApply (@interp_env_nil _ (HeapIG _ _ _ γ)).
Qed.

Corollary type_soundness e τ e' thp σ σ' :
  [] ⊢ₜ e : τ →
  rtc step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros ??. set (Σ := #[irisΣ lang ; authΣ heapUR ]).
  eapply (soundness Σ); eauto using fundamental.
Qed.
