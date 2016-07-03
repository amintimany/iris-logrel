From iris_logrel.F_mu_ref Require Export fundamental.
From iris.proofmode Require Import tactics pviewshifts.
From iris.program_logic Require Import ownership adequacy auth.

Theorem soundness `{authG lang Σ heapUR} e τ e' thp σ σ' :
  (∀ `{heapG Σ}, [] ⊨ e : τ) →
  rtc step ([e], σ) (e' :: thp, σ') →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ?. eapply (wp_adequacy_reducible ⊤ (λ _, True%I));
    eauto using ucmra_unit_valid; last by constructor.
  iIntros "[Hemp _]".
  iPvs (heap_alloc with "Hemp") as {h} "[Hheap Hemp]"; first solve_ndisj.
  rewrite -(empty_env_subst e).
  iApply wp_wand_l; iSplitR; [|iApply Hlog]; eauto.
  repeat iSplit; eauto. by iApply interp_env_nil.
Qed.

Lemma type_soundness e τ e' thp σ σ' :
  [] ⊢ₜ e : τ →
  rtc step ([e], σ) (e' :: thp, σ') →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  set (Σ := #[ auth.authGF heapUR ]).
  intros Htyped. eapply (@soundness Σ _)=> ?. eapply fundamental, Htyped.
Qed.
