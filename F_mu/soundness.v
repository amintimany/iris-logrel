From iris_logrel.F_mu Require Export fundamental.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.

Theorem soundness Σ e τ e' thp σ σ' :
  log_typed (Σ:=Σ) [] e τ →
  rtc step ([e], σ) (e' :: thp, σ') →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ?. eapply (wp_adequacy_reducible ⊤ (λ _, True%I));
    eauto using ucmra_unit_valid; last by constructor.
  iIntros "_". rewrite -(empty_env_subst e).
  iApply wp_wand_l; iSplitR; [|iApply Hlog]; eauto. by iApply interp_env_nil.
Qed.

Lemma type_soundness e τ e' thp σ σ' :
  [] ⊢ₜ e : τ →
  rtc step ([e], σ) (e' :: thp, σ') →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  set (Σ := #[]).
  intros Htyped. eapply (@soundness (globalF Σ)), fundamental, Htyped.
Qed.
