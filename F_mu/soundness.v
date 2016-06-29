Require Import iris.proofmode.tactics.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import iris_logrel.F_mu.lang iris_logrel.F_mu.typing
        iris_logrel.F_mu.rules iris_logrel.F_mu.logrel
        iris_logrel.F_mu.fundamental.
Require Import iris.program_logic.adequacy.
Import uPred.

Section Soundness.
  Definition Σ := #[].

  Lemma empty_env_subst e : e.[env_subst []] = e.
  Proof.
    replace (env_subst []) with (@ids expr _) by reflexivity.
    asimpl; trivial.
  Qed.

  Definition free_type_context : varC -n> valC -n> iProp lang (globalF Σ) :=
    λne x y, True%I.

  Lemma wp_soundness e τ :
    typed [] e τ → True ⊢ WP e {{ @interp (globalF Σ) τ free_type_context }}.
  Proof.
    iIntros {H} "". rewrite -(empty_env_subst e).
    by iApply (@typed_interp _ _ _ []).
  Qed.

  Theorem Soundness e τ :
    typed [] e τ →
    ∀ e' thp, rtc step ([e], tt) (e' :: thp, tt) →
              ¬ reducible e' tt → is_Some (to_val e').
  Proof.
    intros H1 e' thp Hstp Hnr.
    eapply wp_soundness in H1; eauto.
    edestruct (@wp_adequacy_reducible lang (globalF Σ) ⊤
                                     (interp τ free_type_context)
                                     e e' (e' :: thp) tt ∅) as [Ha|Ha];
      eauto using ucmra_unit_valid; try tauto.
    - iIntros "H". iApply H1.
    - constructor.
  Qed.
End Soundness.
