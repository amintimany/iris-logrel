Require Import iris.proofmode.tactics.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import iris_logrel.stlc.lang iris_logrel.stlc.typing
        iris_logrel.stlc.rules iris_logrel.stlc.logrel
        iris_logrel.stlc.fundamental.
Require Import iris.program_logic.adequacy.
Import uPred.

Section Soundness.
  Definition Σ := #[].

  Lemma empty_env_subst e : e.[env_subst []] = e.
  Proof.
    replace (env_subst []) with ids by reflexivity.
    asimpl; trivial.
  Qed.

  Lemma wp_soundness e τ : typed [] e τ → True ⊢ WP e {{ @interp (globalF Σ) τ }}.
  Proof.
    iIntros {H} "".
    rewrite -(empty_env_subst e).
    iApply typed_interp; eauto.
  Qed.

  Theorem Soundness e τ :
    typed [] e τ →
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
End Soundness.
