Require Import iris.proofmode.tactics.
Require Import iris.program_logic.hoare.
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
    {|
      cofe_mor_car :=
        λ x,
        {|
          cofe_mor_car :=
            λ y, (True)%I
        |}
    |}.

  Global Instance free_context_interp_Persistent :
    context_interp_Persistent free_type_context.
  Proof. intros x v; apply const_persistent. Qed.

  Lemma wp_soundness e τ
    : typed [] e τ → True ⊢ WP e {{@interp (globalF Σ) τ free_type_context}}.
  Proof.
    iIntros {H} "".
    rewrite -(empty_env_subst e).
    iPoseProof (@typed_interp _ _ _ []) as "Hi"; eauto; try typeclasses eauto.
    iApply "Hi"; eauto.
  Qed.

  Theorem Soundness e τ :
    typed [] e τ →
    ∀ e' thp, rtc step ([e], tt) (e' :: thp, tt) →
              ¬ reducible e' tt → is_Some (to_val e').
  Proof.
    intros H1 e' thp Hstp Hnr.
    eapply wp_soundness in H1; eauto.
    edestruct(@wp_adequacy_reducible lang (globalF Σ) ⊤
                                     (interp τ free_type_context)
                                     e e' (e' :: thp) tt ∅) as [Ha|Ha];
      eauto using ucmra_unit_valid; try tauto.
    - iIntros "H". iApply H1.
    - constructor.
  Qed.

End Soundness.