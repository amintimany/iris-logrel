Require Import iris.proofmode.weakestpre iris.proofmode.tactics.
Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.auth.
Require Import iris_logrel.F_mu_ref.lang iris_logrel.F_mu_ref.typing
        iris_logrel.F_mu_ref.rules iris_logrel.F_mu_ref.logrel
        iris_logrel.F_mu_ref.fundamental.
Require Import iris.program_logic.adequacy.
Import uPred.

Section Soundness.
  Definition Σ := #[ auth.authGF heapR ].

  Lemma empty_env_subst e : e.[env_subst []] = e.
    replace (env_subst []) with (@ids expr _) by reflexivity.
    asimpl; trivial.
  Qed.

  Definition free_type_context: leibniz_var -n> leibniz_val -n> iPropG lang Σ :=
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
    : typed [] e τ →
      (ownership.ownP ∅)
        ⊢ WP e {{v, ∃ H, @interp Σ H (nroot .@ "Fμ,ref" .@ 1)
                              τ free_type_context v}}.
  Proof.
    iIntros {H1} "Hemp".
    iDestruct (heap_alloc (nroot .@ "Fμ,ref" .@ 2) _ _ _ _ with "Hemp") as "Hp".
    iPvs "Hp" as {H} "[Hheap Hemp]".
    iApply wp_wand_l. iSplitR.
    { iIntros {v} "HΦ". iExists H. iExact "HΦ". }
    rewrite -(empty_env_subst e).
    iPoseProof (@typed_interp _ _ (nroot .@ "Fμ,ref" .@ 1)
                              (nroot .@ "Fμ,ref" .@ 2) _ _ []) as "Hi"; eauto;
      try typeclasses eauto.
    - intros l. apply ndot_preserve_disjoint_r, ndot_ne_disjoint; auto.
    - iApply "Hi"; iSplit; eauto.
      Unshelve. all: trivial.
  Qed.

  Local Arguments of_heap : simpl never.

  Theorem Soundness e τ :
    typed [] e τ →
    ∀ e' thp h, rtc step ([e], (of_heap ∅)) (e' :: thp, h) →
              ¬ reducible e' h → is_Some (to_val e').
  Proof.
    intros H1 e' thp h Hstp Hnr.
    eapply wp_soundness in H1; eauto.
    edestruct(@wp_adequacy_reducible lang (globalF Σ) ⊤
                                     (λ v, (∃ H : heapG Σ,
                                         @interp Σ H (nroot .@ "Fμ,ref" .@ 1)
                                                 τ free_type_context v)%I)
                                     e e' (e' :: thp) ∅ ∅ h)
      as [Ha|Ha]; eauto; try tauto.
    - apply cmra_unit_valid.
    - iIntros "[Hp Hg]". by iApply H1.
    - by rewrite of_empty_heap in Hstp.
    - constructor.
  Qed.

End Soundness.