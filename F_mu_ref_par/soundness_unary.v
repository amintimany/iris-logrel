Require Import iris.proofmode.weakestpre iris.proofmode.tactics.
Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.auth.
Require Import F_mu_ref_par.lang F_mu_ref_par.typing F_mu_ref_par.rules
        F_mu_ref_par.logrel_unary F_mu_ref_par.fundamental_unary.
Require Import iris.program_logic.adequacy.
Import uPred.

Section Soundness.
  Context {Σ : gFunctors}
          {i : heapIG Σ}
          {S : namespace}.

  Lemma empty_env_subst e : e.[env_subst []] = e.
    replace (env_subst []) with (@ids expr _) by reflexivity.
    asimpl; trivial.
  Qed.

  Definition free_type_context: varC -n> valC -n> iPropG lang Σ :=
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
      heapI_ctx (S .@ 2) ⊢ WP e {{@interp Σ _ (S .@ 1) τ free_type_context}}.
  Proof.
    iIntros {H} "Hheap".
    rewrite -(empty_env_subst e).
    iPoseProof (@typed_interp _ _ (S .@ 1) (S .@ 2) _ _ []) as "Hi"; eauto;
      try typeclasses eauto.
    - intros l. apply ndot_preserve_disjoint_r, ndot_ne_disjoint; auto.
    - iApply "Hi"; iSplit; eauto.
  Qed.

  Theorem Soundness e τ :
    typed [] e τ →
    ∀ e' thp h, rtc step ([e], (of_heap ∅)) (e' :: thp, h) →
              ¬ reducible e' h → is_Some (to_val e').
  Proof.
    intros H1 e' thp h Hstp Hnr.
    eapply wp_soundness in H1; eauto.
    edestruct(@wp_adequacy_reducible lang _ ⊤
                                     (@interp _ _ (S .@ 1) τ free_type_context)
                                     e e' (e' :: thp) (of_heap ∅)
                                     (to_globalF heapI_name (● ∅)) h)
      as [Ha|Ha]; eauto; try tauto.
    - apply cmra_valid_validN => n.
      apply iprod_singleton_validN, singleton_validN, cmra_transport_validN.
      constructor; simpl; try rewrite cmra_unit_right_id; trivial.
      apply cmra_unit_validN.
    - iIntros "[Hp Hg]".
      iAssert (ghost_ownership.own heapI_name (● ∅)) as "Hg" with "[Hg]";
      [by unfold ghost_ownership.own|].
      iPvs (inv_alloc (S .@ 2) _ (auth.auth_inv heapI_name heapI_inv)
            with "[Hg Hp]") as "#Hown"; auto.
      + iNext. iExists _; iFrame "Hp Hg"; trivial.
      + iApply H1; by unfold heapI_ctx, auth.auth_ctx.
    - constructor.
  Qed.

End Soundness.