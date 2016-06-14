Require Import iris.proofmode.tactics.
Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import iris_logrel.stlc.lang iris_logrel.stlc.typing
        iris_logrel.stlc.rules iris_logrel.stlc.logrel.
Import uPred.

Section typed_interp.
  Context {Σ : iFunctor}.

  Local Hint Extern 1 =>
  match goal with
    |-
    (_
       --------------------------------------□
       ∃ _ : ?A, _) => let W := fresh "W" in evar (W : A); iExists W; unfold W; clear W
  end : itauto.

  Local Hint Extern 1 =>
  match goal with
    |-
    (_
       --------------------------------------□
       ▷ _) => iNext
  end : itauto.

  Local Hint Extern 1 =>
  match goal with
    |-
    (_
       --------------------------------------□
       (_ ∧ _)) => iSplit
  end : itauto.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) constr(Hp) :=
    iApply (@wp_bind _ _ _ [ctx]);
    iApply wp_impl_l;
    iSplit; [| iApply Hp; trivial]; cbn;
    eapply (@always_intro _ _ _ _);
    iIntros {v} Hv.

  Local Ltac value_case := iApply wp_value; cbn; rewrite ?to_of_val; trivial.

  Lemma typed_interp Γ vs e τ :
    typed Γ e τ → length Γ = length vs →
    Π∧ zip_with (@interp Σ) Γ vs ⊢ wp ⊤ (e.[env_subst vs]) (interp τ).
  Proof.
    intros Htyped; revert vs.
    induction Htyped; intros vs Hlen; iIntros "#Hctx"; cbn.
    - (* var *)
      destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
      { by rewrite -Hlen; apply lookup_lt_Some with τ. }
      rewrite /env_subst Hv. value_case.
      iApply big_and_elem_of; eauto.
      apply elem_of_list_lookup_2 with x.
      rewrite lookup_zip_with; simplify_option_eq; trivial.
    - (* unit *) value_case.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) v "# Hv" IHHtyped1.
      smart_wp_bind (PairRCtx v) v' "# Hv'" IHHtyped2.
      value_case; eauto 10 with itauto.
    - (* fst *)
      smart_wp_bind (FstCtx) v "# Hv" IHHtyped; cbn.
      iApply double_exists; [|trivial].
      intros w w'; cbn; iIntros "#[% [H2 H3]]"; rewrite H.
      iApply wp_fst; try iNext; eauto using to_of_val.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" IHHtyped; cbn.
      iApply double_exists; [|trivial].
      intros w w'; cbn; iIntros "#[% [H2 H3]]"; rewrite H.
      iApply wp_snd; try iNext; eauto using to_of_val.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHHtyped; value_case.
      iLeft; iExists v; auto with itauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHHtyped; value_case.
      iRight; iExists v; auto with itauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v "#Hv" IHHtyped1; cbn.
      iDestruct "Hv" as "[Hv|Hv]"; eauto; iRevert "Hctx";
        iApply exist_elim; eauto; cbn;
          iIntros {w} "#[% Hw2] #Hctx"; rewrite H; cbn;
            [iApply wp_case_inl|iApply wp_case_inr];
            auto 1 using to_of_val;
            asimpl; [specialize (IHHtyped2 (w::vs)) | specialize (IHHtyped3 (w::vs))];
              erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto); iNext;
                [iApply IHHtyped2 | iApply IHHtyped3]; cbn; auto with itauto.
    - (* lam *)
      value_case; apply (always_intro _ _); iIntros {w} "#Hw".
      iApply wp_lam; auto 1 using to_of_val.
      asimpl; erewrite typed_subst_head_simpl; [|eauto|cbn]; eauto.
      iNext; iApply (IHHtyped (w :: vs)); cbn; auto with itauto.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHHtyped2.
      iApply "Hv"; auto with itauto.
  Qed.

End typed_interp.