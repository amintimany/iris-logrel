From iris_logrel.F_mu Require Export logrel.
From iris.proofmode Require Import tactics.
From iris_logrel.F_mu Require Import rules.
From iris.algebra Require Export upred_big_op.

Section typed_interp.
  Context {Σ : iFunctor}.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (@wp_bind _ _ _ [ctx]);
    iApply wp_wand_l;
    iSplitL; [|iApply Hp; trivial]; cbn;
    iIntros {v} Hv.

  Local Ltac value_case := iApply wp_value; cbn; rewrite ?to_of_val; trivial.

  Lemma typed_interp (Δ : varC -n> valC -n> iProp lang Σ) Γ vs e τ
      (Htyped : typed Γ e τ) (HΔ : ∀ x v, PersistentP (Δ x v)) :
    length Γ = length vs →
    [∧] zip_with (λ τ, interp τ Δ) Γ vs ⊢ WP e.[env_subst vs] {{ interp τ Δ }}.
  Proof.
    revert Δ HΔ vs. induction Htyped; iIntros {Δ HΔ vs Hlen} "#HΓ"; cbn.
    - (* var *)
      destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
      { by rewrite -Hlen; apply lookup_lt_Some with τ. }
      rewrite /env_subst Hv; value_case.
      iApply (big_and_elem_of with "HΓ").
      apply elem_of_list_lookup_2 with x.
      rewrite lookup_zip_with; simplify_option_eq; trivial.
    - (* unit *) value_case.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) v "# Hv" IHHtyped1.
      smart_wp_bind (PairRCtx v) v' "# Hv'" IHHtyped2.
      value_case; eauto 10.
    - (* fst *)
      smart_wp_bind (FstCtx) v "# Hv" IHHtyped; cbn.
      iDestruct "Hv" as {w1 w2} "#[% [H2 H3]]"; subst.
      iApply wp_fst; eauto using to_of_val.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" IHHtyped; cbn.
      iDestruct "Hv" as {w1 w2} "#[% [H2 H3]]"; subst.
      iApply wp_snd; eauto using to_of_val.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHHtyped; cbn.
      value_case; eauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHHtyped; cbn.
      value_case; eauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v "#Hv" IHHtyped1; cbn.
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as {w} "[% Hw]"; subst.
      + iApply wp_case_inl; auto 1 using to_of_val; asimpl.
        specialize (IHHtyped2 Δ HΔ (w::vs)).
        erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto).
        iNext; iApply IHHtyped2; cbn; auto.
      + iApply wp_case_inr; auto 1 using to_of_val; asimpl.
        specialize (IHHtyped3 Δ HΔ (w::vs)).
        erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto).
        iNext; iApply IHHtyped3; cbn; auto.
    - (* lam *)
      value_case; iAlways; iIntros {w} "#Hw".
      iApply wp_lam; auto 1 using to_of_val.
      asimpl; erewrite typed_subst_head_simpl; [|eauto|cbn]; eauto.
      iNext; iApply (IHHtyped Δ HΔ (w :: vs)); cbn; auto.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHHtyped2.
      iApply wp_mono; [|iApply "Hv"]; auto.
    - (* TLam *)
      value_case.
      iIntros { τi } "! %". iApply wp_TLam; iNext; simpl in *.
      iApply (IHHtyped (extend_context_interp_fun1 τi Δ)); [rewrite map_length|]; trivial.
      by iDestruct (zip_with_context_interp_subst with "HΓ") as "?".
    - (* TApp *)
      smart_wp_bind TAppCtx v "#Hv" IHHtyped; cbn.
      iApply wp_wand_r; iSplitL; [iApply ("Hv" $! (interp τ' Δ)); iPureIntro; apply _|].
      iIntros{w} "?". by rewrite interp_subst.
    - (* Fold *)
      rewrite map_length in IHHtyped.
      iApply (@wp_bind _ _ _ [FoldCtx]).
        iApply wp_wand_l.
        iSplitL; [|iApply (IHHtyped (extend_context_interp ((interp (TRec τ)) Δ) Δ));
                 trivial].
      + iIntros {v} "#Hv".
        value_case.
        change (fixpoint _) with (interp (TRec τ) Δ) at 1; trivial.
        rewrite fixpoint_unfold; cbn.
        iAlways; eauto.
      + by iDestruct (zip_with_context_interp_subst with "HΓ") as "?".
    - (* Unfold *)
      iApply (@wp_bind _ _ _ [UnfoldCtx]);
        iApply wp_wand_l; iSplitL; [|iApply IHHtyped; trivial].
      iIntros {v}.
      cbn [interp interp_rec cofe_mor_car].
      rewrite fixpoint_unfold.
      iIntros "#Hv"; cbn.
      change (fixpoint _) with (interp (TRec τ) Δ).
      iDestruct "Hv" as {w} "[% #Hw]"; rewrite H.
      iApply wp_Fold; cbn; auto using to_of_val.
      rewrite -interp_subst; trivial.
  Qed.
End typed_interp.
