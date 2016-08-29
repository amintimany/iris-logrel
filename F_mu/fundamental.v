From iris_logrel.F_mu Require Export logrel.
From iris.proofmode Require Import tactics.
From iris_logrel.F_mu Require Import rules.
From iris.algebra Require Export upred_big_op.

Definition log_typed `{irisG lang Σ} (Γ : list type) (e : expr) (τ : type) := ∀ Δ vs,
  env_PersistentP Δ →
  ⟦ Γ ⟧* Δ vs ⊢ ⟦ τ ⟧ₑ Δ e.[env_subst vs].
Notation "Γ ⊨ e : τ" := (log_typed Γ e τ) (at level 74, e, τ at next level).

Section fundamental.
  Context `{irisG lang Σ}.

  Notation D := (valC -n> iProp Σ).

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (wp_bind [ctx]);
    iApply wp_wand_l;
    iSplitL; [|iApply Hp; trivial]; cbn;
    iIntros (v) Hv.

  Local Ltac value_case := iApply wp_value; cbn; rewrite ?to_of_val; trivial.

  Theorem fundamental Γ e τ : Γ ⊢ₜ e : τ → log_typed Γ e τ.
  Proof.
    induction 1; iIntros (Δ vs HΔ) "#HΓ"; cbn.
    - (* var *)
      iDestruct (interp_env_Some_l with "HΓ") as (v) "[% ?]"; first done.
      rewrite /env_subst. simplify_option_eq. by value_case.
    - (* unit *) value_case.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) v "# Hv" IHtyped1.
      smart_wp_bind (PairRCtx v) v' "# Hv'" IHtyped2.
      value_case; eauto 10.
    - (* fst *)
      smart_wp_bind (FstCtx) v "# Hv" IHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_fst; eauto using to_of_val.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" IHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_snd; eauto using to_of_val.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHtyped; cbn.
      value_case; eauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHtyped; cbn.
      value_case; eauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v "#Hv" IHtyped1; cbn.
      iDestruct (interp_env_length with "HΓ") as %?.
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[% Hw]"; simplify_eq/=.
      + iApply wp_case_inl; auto 1 using to_of_val; asimpl. iNext.
        erewrite typed_subst_head_simpl by naive_solver.
        iApply (IHtyped2 Δ (w :: vs)). iApply interp_env_cons; auto.
      + iApply wp_case_inr; auto 1 using to_of_val; asimpl. iNext.
        erewrite typed_subst_head_simpl by naive_solver.
        iApply (IHtyped3 Δ (w :: vs)). iApply interp_env_cons; auto.
    - (* lam *)
      value_case; iAlways; iIntros (w) "#Hw".
      iDestruct (interp_env_length with "HΓ") as %?.
      iApply wp_lam; auto 1 using to_of_val. iNext.
      asimpl. erewrite typed_subst_head_simpl by naive_solver.
      iApply (IHtyped Δ (w :: vs)). iApply interp_env_cons; auto.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHtyped2.
      iApply wp_mono; [|iApply "Hv"]; auto.
    - (* TLam *)
      value_case.
      iAlways; iIntros (τi) "%". iApply wp_tlam; iNext.
      iApply IHtyped. by iApply interp_env_ren.
    - (* TApp *)
      smart_wp_bind TAppCtx v "#Hv" IHtyped; cbn.
      iApply wp_wand_r; iSplitL; [iApply ("Hv" $! (⟦ τ' ⟧ Δ)); iPureIntro; apply _|].
      iIntros (w) "?". by rewrite interp_subst.
    - (* Fold *)
      iApply (wp_bind [FoldCtx]);
        iApply wp_wand_l; iSplitL; [|iApply (IHtyped Δ vs); auto].
      iIntros (v) "#Hv". value_case.
      rewrite /= -interp_subst fixpoint_unfold /=.
      iAlways; eauto.
    - (* Unfold *)
      iApply (wp_bind [UnfoldCtx]);
        iApply wp_wand_l; iSplitL; [|iApply IHtyped; trivial].
      iIntros (v) "#Hv". rewrite /= fixpoint_unfold.
      change (fixpoint _) with (⟦ TRec τ ⟧ Δ); simpl.
      iDestruct "Hv" as (w) "#[% Hw]"; subst; simpl.
      iApply wp_fold. by rewrite to_of_val.
      iNext. by rewrite -interp_subst.
  Qed.
End fundamental.
