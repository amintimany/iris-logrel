Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import stlc.lang stlc.typing stlc.rules stlc.logrel.
Import uPred.

Section typed_interp.
  Context {Σ : iFunctor}.
  Notation "# v" := (of_val v) (at level 20).

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) uconstr(t) ident(v) :=
    rewrite -(@wp_bind _ _ _ [ctx]) /= -wp_impl_l; apply and_intro; eauto with itauto;
    apply (@always_intro _ _ _ t), forall_intro=> v /=; apply impl_intro_l.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) :=
    rewrite -(@wp_bind _ _ _ [ctx]) /= -wp_mono; eauto; intros v; cbn.

  Local Hint Extern 1 ((_ ∧ _) ⊢ _)%I => rewrite and_elim_r : itauto.
  Local Hint Extern 1 ((_ ∧ _) ⊢ _)%I => rewrite and_elim_l : itauto.
  Local Hint Extern 1 (_ ⊢ (_ ∧ _))%I => repeat eapply and_intro : itauto.
  Local Hint Extern 1 (_ ⊢ ▷ _)%I => rewrite -later_intro : itauto.
  Local Hint Extern 1 (_ ⊢ ∃ _, _)%I => rewrite -exist_intro : itauto.
  Local Hint Extern 1 (_ ⊢ (_ ∨ _))%I => rewrite -or_intro_l : itauto.
  Local Hint Extern 1 (_ ⊢ (_ ∨ _))%I => rewrite -or_intro_r : itauto.

  Local Ltac value_case := rewrite -wp_value/= ?to_of_val //; auto.


  Lemma typed_interp Γ vs e τ :
    typed Γ e τ → length Γ = length vs →
    Π∧ zip_with (@interp Σ) Γ vs ⊢ wp ⊤ (e.[env_subst vs]) (interp τ).
  Proof.
    intros Htyped; revert vs.
    induction Htyped; intros vs Hlen; cbn.
    - (* var *)
      destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
      { by rewrite -Hlen; apply lookup_lt_Some with τ. }
      rewrite /env_subst Hv /= -wp_value; eauto using to_of_val.
      apply big_and_elem_of, elem_of_list_lookup_2 with x.
        by rewrite lookup_zip_with; simplify_option_eq.
    - (* unit *) value_case.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) _ v.
      (* weird!: and_alwaysstable is an instance but is not resolved! *)
      smart_wp_bind (PairRCtx v) (and_persistent _ _ _ _) v'.
      value_case; eauto 10 with itauto.
    - (* fst *)
      smart_wp_bind (FstCtx) v.
      rewrite exist_elim; eauto; intros v1. rewrite exist_elim; eauto; intros v2.
      apply const_elim_l; intros H; rewrite H.
      rewrite -wp_fst; eauto using to_of_val, and_elim_l.
    - (* snd *)
      smart_wp_bind SndCtx v.
      rewrite exist_elim; eauto; intros v1. rewrite exist_elim; eauto; intros v2.
      apply const_elim_l; intros H; rewrite H.
      rewrite -wp_snd; eauto using to_of_val, and_elim_r.
    - (* injl *) smart_wp_bind InjLCtx v; value_case; eauto 7 with itauto.
    - (* injr *) smart_wp_bind InjRCtx v; value_case; eauto 7 with itauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) _ v.
      rewrite (later_intro (Π∧ zip_with interp Γ vs)).
      rewrite or_elim; [apply impl_elim_l| |];
      rewrite exist_elim; eauto; [intros v1| intros v2];
      apply const_elim_l; intros H; rewrite H;
      rewrite -impl_intro_r //; rewrite -later_and later_mono; eauto;
      [rewrite -wp_case_inl | rewrite -wp_case_inr]; eauto using to_of_val;
      asimpl; [specialize (IHHtyped2 (v1::vs)) | specialize (IHHtyped3 (v2::vs))];
      erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto);
      [rewrite -IHHtyped2 | rewrite -IHHtyped3]; cbn; auto.
    - (* lam *)
      value_case; apply (always_intro _ _), forall_intro=> v /=; apply impl_intro_l.
      rewrite -wp_lam ?to_of_val //=.
      asimpl. erewrite typed_subst_head_simpl; [|eauto|cbn]; eauto.
      rewrite (later_intro (Π∧ _)) -later_and; apply later_mono.
      apply (IHHtyped (v :: vs)); simpl; auto with f_equal.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) _ v.
      rewrite -(@wp_bind _ _ _ [AppRCtx v]) /=.
      rewrite -wp_impl_l /=; apply and_intro.
      2: etransitivity; [|apply IHHtyped2]; eauto using and_elim_r.
      rewrite and_elim_l. apply always_mono.
      apply forall_intro =>v'.
      rewrite forall_elim.
      apply impl_intro_l.
      rewrite (later_intro (interp τ1 v')).
      apply impl_elim_r.
  Qed.

End typed_interp.