Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import F_mu_ref.lang F_mu_ref.typing F_mu_ref.rules F_mu_ref.logrel.
From iris.program_logic Require Export lifting.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
Require Import Vlist.
Import uPred.

Section typed_interp.
  Context
    {Σ : gFunctors}
    `{i : heapG Σ}
    `{L : namespace}.
  
  Implicit Types P Q R : iPropG lang Σ.
  Notation "# v" := (of_val v) (at level 20).

  Local Ltac ipropsimpl :=
    repeat
      match goal with
      | [|- (_ ⊢ (_ ∧ _))%I] => eapply and_intro
      | [|- (▷ _ ⊢ ▷ _)%I] => apply later_mono
      | [|- (_ ⊢ ∃ _, _)%I] => rewrite -exist_intro
      | [|- ((∃ _, _) ⊢ _)%I] => let v := fresh "v" in rewrite exist_elim; [|intros v]
      end.

  Local Hint Extern 1 => progress ipropsimpl.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) uconstr(t) ident(v) :=
    rewrite -(@wp_bind _ _ _ [ctx]) /= -wp_impl_l; apply and_intro; [
    apply (@always_intro _ _ _ t), forall_intro=> v /=; apply impl_intro_l| eauto with itauto].

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) :=
    rewrite -(@wp_bind _ _ _ [ctx]) /= -wp_mono; eauto; intros v; cbn.

  Create HintDb itauto.

  Local Hint Extern 3 ((_ ∧ _) ⊢ _)%I => rewrite and_elim_r : itauto.
  Local Hint Extern 3 ((_ ∧ _) ⊢ _)%I => rewrite and_elim_l : itauto.
  Local Hint Extern 3 (_ ⊢ (_ ∨ _))%I => rewrite -or_intro_l : itauto.
  Local Hint Extern 3 (_ ⊢ (_ ∨ _))%I => rewrite -or_intro_r : itauto.
  Local Hint Extern 2 (_ ⊢ ▷ _)%I => etransitivity; [|rewrite -later_intro] : itauto.
  
  Local Ltac value_case := rewrite -wp_value/= ?to_of_val //; auto 2.

  Lemma typed_interp N k Δ Γ vs e τ
        (HNLdisj : ∀ l : loc, N ⊥ L .@ l)
        (Htyped : typed k Γ e τ)
        (Hctx : closed_ctx k Γ)
        (HC : closed_type k τ)
        (HΔ : VlistAlwaysStable Δ)
    : length Γ = length vs →
      (heap_ctx N ∧ Π∧ zip_with (λ τ v, (@interp Σ i L) k (` τ) (proj2_sig τ) Δ v) (closed_ctx_list _ Γ Hctx) vs)%I ⊢
                  WP (e.[env_subst vs]) @ ⊤ {{ λ v, (@interp Σ i L) k τ HC Δ v }}.
  Proof.
    revert Hctx HC HΔ vs.
    induction Htyped; intros Hctx HC HΔ vs Hlen; cbn.
    - (* var *)
      destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
      { by rewrite -Hlen; apply lookup_lt_Some with τ. }
      rewrite /env_subst Hv /= -wp_value; eauto using to_of_val.
      edestruct (zipwith_Forall_lookup _ Hctx) as [Hτ' Hτ'eq]; eauto.
      rewrite and_elim_r.
      etransitivity.
      apply big_and_elem_of, elem_of_list_lookup_2 with x.
      rewrite lookup_zip_with; simplify_option_eq; trivial.
      rewrite interp_closed_irrel; trivial.
    - (* unit *) value_case.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) _ v; eauto.
      (* weird!: and_alwaysstable is an instance but is not resolved! *)
      smart_wp_bind (PairRCtx v) (and_persistent _ _ _ _) v'.
      value_case; eauto 10 with itauto.
    - (* fst *)
      smart_wp_bind (FstCtx) v. ipropsimpl; eauto.
      apply const_elim_l; intros H; rewrite H.
      rewrite -wp_fst; eauto using to_of_val, and_elim_l.
      rewrite and_elim_l; rewrite interp_closed_irrel; eauto.
    - (* snd *)
      smart_wp_bind SndCtx v. ipropsimpl; eauto.
      apply const_elim_l; intros H; rewrite H.
      rewrite -wp_snd; eauto using to_of_val, and_elim_l.
      rewrite and_elim_r; rewrite interp_closed_irrel; eauto.
    - (* injl *) smart_wp_bind InjLCtx v; value_case; eauto 7 with itauto.
    - (* injr *) smart_wp_bind InjRCtx v; value_case; eauto 7 with itauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) _ v. cbn.
      rewrite (later_intro (heap_ctx N ∧ Π∧ zip_with
           (λ (τ : {τ : type | closed_type k τ}) (v0 : leibniz_val),
            ((interp k (` τ) (proj2_sig τ)) Δ) v0) (closed_ctx_list k Γ Hctx) vs));
        rewrite or_elim; [apply impl_elim_l| |].
      + rewrite exist_elim; eauto; intros v'.
        apply const_elim_l; intros H; rewrite H.
        rewrite -impl_intro_r //; rewrite -later_and later_mono; eauto.
        rewrite -wp_case_inl; eauto using to_of_val.
        asimpl.
        specialize (IHHtyped2 Δ (typed_closed_ctx _ _ _ _ Htyped2) HC HΔ (v'::vs)).
        erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto).
        rewrite -IHHtyped2; cbn; auto.
        rewrite interp_closed_irrel type_context_closed_irrel /closed_ctx_list.
        apply later_mono; repeat apply and_intro; eauto 3 with itauto.
      + rewrite exist_elim; eauto; intros v'.
        apply const_elim_l; intros H; rewrite H.
        rewrite -impl_intro_r //; rewrite -later_and later_mono; eauto.
        rewrite -wp_case_inr; eauto using to_of_val.
        asimpl.
        specialize (IHHtyped3 Δ (typed_closed_ctx _ _ _ _ Htyped3) HC HΔ (v'::vs)).
        erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto).
        rewrite -IHHtyped3; cbn; auto.
        rewrite interp_closed_irrel type_context_closed_irrel /closed_ctx_list.
        apply later_mono; repeat apply and_intro; eauto 3 with itauto.
    - (* lam *)
      value_case; apply (always_intro _ _), forall_intro=> v /=; apply impl_intro_l.
      rewrite -wp_lam ?to_of_val //=.
      asimpl. erewrite typed_subst_head_simpl; [|eauto|cbn]; eauto.
      rewrite (later_intro (heap_ctx N ∧ Π∧ _)) -later_and; apply later_mono.
      rewrite interp_closed_irrel type_context_closed_irrel /closed_ctx_list.
      rewrite -(IHHtyped Δ (typed_closed_ctx _ _ _ _ Htyped) (closed_type_arrow_2 HC) HΔ (v :: vs)); cbn; auto 2 with f_equal.
      repeat apply and_intro; eauto 3 with itauto.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) _ v.
      rewrite -(@wp_bind _ _ _ [AppRCtx v]) /=.
      rewrite -wp_impl_l /=; apply and_intro.
      2: etransitivity; [|apply IHHtyped2]; eauto using and_elim_r.
      rewrite and_elim_l. apply always_mono.
      apply forall_intro =>v'.
      rewrite forall_elim.
      apply impl_intro_l.
      rewrite -(later_intro).
      etransitivity; [apply impl_elim_r|].
      apply wp_mono => w.
      rewrite interp_closed_irrel; trivial.
    - (* TLam *)
      value_case; rewrite -exist_intro; apply and_intro; auto.
      apply forall_intro =>τi;
        apply (always_intro _ _).
      rewrite map_length in IHHtyped.
      destruct τi as [τi τiAS].
      specialize (IHHtyped
                    (Vlist_cons τi Δ)
                    (closed_ctx_map
                       _ _ _ _
                       Hctx (λ τ, closed_type_S_ren2 τ 1 0 _))
                    (closed_type_forall HC)
                    (alwyas_stable_Vlist_cons _ _ _ τiAS)
                    _
                    Hlen
                 ).
      rewrite -wp_impl_l -later_intro. apply and_intro;
        [ apply (always_intro _ _), forall_intro=> v /=; apply impl_intro_l|].
      2: etransitivity; [|apply IHHtyped].
      + rewrite and_elim_l; trivial.
      + rewrite zip_with_closed_ctx_list_subst; trivial.
    - (* TApp *)
      smart_wp_bind TAppCtx _ v; cbn.
      rewrite and_elim_l.
      rewrite exist_elim; eauto => e'.
      apply const_elim_l; intros H'; rewrite H'.
      rewrite (forall_elim ((interp k τ' H Δ) ↾ _)).
      rewrite always_elim.
      rewrite -wp_TLam; apply later_mono.
      apply wp_mono=> w.
      eapply entails_proper.
      + apply interp_subst.
      + eauto.
      + eauto.
    - (* Fold *)
      value_case. unfold interp_rec.
      rewrite fixpoint_unfold.
      cbn.
      rewrite -exist_intro.
      apply (always_intro _ _).
      apply and_intro; auto.
      rewrite map_length in IHHtyped.
      specialize (IHHtyped
                    (Vlist_cons (@interp Σ i L k (TRec τ) HC Δ) Δ)
                    (closed_ctx_map
                       _ _ _ _
                       Hctx (λ τ, closed_type_S_ren2 τ 1 0 _))
                    (closed_type_rec HC)
                    (alwyas_stable_Vlist_cons _ _ _ _)
                   _
                    Hlen
                 ).      
      rewrite -wp_impl_l -later_intro. apply and_intro;
        [ apply (always_intro _ _), forall_intro=> v /=; apply impl_intro_l|].
      2: etransitivity; [|apply IHHtyped].
      + rewrite and_elim_l; trivial.
      + rewrite zip_with_closed_ctx_list_subst; trivial.
    - (* Unfold *)
      smart_wp_bind UnfoldCtx _ v; cbn.
      rewrite and_elim_l.
      unfold interp_rec. rewrite fixpoint_unfold /interp_rec_pre; cbn.
      replace (fixpoint
                 (λ rec_apr : leibniz_val -n> iPropG lang Σ,
                              CofeMor
                                (λ w : leibniz_val,
                                       □ (∃ e1 : expr,
                                             w = FoldV e1
                                             ∧ ▷ WP e1 @ ⊤ {{ λ v1 : val,
                                                        ((interp (S k) τ (closed_type_rec ?HC4))
                                                           (Vlist_cons rec_apr Δ)) v1 }}))%I))
      with
      (@interp Σ i L k (TRec τ) (typed_closed_type _ _ _ _ Htyped) Δ) by (cbn; unfold interp_rec; trivial).
      rewrite always_elim.
      rewrite exist_elim; eauto => e'.
      apply const_elim_l; intros H'; rewrite H'.
      rewrite -wp_Fold.
      apply later_mono, wp_mono => w.
      rewrite -interp_subst; eauto.
    - (* Alloc *)
      smart_wp_bind AllocCtx _ v; cbn.
      rewrite -wp_atomic; cbn; eauto using to_of_val.
      rewrite -wp_alloc.
      apply pvs_intro.
      all : eauto 3 using to_of_val with itauto.
      rewrite -later_intro.
      apply forall_intro => l.
      apply wand_intro_l.
      rewrite -exist_intro.
      rewrite -pvs_always_l.
      apply and_intro; auto.
      rewrite -inv_alloc; auto.
      rewrite -later_intro /interp_ref_pred.
      rewrite -exist_intro.
      apply sep_mono; eauto.
      auto with itauto.
    - (* Load *)
      smart_wp_bind LoadCtx _ v; cbn.
      rewrite and_exist_r. apply exist_elim => l.
      rewrite -and_assoc.
      apply const_elim_l; intros Heq; rewrite Heq.
      rewrite -wp_atomic; cbn; eauto using to_of_val.
      rewrite -wp_inv; try match goal with |- _ ⊆ _ => trivial end.
      rewrite -pvs_intro; eauto.
      cbn; eauto using to_of_val.
      apply and_elim_l.
      rewrite and_elim_r and_elim_l.
      apply wand_intro_l.
      unfold interp_ref_pred at 1.
      apply wand_elim_l'.
      etrans; [rewrite later_exist|]; eauto.
      rewrite exist_elim; eauto => w.
      apply wand_intro_r.
      rewrite -(wp_load _ _ _ 1); try match goal with |- _ ⊆ _ => trivial end; eauto.
      rewrite sep_elim_r; auto with itauto.
      specialize (HNLdisj l); set_solver_ndisj.
      rewrite sep_elim_l.
      unfold interp_ref_pred.
      rewrite -later_sep.
      apply later_mono.
      apply sep_mono; eauto.
      apply wand_intro_l.
      rewrite -later_intro.
      rewrite -exist_intro.
      rewrite (always_sep_dup (((interp k τ (closed_type_ref _)) Δ) w)).
      rewrite sep_assoc.
      apply sep_mono; eauto.
      rewrite -pvs_intro.
      rewrite interp_closed_irrel; trivial.
    - (* Store *)
      smart_wp_bind (StoreLCtx _) _ v; cbn.
      smart_wp_bind (StoreRCtx _) _ v'; cbn.
      rewrite and_comm ?and_assoc.
      rewrite !and_exist_r. apply exist_elim => l.
      rewrite -!and_assoc.
      apply const_elim_l; intros Heq; rewrite Heq.
      rewrite -wp_atomic; cbn; eauto using to_of_val.
      rewrite -wp_inv; try match goal with |- _ ⊆ _ => trivial end.
      rewrite -pvs_intro; eauto.
      cbn; eauto using to_of_val.
      apply and_elim_l.
      rewrite and_elim_r and_comm -and_assoc and_elim_r.
      apply wand_intro_l.
      unfold interp_ref_pred at 1.
      apply wand_elim_l'.
      etrans; [rewrite later_exist|]; eauto.
      rewrite exist_elim; eauto => w.
      apply wand_intro_r.
      rewrite -wp_store; try match goal with |- _ ⊆ _ => trivial end; eauto using to_of_val.
      rewrite sep_elim_r; auto with itauto.
      specialize (HNLdisj l); set_solver_ndisj.
      rewrite and_elim_l.
      unfold interp_ref_pred.
      rewrite (later_intro (((interp k τ _) Δ) v')).
      rewrite -!later_sep.
      apply later_mono.
      rewrite -wand_intro_l.
      apply sep_mono. apply sep_elim_l.
      trivial.
      rewrite -later_intro.
      rewrite -exist_intro.
      rewrite (always_sep_dup (((interp k τ _) Δ) _)).
      rewrite sep_assoc.
      apply sep_mono; eauto.
      rewrite interp_closed_irrel; trivial.
      rewrite -pvs_intro; auto.
      (* unshelving *)
      Unshelve.
      all: solve [eauto 2 using typed_closed_type | try typeclasses eauto].
  Qed.
  
End typed_interp.