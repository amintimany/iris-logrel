Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import F_mu.lang F_mu.typing F_mu.rules F_mu.logrel.
Require Import prelude.Vlist.
Import uPred.

Section typed_interp.
  Context {Σ : iFunctor}.
  Implicit Types P Q R : iProp lang Σ.
  Notation "# v" := (of_val v) (at level 20).

  Canonical Structure leibniz_val := leibnizC val.

  Canonical Structure leibniz_le n m := leibnizC (n ≤ m).
(*
  Ltac ipropsimpl :=
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
 *)

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

  Lemma typed_interp k Δ Γ vs e τ
        (Htyped : typed k Γ e τ)
        (Hctx : closed_ctx k Γ)
        (HC : closed_type k τ)
        (HΔ : VlistAlwaysStable Δ)
    : List.length Γ = List.length vs →
      Π∧ zip_with (λ τ v, interp k (` τ) (proj2_sig τ) Δ v) (closed_ctx_list _ Γ Hctx) vs ⊢
                  WP (e.[env_subst vs]) @ ⊤ {{ λ v, (@interp Σ) k τ HC Δ v }}.
  Proof.
    revert Hctx HC HΔ vs.
    induction Htyped; intros Hctx HC HΔ vs Hlen; iIntros "#HΓ"; cbn.
    - (* var *)
      destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
      { by rewrite -Hlen; apply lookup_lt_Some with τ. }
      rewrite /env_subst Hv; value_case.
      edestruct (zipwith_Forall_lookup _ Hctx) as [Hτ' Hτ'eq]; eauto.
      iApply interp_closed_irrel_turnstile.
      iApply big_and_elem_of "HΓ"; eauto.
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
      intros w w'; cbn; iIntros "#[% [H2 H3]]"; rewrite H; cbn.
      iApply wp_fst; eauto using to_of_val; cbn.
      iNext; iApply interp_closed_irrel_turnstile; trivial.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" IHHtyped; cbn.
      iApply double_exists; [|trivial].
      intros w w'; cbn; iIntros "#[% [H2 H3]]"; rewrite H.
      iApply wp_snd; eauto using to_of_val.
      iNext; iApply interp_closed_irrel_turnstile; trivial.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHHtyped; cbn.
      value_case; iLeft; auto with itauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHHtyped; cbn.
      value_case; iRight; auto with itauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v "#Hv" IHHtyped1; cbn.
      iDestruct "Hv" as "[Hv|Hv]"; eauto; iRevert "HΓ";
        iApply exist_elim; eauto; cbn;
          iIntros {w} "#[% Hw2] #HΓ"; rewrite H; cbn;
            [iApply wp_case_inl|iApply wp_case_inr];
            auto 1 using to_of_val;
            asimpl;
            [specialize (IHHtyped2 Δ (typed_closed_ctx _ _ _ _ Htyped2) HC HΔ (w::vs)) |
             specialize (IHHtyped3 Δ (typed_closed_ctx _ _ _ _ Htyped3) HC HΔ (w::vs))];
              erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto); iNext;
                [iApply IHHtyped2 | iApply IHHtyped3]; cbn; auto;
                  (iSplit; [iApply interp_closed_irrel_turnstile|
                            iApply type_context_closed_irrel_turnstile]; trivial).
    - (* lam *)
      value_case; apply (always_intro _ _); iIntros {w} "#Hw".
      iApply wp_lam; auto 1 using to_of_val.
      asimpl; erewrite typed_subst_head_simpl; [|eauto|cbn]; eauto.
      iNext; iApply (IHHtyped Δ (typed_closed_ctx _ _ _ _ Htyped) (closed_type_arrow_2 HC)
                              HΔ (w :: vs)); cbn; auto.
      (iSplit; [iApply interp_closed_irrel_turnstile|
                iApply type_context_closed_irrel_turnstile]; trivial).
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHHtyped2.
      iApply wp_mono; [|iApply "Hv"; auto with itauto].
      intros; apply interp_closed_irrel_turnstile.
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
      rewrite interp_subst; trivial.
    - (* Fold *)
      value_case. unfold interp_rec.
      rewrite fixpoint_unfold.
      cbn.
      rewrite -exist_intro.
      apply (always_intro _ _).
      apply and_intro; auto.
      rewrite map_length in IHHtyped.
      specialize (IHHtyped
                    (Vlist_cons (interp k (TRec τ) HC Δ) Δ)
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
                 (λ rec_apr : leibniz_val -n> iProp lang Σ,
                              CofeMor
                                (λ w : leibniz_val,
                                       □ (∃ e1 : expr,
                                             w = FoldV e1
                                             ∧ ▷ WP e1 @ ⊤ {{ λ v1 : val,
                                                        ((interp (S k) τ (closed_type_rec ?HC4))
                                                           (Vlist_cons rec_apr Δ)) v1 }}))%I))
      with
      (interp k (TRec τ) (typed_closed_type _ _ _ _ Htyped) Δ) by (cbn; unfold interp_rec; trivial).
      rewrite always_elim.
      rewrite exist_elim; eauto => e'.
      apply const_elim_l; intros H'; rewrite H'.
      rewrite -wp_Fold.
      apply later_mono, wp_mono => w.
      rewrite -interp_subst; eauto.
      (* unshelving *)
      Unshelve.
      all: solve [eauto 2 using typed_closed_type | try typeclasses eauto].
  Qed.
  
End typed_interp.
