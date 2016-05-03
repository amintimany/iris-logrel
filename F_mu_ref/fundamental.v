Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import F_mu_ref.lang F_mu_ref.typing F_mu_ref.rules F_mu_ref.logrel.
From iris.program_logic Require Export lifting.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
Require Import prelude.Vlist.
Import uPred.

Section typed_interp.
  Context
    {Σ : gFunctors}
    `{i : heapG Σ}
    `{L : namespace}.
  
  Implicit Types P Q R : iPropG lang Σ.
  Notation "# v" := (of_val v) (at level 20).

  (*
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
  
  
  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (@wp_bind _ _ _ [ctx]);
    iApply wp_impl_l;
    iSplit; [| iApply Hp; trivial];
    [apply (always_intro _ _); iIntros {v} Hv|iSplit; trivial]; cbn.
              
  Local Ltac value_case := iApply wp_value; cbn; rewrite ?to_of_val; trivial.

  Lemma later_exist_turnstile (M : cmraT) (A : Type) :
    Inhabited A → ∀ Φ : A → uPred M, (▷ (∃ a : A, Φ a))%I ⊢ (∃ a : A, ▷ Φ a)%I.
  Proof. intros H Φ. rewrite later_exist; trivial. Qed.

  Lemma typed_interp N k Δ Γ vs e τ
        (HNLdisj : ∀ l : loc, N ⊥ L .@ l)
        (Htyped : typed k Γ e τ)
        (Hctx : closed_ctx k Γ)
        (HC : closed_type k τ)
        (HΔ : VlistAlwaysStable Δ)
    : List.length Γ = List.length vs →
      (heap_ctx N ∧ Π∧ zip_with (λ τ v, (@interp Σ i L) k (` τ) (proj2_sig τ) Δ v) (closed_ctx_list _ Γ Hctx) vs)%I ⊢
                  WP (e.[env_subst vs]) @ ⊤ {{ λ v, (@interp Σ i L) k τ HC Δ v }}.
  Proof.
    revert Hctx HC HΔ vs.
    induction Htyped; intros Hctx HC HΔ vs Hlen; iIntros "#[Hheap HΓ]"; cbn.
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
      smart_wp_bind (PairLCtx e2.[env_subst vs]) v "#Hv" IHHtyped1.
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
      intros w w'; cbn; iIntros "#[% [H2 H3]]"; rewrite H; cbn.
      iApply wp_snd; eauto using to_of_val; cbn.
      iNext; iApply interp_closed_irrel_turnstile; trivial.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHHtyped; cbn.
      value_case; iLeft; auto with itauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHHtyped; cbn.
      value_case; iRight; auto with itauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v "#Hv" IHHtyped1; cbn.
      iDestruct "Hv" as "[Hv|Hv]"; eauto; iRevert "HΓ"; iRevert "Hheap";
        iApply exist_elim; eauto; cbn;
          iIntros {w} "#[% Hw2] #HΓ #Hheap"; rewrite H; cbn;
            [iApply wp_case_inl|iApply wp_case_inr];
            auto 1 using to_of_val;
            asimpl;
            [specialize (IHHtyped2 Δ (typed_closed_ctx _ _ _ _ Htyped2) HC HΔ (w::vs)) |
             specialize (IHHtyped3 Δ (typed_closed_ctx _ _ _ _ Htyped3) HC HΔ (w::vs))];
              erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto); iNext;
                [iApply IHHtyped2 | iApply IHHtyped3]; cbn; auto;
                  (iSplit; [trivial|iSplit]; [iApply interp_closed_irrel_turnstile|
                            iApply type_context_closed_irrel_turnstile]; trivial).
    - (* lam *)
      value_case; apply (always_intro _ _); iIntros {w} "#Hw".
      iApply wp_lam; auto 1 using to_of_val.
      asimpl; erewrite typed_subst_head_simpl; [|eauto|cbn]; eauto.
      iNext; iApply (IHHtyped Δ (typed_closed_ctx _ _ _ _ Htyped) (closed_type_arrow_2 HC)
                              HΔ (w :: vs)); cbn; auto.
      (iSplit; [trivial|iSplit]; [iApply interp_closed_irrel_turnstile|
                iApply type_context_closed_irrel_turnstile]; trivial).
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHHtyped2.
      iApply wp_mono; [|iApply "Hv"; auto with itauto].
      intros; apply interp_closed_irrel_turnstile.
    - (* TLam *)
      value_case; iApply exist_intro; iSplit; trivial.
      iIntros {τi}; destruct τi as [τi τiPr].
      iRevert "Hheap".
      iPoseProof always_intro "HΓ" as "HP"; try typeclasses eauto;
        try (iApply always_impl; iExact "HP").
      iIntros "#HΓ #Hheap"; iNext.
      iApply IHHtyped; [rewrite map_length|]; trivial.
      iSplit; trivial.
      iRevert "HΓ". rewrite zip_with_closed_ctx_list_subst. iIntros "#HΓ"; trivial.
    - (* TApp *)
      smart_wp_bind TAppCtx v "#Hv" IHHtyped; cbn.
      iApply exist_elim; [|iExact "Hv"]; cbn.
      iIntros {e'} "[% #He']"; rewrite H0.
      iApply wp_TLam.
      iSpecialize "He'" {((interp k τ' H Δ) ↾ _)}; cbn.
      iApply always_elim. iApply always_mono; [|trivial].
      iIntros "He'"; iNext.
      iApply wp_mono; [|trivial].
      intros w; cbn; rewrite -interp_subst; trivial.
    - (* Fold *)
      rewrite map_length in IHHtyped.
      iApply (@wp_bind _ _ _ [FoldCtx]);
        iApply wp_impl_l;
        iSplit; [eapply (@always_intro _ _ _ _)|
                 iApply (IHHtyped _ _ (closed_type_rec HC)); trivial]; cbn.
      + iIntros {v} "#Hv".
        value_case. rewrite /interp_rec fixpoint_unfold. unfold interp_rec_pre at 1; cbn.
        eapply (@always_intro _ _ _ _).
        iApply exist_intro; iSplit; trivial.
        iNext.
        change (fixpoint (interp_rec_pre
                            (Vlist_cons_apply Δ (interp (S k) τ (closed_type_rec HC)))))
        with ((@interp _ _ L k (TRec τ) HC) Δ); trivial.
      + iRevert "HΓ"; rewrite zip_with_closed_ctx_list_subst; iIntros "#HΓ";
          iSplit; trivial.
    - (* Unfold *)
      iApply (@wp_bind _ _ _ [UnfoldCtx]);
        iApply wp_impl_l;
        iSplit; [eapply (@always_intro _ _ _ _)|
                 iApply (IHHtyped _ _ (typed_closed_type _ _ _ _ Htyped)); trivial];
        [|iSplit; trivial]; cbn.
      iIntros {v}.
      rewrite /interp_rec fixpoint_unfold. unfold interp_rec_pre at 1; cbn.
      iIntros "#Hv".
      iApply exist_elim; [|iAssumption].
      iIntros {w}; cbn.
      change (fixpoint (interp_rec_pre
                          (Vlist_cons_apply
                             Δ
                             (interp
                                (S k) τ
                                (closed_type_rec
                                   (typed_closed_type k Γ e (TRec τ) Htyped))))))
      with ((@interp _ _ L k (TRec τ) (typed_closed_type k Γ e (TRec τ) Htyped)) Δ);
        trivial.
      iIntros "[% #Hw]"; rewrite H.
      iApply wp_Fold; cbn; auto using to_of_val.
      iRevert "Hw". rewrite -interp_subst. iIntros "#Hw". trivial.
    - (* Alloc *)
      smart_wp_bind AllocCtx v "#Hv" IHHtyped; cbn. iClear "HΓ".
      iApply wp_atomic; cbn; trivial; [rewrite to_of_val; auto|].
      iApply pvs_intro.
      iApply wp_alloc; [| | | |iSplit;[iExact "Hheap"|iExact "Hv"]];
        [|iIntros "#[Hheap Hv]"| |]; auto using to_of_val.
      iIntros "#[Hheap Hv]". iNext.
      iIntros {l} "Hl".
      iApply exist_intro.
      iApply and_intro; [| trivial |]; auto.
      iApply inv_alloc; trivial. iNext.
      iApply exist_intro.
      iSplit; trivial.
    - (* Load *)
      smart_wp_bind LoadCtx v "#Hv" IHHtyped; cbn. iClear "HΓ".
      iRevert "Hheap". iApply exist_elim; [|iExact "Hv"].
      iIntros {l} "[% #Hv] #Hheap"; rewrite H.
      iApply wp_atomic; cbn; eauto using to_of_val.
      iApply wp_inv; [auto using to_of_val| trivial
                      | apply and_elim_r | apply and_elim_l | ].
      iApply pvs_intro. iSplit; trivial.
      iIntros "Hl".
      iPoseProof later_exist_turnstile "Hl" as "Hl'"; [typeclasses eauto|].
      iRevert "Hheap".
      iApply exist_elim; [|iExact "Hl'"].
      iIntros {w} "[Hl1 #Hl2] #Hheap".
      iApply (wp_load _ _ _ 1);
        [apply and_elim_r| trivial | apply and_elim_l | iSplit; trivial].
      specialize (HNLdisj l); set_solver_ndisj.
      iNext.
      iSplitL; trivial.
      iIntros "Hl".
      iSplitL.
      + iNext. iApply exist_intro; iSplitL; trivial.
      + iApply pvs_intro; iApply interp_closed_irrel_turnstile; trivial.
    - (* Store *)
      smart_wp_bind (StoreLCtx _) v "#Hv" IHHtyped1; cbn.
      smart_wp_bind (StoreRCtx _) w "#Hw" IHHtyped2; cbn. iClear "HΓ".
      iRevert "Hheap Hw". iApply exist_elim; [|iExact "Hv"].
      iIntros {l} "#[% Hl] #Hheap #Hw"; rewrite H.
      iApply wp_atomic; cbn; [trivial| rewrite ?to_of_val; auto |].
      iApply wp_inv; [cbn; rewrite ?to_of_val; auto| trivial
                      | apply and_elim_r | apply and_elim_l | ].
      iApply pvs_intro. iSplit; trivial.
      iClear "Hl". iIntros "Hl".
      iPoseProof later_exist_turnstile "Hl" as "Hl'"; [typeclasses eauto|].
      iRevert "Hheap Hw".
      iApply exist_elim; [|iExact "Hl'"].
      iIntros {u} "[Hl1 #Hl2] #Hheap #Hw".
      iApply wp_store;
        [rewrite to_of_val; trivial | apply and_elim_r
         | | apply and_elim_l | iSplit; trivial]. 
      specialize (HNLdisj l); set_solver_ndisj.
      iSplitL; trivial.
      iNext. iIntros "Hl".
      iSplitL; [|iApply pvs_intro; trivial].
      iNext. iApply exist_intro; iSplitL; trivial.
      iApply interp_closed_irrel_turnstile; trivial.
      (* unshelving *)
      Unshelve.
      all: cbn; solve [eauto 2 using closed_ctx_map_S_back,
                       typed_closed_type | try typeclasses eauto].
  Qed.
  
End typed_interp.