Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import F_mu_ref_par.lang F_mu_ref_par.typing F_mu_ref_par.rules
        F_mu_ref_par.rules_binary F_mu_ref_par.logrel_binary.
From iris.program_logic Require Export lifting.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
Require Import iris.proofmode.tactics iris.proofmode.invariants.
Import uPred.

Section typed_interp.
  Context {Σ : gFunctors} {i : heapIG Σ} {iS : cfgSG Σ}
          {L : namespace} {S : namespace}.

  Implicit Types P Q R : iPropG lang Σ.
  Notation "# v" := (of_val v) (at level 20).

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
       □ _) => eapply (@always_intro _ _ _ _)
  end : itauto.

  Local Hint Extern 1 =>
  match goal with
    |-
    (_
       --------------------------------------□
       (_ ∧ _)) => iSplit
  end : itauto.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) ident(w)
        constr(Hv) uconstr(Hp) :=
    iApply (@wp_bind _ _ _ [ctx]);
    iApply wp_wand_l; iSplitR;
    [|iApply Hp; rewrite fill_app; simpl; repeat iSplitR; trivial];
    iIntros {v} "Htemporary";
    iDestruct "Htemporary" as {w} Hv;
    rewrite fill_app; simpl.
  (*
    iApply (@wp_bind _ _ _ [ctx]);
    iApply wp_impl_l;
    iSplit; [| iApply Hp; trivial];
    [apply (always_intro _ _); iIntros {v} Hv|iSplit; trivial]; cbn.
*)
  Local Ltac value_case := iApply wp_value; [cbn; rewrite ?to_of_val; trivial|].

  Lemma map_lookup {A B} (l : list A) (f : A → B) k :
    (map f l) !! k = option_map f (l !! k).
  Proof.
    revert k; induction l => k; simpl; trivial.
    destruct k; simpl; trivial.
  Qed.

  Lemma typed_binary_interp N Δ Γ vs e τ
        (HNLdisj : ∀ l : loc * loc, N ⊥ L .@ l)
        (HSLdisj : ∀ l : loc * loc, S ⊥ L .@ l)
        (Htyped : typed Γ e τ)
        (HΔ : context_interp_Persistent Δ)
    : List.length Γ = List.length vs →
      ∀ ρ j K,
        ((heapI_ctx N ★ Spec_ctx S ρ ★
          Π∧ zip_with (λ τ v, (@interp Σ iS i L) τ Δ v) Γ vs
          ★ j ⤇ (fill K (e.[env_subst (map snd vs)])))%I)
          ⊢ WP (e.[env_subst (map fst vs)]) @ ⊤
          {{ λ v, ∃ v', j ⤇ (fill K (# v')) ★ (@interp Σ iS i L) τ Δ (v, v') }}.
  Proof.
    revert Δ HΔ vs.
    induction Htyped; intros Δ HΔ vs Hlen ρ j K;
      iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    - (* var *)
      destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
      { by rewrite -Hlen; apply lookup_lt_Some with τ. }
      rewrite /env_subst. repeat rewrite map_lookup. rewrite Hv; simpl.
      value_case.
      iExists _; iFrame "Htr".
      iApply (big_and_elem_of with "HΓ").
      apply elem_of_list_lookup_2 with x.
      rewrite lookup_zip_with; simplify_option_eq; destruct v; trivial.
    - (* unit *) value_case. iExists UnitV; iFrame "Htr"; iSplit; trivial.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst (map fst vs)]) v v' "[Hv #Hiv]"
                    (IHHtyped1 _ _ _ _ _ j
                               (K ++ [PairLCtx e2.[env_subst (map snd vs)] ])).
      smart_wp_bind (PairRCtx v) w w' "[Hw #Hiw]"
                    (IHHtyped2 _ _ _ _ _ j
                               (K ++ [(PairRCtx v')])).
      value_case. iExists (PairV v' w'); iFrame "Hw".
      iExists (v, w), (v', w'); simpl; eauto 10 with itauto.
    - (* fst *)
      smart_wp_bind (FstCtx) v v' "[Hv #Hiv]"
                    (IHHtyped _ _ _ _ _ j (K ++ [FstCtx])); cbn.
      iDestruct "Hiv" as {w1 w2} "#[% [Hiv2 Hiv3]]".
      inversion H; subst.
      iPvs (step_fst _ _ _ j K (# (w2.1)) (w2.1) (# (w2.2)) (w2.2)
                     _ _ _ with "* -") as "Hw".
      iFrame "Hspec Hv"; trivial.
      iApply wp_fst; eauto using to_of_val; cbn.
      iNext. iExists _; iSplitL; trivial.
    - (* snd *)
      smart_wp_bind (SndCtx) v v' "[Hv #Hiv]"
                    (IHHtyped _ _ _ _ _ j (K ++ [SndCtx])); cbn.
      iDestruct "Hiv" as {w1 w2} "#[% [Hiv2 Hiv3]]".
      inversion H; subst.
      iPvs (step_snd _ _ _ j K (# (w2.1)) (w2.1) (# (w2.2)) (w2.2)
                     _ _ _ with "* -") as "Hw".
      iFrame "Hspec Hv"; trivial.
      iApply wp_snd; eauto using to_of_val; cbn.
      iNext. iExists _; iSplitL; trivial.
    - (* injl *)
      smart_wp_bind (InjLCtx) v v' "[Hv #Hiv]"
                    (IHHtyped _ _ _ _ _ j (K ++ [InjLCtx])); cbn.
      value_case. iExists (InjLV v'); iFrame "Hv".
      iLeft; iExists _; iSplit; [|eauto]; simpl; trivial.
    - (* injr *)
      smart_wp_bind (InjRCtx) v v' "[Hv #Hiv]"
                    (IHHtyped _ _ _ _ _ j (K ++ [InjRCtx])); cbn.
      value_case. iExists (InjRV v'); iFrame "Hv".
      iRight; iExists _; iSplit; [|eauto]; simpl; trivial.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v v' "[Hv #Hiv]"
                    (IHHtyped1 _ _ _ _ _ j (K ++ [CaseCtx _ _])); cbn.
      iDestruct "Hiv" as "[Hiv|Hiv]".
      + iDestruct "Hiv" as {w} "[% Hw]".
        inversion H; subst.
        iPvs (step_case_inl _ _ _ j K (# (w.2)) (w.2) _ _
                     _ _ with "* -") as "Hz".
        iFrame "Hspec Hv"; trivial.
        iApply wp_case_inl; auto 1 using to_of_val.
        asimpl.
        specialize (IHHtyped2 Δ HΔ (w::vs)); simpl in IHHtyped2.
        erewrite <- ?typed_subst_head_simpl in IHHtyped2; eauto;
          simpl; try rewrite map_length; eauto with f_equal. iNext.
        iApply IHHtyped2; auto 2.
        iFrame "Hheap Hspec Hw HΓ"; trivial.
      + iDestruct "Hiv" as {w} "[% Hw]".
        inversion H; subst.
        iPvs (step_case_inr _ _ _ j K (# (w.2)) (w.2) _ _
                     _ _ with "* -") as "Hz".
        iFrame "Hspec Hv"; trivial.
        iApply wp_case_inr; auto 1 using to_of_val.
        asimpl.
        specialize (IHHtyped3 Δ HΔ (w::vs)); simpl in IHHtyped3.
        erewrite <- ?typed_subst_head_simpl in IHHtyped3; eauto;
          simpl; try rewrite map_length; eauto with f_equal. iNext.
        iApply IHHtyped3; auto 2.
        iFrame "Hheap Hspec Hw HΓ"; trivial.
    - (* lam *)
      value_case. iExists (LamV _). iFrame "Htr".
      iAlways. iIntros {j' K' v} "[#Hiv Hv]".
      iApply wp_lam; auto 1 using to_of_val. iNext.
      iPvs (step_lam _ _ _ j' K' _ (# (v.2)) (v.2) _ _ with "* -") as "Hz".
      iFrame "Hspec Hv"; trivial.
      asimpl. erewrite ?typed_subst_head_simpl; eauto;
          simpl; try rewrite map_length; eauto with f_equal.
      specialize (IHHtyped Δ HΔ (v::vs)); simpl in IHHtyped.
      iApply IHHtyped; auto.
      iFrame "Hheap Hspec Hiv HΓ"; trivial.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst (map fst vs)])) v v' "[Hv #Hiv]"
                    (IHHtyped1
                       _ _ _ _ _ j
                       (K ++ [(AppLCtx (e2.[env_subst (map snd vs)]))])); cbn.
      smart_wp_bind (AppRCtx v) w w' "[Hw #Hiw]"
                    (IHHtyped2
                       _ _ _ _ _ j
                       (K ++ [AppRCtx v'])); cbn.
      iApply ("Hiv" $! j K (w, w')); simpl.
      iNext; iFrame "Hw"; trivial.
    - (* TLam *)
      value_case. iExists (TLamV _). iFrame "Htr"; simpl.
      iExists (e.[env_subst (map fst vs)], e.[env_subst (map snd vs)]).
      iSplit; trivial.
      iIntros {τi}; destruct τi as [τi τiPr].
      iAlways. iNext. iIntros {j' K'} "Hv". simpl.
      iApply IHHtyped; [rewrite map_length; trivial|].
      iFrame "Hheap Hspec Hv".
      rewrite zip_with_context_interp_subst; trivial.
    - (* TApp *)
      smart_wp_bind (TAppCtx) v v' "[Hv #Hiv]"
                    (IHHtyped _ _ _ _ _ j (K ++ [TAppCtx])); cbn.
      iDestruct "Hiv" as {e'} "[% He']".
      inversion H; subst.
      iSpecialize ("He'" $! ((interp τ' Δ) ↾ _)); cbn.
      iPvs (step_Tlam _ _ _ j K (e'.2) _ with "* -") as "Hz".
      iFrame "Hspec Hv"; trivial.
      iApply wp_TLam.
      iRevert "He'"; iIntros "#He'". (*To get rid of □. Is this the best way?!*)
      iNext.
      iApply wp_wand_l; iSplitR; [|iApply "He'"; auto].
      iIntros {w} "Hw". iDestruct "Hw" as {w'} "[Hw #Hiw]".
      iExists _; iFrame "Hw".
      rewrite -interp_subst; trivial.
    - (* Fold *)
      rewrite map_length in IHHtyped.
      iApply (@wp_bind _ _ _ [FoldCtx]);
        iApply wp_wand_l; iSplitR;
          [|iApply (IHHtyped (extend_context_interp ((interp (TRec τ)) Δ) Δ)
                             _ _ _ _ j (K ++ [FoldCtx]));
            rewrite fill_app; simpl; repeat iSplitR; trivial].
      + iIntros {v} "Hv"; iDestruct "Hv" as {w} "[Hv #Hiv]";
          rewrite fill_app.
        value_case. iExists (FoldV w); iFrame "Hv".
        rewrite fixpoint_unfold; cbn.
        iAlways. iExists (_, _); iSplit; auto with itauto.
      + rewrite zip_with_context_interp_subst; trivial.
    - (* Unfold *)
      iApply (@wp_bind _ _ _ [UnfoldCtx]);
        iApply wp_wand_l; iSplitR;
          [|iApply (IHHtyped _ _ _ _ _ j (K ++ [UnfoldCtx]));
            rewrite fill_app; simpl; repeat iSplitR; trivial].
      iIntros {v} "Hv". iDestruct "Hv" as {w} "[Hw #Hiw]"; rewrite fill_app.
      simpl. rewrite fixpoint_unfold; simpl.
      iRevert "Hiw"; iIntros "#Hiw". (*To get rid of □. Is this the best way?!*)
      change (fixpoint _) with (@interp _ _ _ L (TRec τ) Δ).
      iDestruct "Hiw" as {z} "[% #Hiz]"; inversion H; subst.
      iPvs (step_Fold _ _ _ j K (# (z.2)) (z.2) _ _ with "* -") as "Hz".
      iFrame "Hspec Hw"; trivial.
      iApply wp_Fold; cbn; auto using to_of_val.
      iNext. iExists _; iFrame "Hz".
      rewrite -interp_subst; destruct z; trivial.
    - (* Fork *)
      iPvs (step_fork _ _ _ j K _ _ with "* -") as "Hz".
      iFrame "Hspec Htr"; trivial.
      iDestruct "Hz" as {j'} "[Hz1 Hz2]".
      iApply wp_fork.
      iSplitL "Hz1".
      + iNext. iExists UnitV; iFrame "Hz1"; iSplit; trivial.
      + iNext. iApply wp_wand_l; iSplitR;
                 [|iApply (IHHtyped _ _ _ _ _ _ [])]; trivial.
        * iIntros {w} "Hw"; trivial.
        * iFrame "Hheap Hspec HΓ"; trivial.
    - (* Alloc *)
      smart_wp_bind (AllocCtx) v v' "[Hv #Hiv]"
                    (IHHtyped
                       _ _ _ _ _ j (K ++ [AllocCtx])).
      iApply wp_atomic; cbn; trivial; [rewrite to_of_val; auto|].
      iPvsIntro.
      iPvs (step_alloc _ _ _ j K (# v') v' _ _ with "* -") as "Hz".
      iFrame "Hspec Hv"; trivial.
      iDestruct "Hz" as {l'} "[Hj Hl']".
      iApply wp_alloc; auto 1 using to_of_val.
      iFrame "Hheap". iNext.
      iIntros {l} "Hl".
      iAssert ((∃ w : val * val, l ↦ᵢ w.1 ★ l' ↦ₛ w.2 ★
                                   ((@interp _ _ _ L τ) Δ) w)%I)
        as "Hinv" with "[Hl Hl']".
      { iExists (v, v'); iFrame "Hl Hl' Hiv"; trivial. }
      iPvs (inv_alloc _ with "[Hinv]") as "HN"; eauto 1.
      { iNext; iExact "Hinv". }
      iPvsIntro; iExists (LocV l'); iSplit; [iExact "Hj"|].
      iExists (l, l'); iSplit; trivial.
    - (* Load *)
      smart_wp_bind (LoadCtx) v v' "[Hv #Hiv]"
                    (IHHtyped
                       _ _ _ _ _ j (K ++ [LoadCtx])).
      iDestruct "Hiv" as {l} "[% Hinv]".
      inversion H; subst.
      iApply wp_atomic; cbn; trivial.
      iPvsIntro.
      iInv (L .@ l) as {w} "[Hw1 [Hw2 #Hw3]]".
      iTimeless "Hw2".
      iPvs (step_load _ _ _ j K (l.2) 1 (w.2) _ with "[Hv Hw2]") as "[Hv Hw2]".
      iFrame "Hspec Hv"; trivial.
      iApply (wp_load _ _ _ 1); [|iFrame "Hheap"]; trivial.
      specialize (HNLdisj l); set_solver_ndisj.
      iNext. iFrame "Hw1". iIntros "Hw1".
      iSplitL "Hw1 Hw2".
      + iNext; iExists w; iFrame "Hw1 Hw2 Hw3"; trivial.
      + iPvsIntro.
        destruct w as [w1 w2]; iExists (w2); iFrame "Hv Hw3"; trivial.
    - (* Store *)
      smart_wp_bind (StoreLCtx _) v v' "[Hv #Hiv]"
                    (IHHtyped1
                       _ _ _ _ _ j (K ++ [StoreLCtx _])).
      smart_wp_bind (StoreRCtx _) w w' "[Hw #Hiw]"
                    (IHHtyped2
                       _ _ _ _ _ j (K ++ [StoreRCtx _])).
      iDestruct "Hiv" as {l} "[% Hinv]".
      inversion H; subst.
      iApply wp_atomic; trivial;
        [eapply bool_decide_spec; eauto using to_of_val|].
      iPvsIntro.
      iInv (L .@ l) as {z} "[Hw1 [Hw2 #Hw3]]".
      eapply bool_decide_spec; eauto using to_of_val.
      iTimeless "Hw2".
      iPvs (step_store _ _ _ j K (l.2) (z.2) (# w') w' _ _ with "[Hw Hw2]")
        as "[Hw Hw2]".
      iFrame "Hspec Hw Hw2"; trivial.
      iApply (wp_store N); auto using to_of_val.
      specialize (HNLdisj l); set_solver_ndisj.
      iFrame "Hheap Hw1". iNext. iIntros "Hw1".
      iSplitL "Hw1 Hw2".
      + iNext; iExists (w, w'); iFrame "Hw1 Hw2 Hiw"; trivial.
      + iPvsIntro. iExists UnitV; iFrame "Hw" ; iSplit; trivial.
    - (* CAS *)
      smart_wp_bind (CasLCtx _ _) v v' "[Hv #Hiv]"
                    (IHHtyped1
                       _ _ _ _ _ j (K ++ [CasLCtx _ _])).
      smart_wp_bind (CasMCtx _ _) w w' "[Hw #Hiw]"
                    (IHHtyped2
                       _ _ _ _ _ j (K ++ [CasMCtx _ _])).
      smart_wp_bind (CasRCtx _ _) u u' "[Hu #Hiu]"
                    (IHHtyped3
                       _ _ _ _ _ j (K ++ [CasRCtx _ _])).
      iDestruct "Hiv" as {l} "[% Hinv]".
      inversion H0; subst.
      iApply wp_atomic; trivial;
        [cbn; eauto 10 using to_of_val|].
      iPvsIntro.
      iInv (L .@ l) as {z} "[Hw1 [Hw2 #Hw3]]".
      eapply bool_decide_spec; eauto 10 using to_of_val.
      iTimeless "Hw2".
      destruct z as [z1 z2]; simpl.
      destruct (val_dec_eq z1 w) as [|Hneq]; subst.
      + iPvs (step_cas_suc _ _ _ j K (l.2) (# w') w' z2 (# u') u' _ _ _
              with "[Hu Hw2]") as "[Hw Hw2]"; simpl.
        { iFrame "Hspec Hu Hw2". iNext.
          rewrite ?EqType_related_eq; trivial.
          iDestruct "Hiw" as "%". iDestruct "Hw3" as "%".
          repeat subst; trivial. }
        iApply (wp_cas_suc N); eauto using to_of_val.
        specialize (HNLdisj l); set_solver_ndisj.
        iFrame "Hheap Hw1".
        iNext. iIntros "Hw1".
        iSplitL "Hw1 Hw2".
        * iNext; iExists (_, _); iFrame "Hw1 Hw2"; trivial.
        * iPvsIntro. iExists TRUEV; iFrame "Hw".
          iLeft; iExists (UnitV, UnitV); auto with itauto.
      + iPvs (step_cas_fail _ _ _ j K (l.2) 1 (z2) (# w') w' (# u') u' _ _ _
              with "[Hu Hw2]") as "[Hw Hw2]"; simpl.
        { iFrame "Hspec Hu Hw2". iNext.
          rewrite ?EqType_related_eq; trivial.
          iDestruct "Hiw" as "%". iDestruct "Hw3" as "%".
          repeat subst; trivial. }
        iApply (wp_cas_fail N); eauto using to_of_val.
        clear Hneq. specialize (HNLdisj l); set_solver_ndisj.
        (* Weird that Hneq above makes set_solver_ndisj diverge or
           take exceptionally long!?!? *)
        iFrame "Hheap Hw1".
        iNext. iIntros "Hw1".
        iSplitL "Hw1 Hw2".
        * iNext; iExists (_, _); iFrame "Hw1 Hw2"; trivial.
        * iPvsIntro. iExists FALSEV; iFrame "Hw".
          iRight; iExists (UnitV, UnitV); auto with itauto.
          (* unshelving... *)
          Unshelve.
          all: auto using to_of_val.
          simpl; typeclasses eauto.
          all: clear - HSLdisj; specialize (HSLdisj l); set_solver_ndisj.
  Qed.

End typed_interp.