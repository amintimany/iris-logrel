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
  Context {Σ : gFunctors} {iI : heapIG Σ} {iS : cfgSG Σ}
          {N : namespace}.

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

  Local Ltac value_case := iApply wp_value; [cbn; rewrite ?to_of_val; trivial|].

  Lemma map_lookup {A B} (l : list A) (f : A → B) k :
    (map f l) !! k = option_map f (l !! k).
  Proof.
    revert k; induction l => k; simpl; trivial.
    destruct k; simpl; trivial.
  Qed.

  Definition bin_log_related Δ Γ e e' τ
             {HΔ : context_interp_Persistent Δ}
    :=
      ∀ vs,
        List.length Γ = List.length vs →
        ∀ ρ j K,
          ((heapI_ctx (N .@ 2) ★ Spec_ctx (N .@ 3) ρ ★
                      Π∧ zip_with (λ τ v, @interp Σ iS iI (N .@ 1) τ Δ v) Γ vs
                                  ★ j ⤇ (fill K (e'.[env_subst (map snd vs)]))
           )%I)
            ⊢ WP (e.[env_subst (map fst vs)]) @ ⊤
            {{ λ v, ∃ v', j ⤇ (fill K (# v')) ★
                            (@interp Σ iS iI (N .@ 1)
                                     τ Δ (v, v')) }}.

  Notation "Δ ∥ Γ ⊩ e '≤log≤' e' ∷ τ" := (bin_log_related Δ Γ e e' τ)
                                       (at level 20) : bin_logrel_scope.

  Delimit Scope bin_logrel_scope with bin_logrel.

  Local Open Scope bin_logrel_scope.

  Notation "✓✓" := context_interp_Persistent.

  Lemma typed_binary_interp_Pair Δ Γ e1 e2 e1' e2' τ1 τ2 {HΔ : ✓✓ Δ}
        (IHHtyped1 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e1 ≤log≤ e1' ∷ τ1)
        (IHHtyped2 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e2 ≤log≤ e2' ∷ τ2)
    :
      Δ ∥ Γ ⊩ Pair e1 e2 ≤log≤ Pair e1' e2' ∷ TProd τ1 τ2.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (PairLCtx e2.[env_subst (map fst vs)]) v v' "[Hv #Hiv]"
                  (IHHtyped1 _ _ _ _ _ j
                             (K ++ [PairLCtx e2'.[env_subst (map snd vs)] ])).
    smart_wp_bind (PairRCtx v) w w' "[Hw #Hiw]"
                  (IHHtyped2 _ _ _ _ _ j
                             (K ++ [(PairRCtx v')])).
    value_case. iExists (PairV v' w'); iFrame "Hw".
    iExists (v, w), (v', w'); simpl; eauto 10 with itauto.
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_Fst Δ Γ e e' τ1 τ2 {HΔ : ✓✓ Δ}
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e ≤log≤ e' ∷ (TProd τ1 τ2))
    :
      Δ ∥ Γ ⊩ Fst e ≤log≤ Fst e' ∷ τ1.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (FstCtx) v v' "[Hv #Hiv]"
                  (IHHtyped _ _ _ _ _ j (K ++ [FstCtx])); cbn.
    iDestruct "Hiv" as {w1 w2} "#[% [Hiv2 Hiv3]]".
    inversion H; subst.
    iPvs (step_fst _ _ _ j K (# (w2.1)) (w2.1) (# (w2.2)) (w2.2)
                   _ _ _ with "* -") as "Hw".
    iFrame "Hspec Hv"; trivial.
    iApply wp_fst; eauto using to_of_val; cbn.
    iNext. iExists _; iSplitL; trivial.
    (* unshelving *)
    Unshelve. all: eauto using to_of_val.
  Qed.

  Lemma typed_binary_interp_Snd Δ Γ e e' τ1 τ2 {HΔ : ✓✓ Δ}
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e ≤log≤ e' ∷ (TProd τ1 τ2))
    :
      Δ ∥ Γ ⊩ Snd e ≤log≤ Snd e' ∷ τ2.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (SndCtx) v v' "[Hv #Hiv]"
                  (IHHtyped _ _ _ _ _ j (K ++ [SndCtx])); cbn.
    iDestruct "Hiv" as {w1 w2} "#[% [Hiv2 Hiv3]]".
    inversion H; subst.
    iPvs (step_snd _ _ _ j K (# (w2.1)) (w2.1) (# (w2.2)) (w2.2)
                   _ _ _ with "* -") as "Hw".
    iFrame "Hspec Hv"; trivial.
    iApply wp_snd; eauto using to_of_val; cbn.
    iNext. iExists _; iSplitL; trivial.
    (* unshelving *)
    Unshelve. all: eauto using to_of_val.
  Qed.

  Lemma typed_binary_interp_InjL Δ Γ e e' τ1 τ2 {HΔ : ✓✓ Δ}
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e ≤log≤ e' ∷ τ1)
    :
      Δ ∥ Γ ⊩ InjL e ≤log≤ InjL e' ∷ (TSum τ1 τ2).
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (InjLCtx) v v' "[Hv #Hiv]"
                  (IHHtyped _ _ _ _ _ j (K ++ [InjLCtx])); cbn.
    value_case. iExists (InjLV v'); iFrame "Hv".
    iLeft; iExists _; iSplit; [|eauto]; simpl; trivial.
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_InjR Δ Γ e e' τ1 τ2 {HΔ : ✓✓ Δ}
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e ≤log≤ e' ∷ τ2)
    :
      Δ ∥ Γ ⊩ InjR e ≤log≤ InjR e' ∷ (TSum τ1 τ2).
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (InjRCtx) v v' "[Hv #Hiv]"
                  (IHHtyped _ _ _ _ _ j (K ++ [InjRCtx])); cbn.
    value_case. iExists (InjRV v'); iFrame "Hv".
    iRight; iExists _; iSplit; [|eauto]; simpl; trivial.
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_Case Δ Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3 {HΔ : ✓✓ Δ}
        (Htyped2 : typed (τ1 :: Γ) e1 τ3)
        (Htyped3 : typed (τ2 :: Γ) e2 τ3)
        (Htyped2' : typed (τ1 :: Γ) e1' τ3)
        (Htyped3' : typed (τ2 :: Γ) e2' τ3)
        (IHHtyped1 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e0 ≤log≤ e0' ∷ TSum τ1 τ2)
        (IHHtyped2 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ τ1 :: Γ ⊩ e1 ≤log≤ e1' ∷ τ3)
        (IHHtyped3 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ τ2 :: Γ ⊩ e2 ≤log≤ e2' ∷ τ3)
    :
      Δ ∥ Γ ⊩ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' ∷ τ3.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
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
      (* unshelving *)
      Unshelve. all: eauto using to_of_val.
  Qed.


  Lemma typed_binary_interp_Lam Δ Γ e e' τ1 τ2 {HΔ : ✓✓ Δ}
        (Htyped : typed (τ1 :: Γ) e τ2)
        (Htyped' : typed (τ1 :: Γ) e' τ2)
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ τ1 :: Γ ⊩ e ≤log≤ e' ∷ τ2)
    :
      Δ ∥ Γ ⊩ Lam e ≤log≤ Lam e' ∷  TArrow τ1 τ2.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
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
    (* unshelving *)
    Unshelve. all: eauto using to_of_val.
  Qed.

  Lemma typed_binary_interp_App Δ Γ e1 e2 e1' e2' τ1 τ2 {HΔ : ✓✓ Δ}
        (IHHtyped1 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e1 ≤log≤ e1' ∷ TArrow τ1 τ2)
        (IHHtyped2 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e2 ≤log≤ e2' ∷ τ1)
    :
      Δ ∥ Γ ⊩ App e1 e2 ≤log≤ App e1' e2' ∷  τ2.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (AppLCtx (e2.[env_subst (map fst vs)])) v v' "[Hv #Hiv]"
                  (IHHtyped1
                     _ _ _ _ _ j
                     (K ++ [(AppLCtx (e2'.[env_subst (map snd vs)]))])); cbn.
    smart_wp_bind (AppRCtx v) w w' "[Hw #Hiw]"
                  (IHHtyped2
                     _ _ _ _ _ j
                     (K ++ [AppRCtx v'])); cbn.
    iApply ("Hiv" $! j K (w, w')); simpl.
    iNext; iFrame "Hw"; trivial.
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_TLam Δ Γ e e' τ {HΔ : ✓✓ Δ}
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ),
            Δ ∥ map (λ t : type, t.[ren (+1)]) Γ ⊩ e ≤log≤ e' ∷ τ)
    :
      Δ ∥ Γ ⊩ TLam e ≤log≤ TLam e' ∷  TForall τ.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    value_case. iExists (TLamV _). iFrame "Htr"; simpl.
    iExists (e.[env_subst (map fst vs)], e'.[env_subst (map snd vs)]).
    iSplit; trivial.
    iIntros {τi}; destruct τi as [τi τiPr].
    iAlways. iNext. iIntros {j' K'} "Hv". simpl.
    iApply IHHtyped; [rewrite map_length; trivial|].
    iFrame "Hheap Hspec Hv".
    rewrite zip_with_context_interp_subst; trivial.
  Qed.

  Lemma typed_binary_interp_TApp Δ Γ e e' τ τ' {HΔ : ✓✓ Δ}
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e ≤log≤ e' ∷ TForall τ)
    :
      Δ ∥ Γ ⊩ TApp e ≤log≤ TApp e' ∷ τ.[τ'/].
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (TAppCtx) v v' "[Hv #Hiv]"
                    (IHHtyped _ _ _ _ _ j (K ++ [TAppCtx])); cbn.
    iDestruct "Hiv" as {e''} "[% He'']".
    inversion H; subst.
    iSpecialize ("He''" $! ((interp τ' Δ) ↾ _)); cbn.
    iPvs (step_Tlam _ _ _ j K (e''.2) _ with "* -") as "Hz".
    iFrame "Hspec Hv"; trivial.
    iApply wp_TLam.
    iRevert "He''"; iIntros "#He''". (*To get rid of □. Is this the best way?!*)
    iNext.
    iApply wp_wand_l; iSplitR; [|iApply "He''"; auto].
    iIntros {w} "Hw". iDestruct "Hw" as {w'} "[Hw #Hiw]".
    iExists _; iFrame "Hw".
    rewrite -interp_subst; trivial.
    (* unshelving *)
    Unshelve. all: trivial. simpl; typeclasses eauto.
  Qed.

  Lemma typed_binary_interp_Fold Δ Γ e e' τ {HΔ : ✓✓ Δ}
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ),
            Δ ∥ map (λ t : type, t.[ren (+1)]) Γ ⊩ e ≤log≤ e' ∷ τ)
    :
      Δ ∥ Γ ⊩ Fold e ≤log≤ Fold e' ∷  TRec τ.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
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
      (* unshelving *)
      Unshelve. all: rewrite map_length; trivial.
  Qed.

  Lemma typed_binary_interp_Unfold Δ Γ e e' τ {HΔ : ✓✓ Δ}
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e ≤log≤ e' ∷ TRec τ)
    :
      Δ ∥ Γ ⊩ Unfold e ≤log≤ Unfold e' ∷ τ.[(TRec τ)/].
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    iApply (@wp_bind _ _ _ [UnfoldCtx]);
      iApply wp_wand_l; iSplitR;
        [|iApply (IHHtyped _ _ _ _ _ j (K ++ [UnfoldCtx]));
          rewrite fill_app; simpl; repeat iSplitR; trivial].
    iIntros {v} "Hv". iDestruct "Hv" as {w} "[Hw #Hiw]"; rewrite fill_app.
    simpl. rewrite fixpoint_unfold; simpl.
    iRevert "Hiw"; iIntros "#Hiw". (*To get rid of □. Is this the best way?!*)
    change (fixpoint _) with (@interp _ _ _ (N .@ 1) (TRec τ) Δ).
    iDestruct "Hiw" as {z} "[% #Hiz]"; inversion H; subst.
    iPvs (step_Fold _ _ _ j K (# (z.2)) (z.2) _ _ with "* -") as "Hz".
    iFrame "Hspec Hw"; trivial.
    iApply wp_Fold; cbn; auto using to_of_val.
    iNext. iExists _; iFrame "Hz".
    rewrite -interp_subst; destruct z; trivial.
    (* unshelving *)
    Unshelve. all: eauto using to_of_val.
  Qed.


  Lemma typed_binary_interp_Fork Δ Γ e e' {HΔ : ✓✓ Δ}
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e ≤log≤ e' ∷ TUnit)
    :
      Δ ∥ Γ ⊩ Fork e ≤log≤ Fork e' ∷ TUnit.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
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
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_Alloc Δ Γ e e' τ {HΔ : ✓✓ Δ}
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e ≤log≤ e' ∷ τ)
    :
      Δ ∥ Γ ⊩ Alloc e ≤log≤ Alloc e' ∷ (Tref τ).
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
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
                                 ((@interp _ _ _ (N .@ 1) τ) Δ) w)%I)
      as "Hinv" with "[Hl Hl']".
    { iExists (v, v'); iFrame "Hl Hl' Hiv"; trivial. }
    iPvs (inv_alloc _ with "[Hinv]") as "HN"; eauto 1.
    { iNext; iExact "Hinv". }
    iPvsIntro; iExists (LocV l'); iSplit; [iExact "Hj"|].
    iExists (l, l'); iSplit; trivial.
    (* unshelving *)
    Unshelve. all: eauto using to_of_val.
  Qed.

  Lemma Disjoint_after_dot : ∀ i (l : loc * loc), i ≠ 1 →  N .@ i ⊥ N .@ 1 .@ l.
  Proof.
    intros i l h.
    apply ndot_preserve_disjoint_r, ndot_ne_disjoint; auto.
  Qed.

  Ltac SolveDisj i l :=
    let Hneq := fresh "Hneq" in
    let Hdsj := fresh "Hdsj" in
    assert (Hneq : i ≠ 1) by omega; set (Hdsj := Disjoint_after_dot i l Hneq);
    clearbody Hdsj; clear Hneq; revert Hdsj;
    generalize (N .@ 1) as S1; generalize (N .@ 2) as S2;
    intros S1 S2 Hsdj; set_solver_ndisj.

  Lemma typed_binary_interp_Load Δ Γ e e' τ {HΔ : ✓✓ Δ}
        (IHHtyped : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e ≤log≤ e' ∷ (Tref τ))
    :
      Δ ∥ Γ ⊩ Load e ≤log≤ Load e' ∷ τ.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (LoadCtx) v v' "[Hv #Hiv]"
                  (IHHtyped
                     _ _ _ _ _ j (K ++ [LoadCtx])).
    iDestruct "Hiv" as {l} "[% Hinv]".
    inversion H; subst.
    iApply wp_atomic; cbn; trivial.
    iPvsIntro.
    iInv (N .@ 1 .@ l) as {w} "[Hw1 [Hw2 #Hw3]]".
    iTimeless "Hw2".
    iPvs (step_load _ _ _ j K (l.2) 1 (w.2) _ with "[Hv Hw2]") as "[Hv Hw2]".
    iFrame "Hspec Hv"; trivial.
    iApply (wp_load _ _ _ 1); [|iFrame "Hheap"]; trivial.
    SolveDisj 2 l.
    iNext. iFrame "Hw1". iIntros "Hw1".
    iSplitL "Hw1 Hw2".
    + iNext; iExists w; iFrame "Hw1 Hw2 Hw3"; trivial.
    + iPvsIntro.
      destruct w as [w1 w2]; iExists (w2); iFrame "Hv Hw3"; trivial.
      (* unshelving *)
      Unshelve. all: eauto using to_of_val.
      SolveDisj 3 l.
  Qed.

  Lemma typed_binary_interp_Store Δ Γ e1 e2 e1' e2' τ {HΔ : ✓✓ Δ}
        (IHHtyped1 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e1 ≤log≤ e1' ∷ (Tref τ))
        (IHHtyped2 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e2 ≤log≤ e2' ∷ τ)
    :
      Δ ∥ Γ ⊩ Store e1 e2 ≤log≤ Store e1' e2' ∷ TUnit.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
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
    iInv (N .@ 1 .@ l) as {z} "[Hw1 [Hw2 #Hw3]]".
    eapply bool_decide_spec; eauto using to_of_val.
    iTimeless "Hw2".
    iPvs (step_store _ _ _ j K (l.2) (z.2) (# w') w' _ _ with "[Hw Hw2]")
      as "[Hw Hw2]".
    iFrame "Hspec Hw Hw2"; trivial.
    iApply (wp_store (N .@ 2)); auto using to_of_val.
    SolveDisj 2 l.
    iFrame "Hheap Hw1". iNext. iIntros "Hw1".
    iSplitL "Hw1 Hw2".
    + iNext; iExists (w, w'); iFrame "Hw1 Hw2 Hiw"; trivial.
    + iPvsIntro. iExists UnitV; iFrame "Hw" ; iSplit; trivial.
      (* unshelving *)
      Unshelve. all: eauto using to_of_val.
      SolveDisj 3 l.
  Qed.

  Lemma typed_binary_interp_CAS Δ Γ e1 e2 e3 e1' e2' e3' τ {HΔ : ✓✓ Δ}
        (HEqτ : EqType τ)
        (IHHtyped1 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e1 ≤log≤ e1' ∷ Tref τ)
        (IHHtyped2 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e2 ≤log≤ e2' ∷ τ)
        (IHHtyped3 : ∀ Δ (HΔ : ✓✓ Δ), Δ ∥ Γ ⊩ e3 ≤log≤ e3' ∷ τ)
    :
      Δ ∥ Γ ⊩ CAS e1 e2 e3 ≤log≤ CAS e1' e2' e3' ∷ TBOOL.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
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
    inversion H; subst.
    iApply wp_atomic; trivial;
      [cbn; eauto 10 using to_of_val|].
    iPvsIntro.
    iInv (N .@ 1 .@ l) as {z} "[Hw1 [Hw2 #Hw3]]".
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
      iApply (wp_cas_suc (N .@ 2)); eauto using to_of_val.
      SolveDisj 2 l.
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
      iApply (wp_cas_fail (N .@ 2)); eauto using to_of_val.
      SolveDisj 2 l.
      iFrame "Hheap Hw1".
      iNext. iIntros "Hw1".
      iSplitL "Hw1 Hw2".
      * iNext; iExists (_, _); iFrame "Hw1 Hw2"; trivial.
      * iPvsIntro. iExists FALSEV; iFrame "Hw".
        iRight; iExists (UnitV, UnitV); auto with itauto.
        (* unshelving *)
        Unshelve. all: eauto using to_of_val. all: SolveDisj 3 l.
  Qed.


  Lemma typed_binary_interp Δ Γ e τ {HΔ : context_interp_Persistent Δ}
        (Htyped : typed Γ e τ)
    : Δ ∥ Γ ⊩ e ≤log≤ e ∷ τ.
  Proof.
    revert Δ HΔ; induction Htyped; intros Δ HΔ.
    - intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
      destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
      { by rewrite -Hlen; apply lookup_lt_Some with τ. }
      rewrite /env_subst. repeat rewrite map_lookup. rewrite Hv; simpl.
      value_case.
      iExists _; iFrame "Htr".
      iApply (big_and_elem_of with "HΓ").
      apply elem_of_list_lookup_2 with x.
      rewrite lookup_zip_with; simplify_option_eq; destruct v; trivial.
    - intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
      value_case. iExists UnitV; iFrame "Htr"; iSplit; trivial.
    - apply typed_binary_interp_Pair; trivial.
    - eapply typed_binary_interp_Fst; trivial.
    - eapply typed_binary_interp_Snd; trivial.
    - eapply typed_binary_interp_InjL; trivial.
    - eapply typed_binary_interp_InjR; trivial.
    - eapply typed_binary_interp_Case; eauto.
    - eapply typed_binary_interp_Lam; eauto.
    - eapply typed_binary_interp_App; trivial.
    - eapply typed_binary_interp_TLam; trivial.
    - eapply typed_binary_interp_TApp; trivial.
    - eapply typed_binary_interp_Fold; trivial.
    - eapply typed_binary_interp_Unfold; trivial.
    - eapply typed_binary_interp_Fork; trivial.
    - eapply typed_binary_interp_Alloc; trivial.
    - eapply typed_binary_interp_Load; trivial.
    - eapply typed_binary_interp_Store; trivial.
    - eapply typed_binary_interp_CAS; eauto.
  Qed.

End typed_interp.

Notation "Δ ∥ Γ ⊩ e '≤log≤' e' ∷ τ" := (bin_log_related Δ Γ e e' τ)
                                       (at level 20) : bin_logrel_scope.