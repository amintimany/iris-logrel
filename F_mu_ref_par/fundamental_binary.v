Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import iris_logrel.F_mu_ref_par.lang iris_logrel.F_mu_ref_par.typing
        iris_logrel.F_mu_ref_par.rules iris_logrel.F_mu_ref_par.rules_binary
        iris_logrel.F_mu_ref_par.logrel_binary.
From iris.program_logic Require Export lifting.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
Require Import iris.proofmode.tactics iris.proofmode.invariants.
Import uPred.

Section typed_interp.
  Context {Σ : gFunctors} {iI : heapIG Σ} {iS : cfgSG Σ} {N : namespace}.
  Implicit Types Δ : varC -n> bivalC -n> iPropG lang Σ.
  Implicit Types P Q R : iPropG lang Σ.
  Notation "# v" := (of_val v) (at level 20).

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) ident(w)
        constr(Hv) uconstr(Hp) :=
    iApply (@wp_bind _ _ _ [ctx]);
    iApply wp_wand_l; iSplitR;
    [|iApply Hp; rewrite fill_app; simpl; repeat iSplitR; trivial];
    let Htmp := iFresh in
    iIntros {v} Htmp; iDestruct Htmp as {w} Hv;
    rewrite fill_app; simpl.

  Local Ltac value_case := iApply wp_value; [cbn; rewrite ?to_of_val; trivial|].

  Lemma map_lookup {A B} (l : list A) (f : A → B) k :
    (map f l) !! k = option_map f (l !! k).
  Proof.
    revert k; induction l => k; simpl; trivial.
    destruct k; simpl; trivial.
  Qed.

  Definition bin_log_related Δ Γ e e' τ {HΔ : ∀ x vw, PersistentP (Δ x vw)} :=
    ∀ vs, List.length Γ = List.length vs →
    ∀ ρ j K,
      heapI_ctx (N .@ 2) ★ Spec_ctx (N .@ 3) ρ ★
        [∧] zip_with (λ τ, interp (N .@ 1) τ Δ) Γ vs ★
        j ⤇ fill K (e'.[env_subst (map snd vs)])
      ⊢ WP e.[env_subst (map fst vs)] {{ v, ∃ v',
          j ⤇ fill K (# v') ★ interp (N .@ 1) τ Δ (v, v') }}.

  Notation "Δ ∥ Γ ⊩ e '≤log≤' e' ∷ τ" := (bin_log_related Δ Γ e e' τ)
                                       (at level 20) : bin_logrel_scope.

  Local Open Scope bin_logrel_scope.

  Notation "✓✓ Δ" := (∀ x v, PersistentP (Δ x v)) (at level 20).

  Lemma typed_binary_interp_Pair Δ Γ e1 e2 e1' e2' τ1 τ2 {HΔ : ✓✓ Δ}
      (IHHtyped1 : Δ ∥ Γ ⊩ e1 ≤log≤ e1' ∷ τ1)
      (IHHtyped2 : Δ ∥ Γ ⊩ e2 ≤log≤ e2' ∷ τ2) :
    Δ ∥ Γ ⊩ Pair e1 e2 ≤log≤ Pair e1' e2' ∷ TProd τ1 τ2.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    smart_wp_bind (PairLCtx e2.[env_subst (map fst vs)]) v v' "[Hv #Hiv]"
                  (IHHtyped1 _ _ _ j
                             (K ++ [PairLCtx e2'.[env_subst (map snd vs)] ])).
    smart_wp_bind (PairRCtx v) w w' "[Hw #Hiw]"
                  (IHHtyped2 _ _ _ j (K ++ [(PairRCtx v')])).
    value_case. iExists (PairV v' w'); iFrame "Hw".
    iExists (v, w), (v', w'); simpl; repeat iSplit; trivial.
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_Fst Δ Γ e e' τ1 τ2 {HΔ : ✓✓ Δ}
      (IHHtyped : Δ ∥ Γ ⊩ e ≤log≤ e' ∷ TProd τ1 τ2) :
    Δ ∥ Γ ⊩ Fst e ≤log≤ Fst e' ∷ τ1.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (FstCtx) v v' "[Hv #Hiv]"
                  (IHHtyped _ _ _ j (K ++ [FstCtx])); cbn.
    iDestruct "Hiv" as {w1 w2} "#[% [Hiv2 Hiv3]]".
    inversion H; subst.
    iPvs (step_fst _ _ _ j K (# (w2.1)) (w2.1) (# (w2.2)) (w2.2)
                   _ _ _ with "* [-]") as "Hw".
    iFrame "Hspec Hv"; trivial.
    iApply wp_fst; eauto using to_of_val; cbn.
    (* unshelving *)
    Unshelve. all: eauto using to_of_val.
  Qed.

  Lemma typed_binary_interp_Snd Δ Γ e e' τ1 τ2 {HΔ : ✓✓ Δ}
      (IHHtyped : Δ ∥ Γ ⊩ e ≤log≤ e' ∷ TProd τ1 τ2) :
    Δ ∥ Γ ⊩ Snd e ≤log≤ Snd e' ∷ τ2.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (SndCtx) v v' "[Hv #Hiv]"
                  (IHHtyped _ _ _ j (K ++ [SndCtx])); cbn.
    iDestruct "Hiv" as {w1 w2} "#[% [Hiv2 Hiv3]]".
    inversion H; subst.
    iPvs (step_snd _ _ _ j K (# (w2.1)) (w2.1) (# (w2.2)) (w2.2)
                   _ _ _ with "* [-]") as "Hw".
    iFrame "Hspec Hv"; trivial.
    iApply wp_snd; eauto using to_of_val; cbn.
    (* unshelving *)
    Unshelve. all: eauto using to_of_val.
  Qed.

  Lemma typed_binary_interp_InjL Δ Γ e e' τ1 τ2 {HΔ : ✓✓ Δ}
      (IHHtyped : Δ ∥ Γ ⊩ e ≤log≤ e' ∷ τ1) :
    Δ ∥ Γ ⊩ InjL e ≤log≤ InjL e' ∷ (TSum τ1 τ2).
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (InjLCtx) v v' "[Hv #Hiv]"
                  (IHHtyped _ _ _ j (K ++ [InjLCtx])); cbn.
    value_case. iExists (InjLV v'); iFrame "Hv".
    iLeft; iExists _; iSplit; [|eauto]; simpl; trivial.
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_InjR Δ Γ e e' τ1 τ2 {HΔ : ✓✓ Δ}
      (IHHtyped : Δ ∥ Γ ⊩ e ≤log≤ e' ∷ τ2) :
    Δ ∥ Γ ⊩ InjR e ≤log≤ InjR e' ∷ TSum τ1 τ2.
  Proof.
    intros vs Hlen ρ j K. iIntros "[#Hheap [#Hspec [#HΓ Htr]]]"; cbn.
    smart_wp_bind (InjRCtx) v v' "[Hv #Hiv]"
                  (IHHtyped _ _ _ j (K ++ [InjRCtx])); cbn.
    value_case. iExists (InjRV v'); iFrame "Hv".
    iRight; iExists _; iSplit; [|eauto]; simpl; trivial.
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_Case Δ Γ (e0 e1 e2 e0' e1' e2' : expr) τ1 τ2 τ3
      {HΔ : ✓✓ Δ}
      (Hclosed2 : ∀ f, e1.[iter (S (List.length Γ)) up f] = e1)
      (Hclosed3 : ∀ f, e2.[iter (S (List.length Γ)) up f] = e2)
      (Hclosed2' : ∀ f, e1'.[iter (S (List.length Γ)) up f] = e1')
      (Hclosed3' : ∀ f, e2'.[iter (S (List.length Γ)) up f] = e2')
      (IHHtyped1 : Δ ∥ Γ ⊩ e0 ≤log≤ e0' ∷ TSum τ1 τ2)
      (IHHtyped2 : Δ ∥ τ1 :: Γ ⊩ e1 ≤log≤ e1' ∷ τ3)
      (IHHtyped3 : Δ ∥ τ2 :: Γ ⊩ e2 ≤log≤ e2' ∷ τ3) :
    Δ ∥ Γ ⊩ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' ∷ τ3.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    smart_wp_bind (CaseCtx _ _) v v' "[Hv #Hiv]"
                  (IHHtyped1 _ _ _ j (K ++ [CaseCtx _ _])); cbn.
    iDestruct "Hiv" as "[Hiv|Hiv]".
    + iDestruct "Hiv" as {w} "[% Hw]"; simplify_eq.
      iPvs (step_case_inl _ _ _ j K (# (w.2)) (w.2) _ _
                          _ _ with "* [-]") as "Hz".
      iFrame "Hspec Hv"; trivial.
      iApply wp_case_inl; auto 1 using to_of_val.
      asimpl.
      specialize (IHHtyped2 (w::vs)); simpl in IHHtyped2.
      erewrite <- ?n_closed_subst_head_simpl in IHHtyped2; eauto;
        simpl; try rewrite map_length; eauto with f_equal. iNext.
      iApply IHHtyped2; eauto.
    + iDestruct "Hiv" as {w} "[% Hw]"; simplify_eq.
      iPvs (step_case_inr _ _ _ j K (# (w.2)) (w.2) _ _ _ _ with "* [-]") as "Hz".
      iFrame "Hspec Hv"; trivial.
      iApply wp_case_inr; auto 1 using to_of_val.
      asimpl.
      specialize (IHHtyped3 (w::vs)); simpl in IHHtyped3.
      erewrite <- ?n_closed_subst_head_simpl in IHHtyped3; eauto;
        simpl; try rewrite map_length; eauto with f_equal. iNext.
      iApply IHHtyped3; eauto 10.
      (* unshelving *)
      Unshelve. all: eauto using to_of_val.
  Qed.

  Lemma typed_binary_interp_If Δ Γ e0 e1 e2 e0' e1' e2' τ {HΔ : ✓✓ Δ}
      (IHHtyped1 : Δ ∥ Γ ⊩ e0 ≤log≤ e0' ∷ TBool)
      (IHHtyped2 : Δ ∥ Γ ⊩ e1 ≤log≤ e1' ∷ τ)
      (IHHtyped3 : Δ ∥ Γ ⊩ e2 ≤log≤ e2' ∷ τ) :
    Δ ∥ Γ ⊩ If e0 e1 e2 ≤log≤ If e0' e1' e2' ∷ τ.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    smart_wp_bind (IfCtx _ _) v v' "[Hv #Hiv]"
                  (IHHtyped1 _ _ _ j (K ++ [IfCtx _ _])); cbn.
    iDestruct "Hiv" as { [] } "[% %]"; simplify_eq/=.
    + iPvs (step_if_true _ _ _ j K _ _ _ with "* [-]") as "Hz".
      iFrame "Hspec Hv"; trivial. iApply wp_if_true. iNext.
      iApply IHHtyped2; eauto.
    + iPvs (step_if_false _ _ _ j K _ _ _ with "* [-]") as "Hz".
      iFrame "Hspec Hv"; trivial. iApply wp_if_false. iNext.
      iApply IHHtyped3; eauto.
      (* unshelving *)
      Unshelve. all: eauto using to_of_val.
  Qed.

  Lemma typed_binary_interp_nat_bin_op Δ Γ op e1 e2 e1' e2' {HΔ : ✓✓ Δ}
      (IHHtyped1 : Δ ∥ Γ ⊩ e1 ≤log≤ e1' ∷ TNat)
      (IHHtyped2 : Δ ∥ Γ ⊩ e2 ≤log≤ e2' ∷ TNat) :
    Δ ∥ Γ ⊩ NBOP op e1 e2 ≤log≤ NBOP op e1' e2' ∷ NatBinOP_res_type op.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr)"; cbn.
    smart_wp_bind (NBOPLCtx _ _) v v' "[Hv #Hiv]"
                  (IHHtyped1 _ _ _ j (K ++ [NBOPLCtx _ _])); cbn.
    smart_wp_bind (NBOPRCtx _ _) w w' "[Hw #Hiw]"
                  (IHHtyped2 _ _ _ j (K ++ [NBOPRCtx _ _])); cbn.
    iDestruct "Hiv" as {n} "[% %]"; subst; simpl.
    iDestruct "Hiw" as {n'} "[% %]"; subst; simpl.
    iPvs (step_nat_bin_op _ _ _ j K _ _ _ _ with "* [-]") as "Hz".
    iFrame "Hspec Hw"; trivial. iApply wp_nat_bin_op. iNext.
    iExists _; iSplitL; eauto.
    destruct op; simpl; try destruct eq_nat_dec; try destruct le_dec;
      try destruct lt_dec; iExists _; iSplit; trivial.
    (* unshelving *)
    Unshelve. all: eauto using to_of_val.
  Qed.

  Lemma typed_binary_interp_Lam Δ Γ (e e' : expr) τ1 τ2 {HΔ : ✓✓ Δ}
      (Hclosed : ∀ f, e.[iter (S (S (List.length Γ))) up f] = e)
      (Hclosed' : ∀ f, e'.[iter (S (S (List.length Γ))) up f] = e')
      (IHHtyped : Δ ∥ TArrow τ1 τ2 :: τ1 :: Γ ⊩ e ≤log≤ e' ∷ τ2) :
    Δ ∥ Γ ⊩ Lam e ≤log≤ Lam e' ∷ TArrow τ1 τ2.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    value_case. iExists (LamV _). iFrame "Htr". iAlways.
    iLöb as "IH". iIntros {j' K' v} "[#Hiv Hv]".
    iApply wp_lam; auto 1 using to_of_val. iNext.
    iPvs (step_lam _ _ _ j' K' _ (# (v.2)) (v.2) _ _ with "* [-]") as "Hz".
    iFrame "Hspec Hv"; trivial.
    asimpl.
    specialize (IHHtyped ((LamV e.[upn 2 (env_subst (map fst vs))],
                           LamV e'.[upn 2 (env_subst (map snd vs))])
                            :: v :: vs)). simpl in IHHtyped.
    erewrite <- ?n_closed_subst_head_simpl_2 in IHHtyped; eauto; simpl;
      try rewrite map_length; auto.
    iApply IHHtyped; auto. repeat iSplitR; eauto.
    (* unshelving *)
    Unshelve. all: eauto using to_of_val.
  Qed.

  Lemma typed_binary_interp_App Δ Γ e1 e2 e1' e2' τ1 τ2 {HΔ : ✓✓ Δ}
      (IHHtyped1 : Δ ∥ Γ ⊩ e1 ≤log≤ e1' ∷ TArrow τ1 τ2)
      (IHHtyped2 : Δ ∥ Γ ⊩ e2 ≤log≤ e2' ∷ τ1) :
    Δ ∥ Γ ⊩ App e1 e2 ≤log≤ App e1' e2' ∷  τ2.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    smart_wp_bind (AppLCtx (e2.[env_subst (map fst vs)])) v v' "[Hv #Hiv]"
                  (IHHtyped1 _ _ _ j
                     (K ++ [(AppLCtx (e2'.[env_subst (map snd vs)]))])); cbn.
    smart_wp_bind (AppRCtx v) w w' "[Hw #Hiw]"
                  (IHHtyped2 _ _ _ j (K ++ [AppRCtx v'])); cbn.
    iApply ("Hiv" $! j K (w, w')); simpl; eauto.
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_TLam Δ Γ e e' τ {HΔ : ✓✓ Δ}
      (IHHtyped : ∀ (τi : bivalC -n> _) (Hpr: ∀ vw, PersistentP (τi vw)),
      (extend_context_interp_fun1 τi Δ) ∥ map (λ t : type, t.[ren (+1)]) Γ
                                        ⊩ e ≤log≤ e' ∷ τ) :
    Δ ∥ Γ ⊩ TLam e ≤log≤ TLam e' ∷ TForall τ.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    value_case. iExists (TLamV _). iFrame "Htr"; simpl.
    iAlways; iIntros {τi j' K'} "% Hv /=".
    iApply wp_TLam; iNext.
    iPvs (step_Tlam _ _ _ j' K' (e'.[env_subst (map snd vs)]) _ with "* [-]")
      as "Hz".
    iFrame "Hspec Hv"; trivial.
    iApply IHHtyped; [rewrite map_length; trivial|].
    iFrame "Hheap Hspec".
    rewrite zip_with_context_interp_subst; by iFrame "HΓ".
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_TApp Δ Γ e e' τ τ' {HΔ : ✓✓ Δ}
      (IHHtyped : Δ ∥ Γ ⊩ e ≤log≤ e' ∷ TForall τ) :
    Δ ∥ Γ ⊩ TApp e ≤log≤ TApp e' ∷ τ.[τ'/].
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    smart_wp_bind (TAppCtx) v v' "[Hj #Hv]"
                    (IHHtyped _ _ _ j (K ++ [TAppCtx])); cbn.
    iApply wp_wand_r; iSplitL.
    { iApply ("Hv" $! (interp (N .@ 1) τ' Δ) with "[#] Hj"); iPureIntro; apply _. }
    iIntros {w} "Hw". iDestruct "Hw" as {w'} "[Hw #Hiw]".
    iExists _; rewrite -interp_subst; eauto.
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_Fold Δ Γ e e' τ {HΔ : ✓✓ Δ}
      (IHHtyped : Δ ∥ Γ ⊩ e ≤log≤ e' ∷ τ.[(TRec τ)/]) :
    Δ ∥ Γ ⊩ Fold e ≤log≤ Fold e' ∷ TRec τ.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    iApply (@wp_bind _ _ _ [FoldCtx]);
      iApply wp_wand_l; iSplitR;
        [|iApply (IHHtyped _ _ _ j (K ++ [FoldCtx]));
          rewrite fill_app; simpl; repeat iSplitR; trivial].
    iIntros {v} "Hv"; iDestruct "Hv" as {w} "[Hv #Hiv]";
      rewrite fill_app.
    value_case. iExists (FoldV w); iFrame "Hv".
    rewrite fixpoint_unfold; cbn.
    rewrite -interp_subst; trivial.
    iAlways; iExists (_, _); eauto.
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_Unfold Δ Γ e e' τ {HΔ : ✓✓ Δ}
      (IHHtyped : Δ ∥ Γ ⊩ e ≤log≤ e' ∷ TRec τ) :
    Δ ∥ Γ ⊩ Unfold e ≤log≤ Unfold e' ∷ τ.[(TRec τ)/].
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    iApply (@wp_bind _ _ _ [UnfoldCtx]);
      iApply wp_wand_l; iSplitR;
        [|iApply (IHHtyped _ _ _ j (K ++ [UnfoldCtx]));
          rewrite fill_app; simpl; repeat iSplitR; trivial].
    iIntros {v} "Hv". iDestruct "Hv" as {w} "[Hw #Hiw]"; rewrite fill_app.
    simpl. rewrite fixpoint_unfold; simpl.
    change (fixpoint _) with (@interp _ _ _ (N .@ 1) (TRec τ) Δ).
    iDestruct "Hiw" as {z} "#[% Hiz]"; simplify_eq/=.
    iPvs (step_Fold _ _ _ j K (# (z.2)) (z.2) _ _ with "* [-]") as "Hz".
    iFrame "Hspec Hw"; trivial.
    iApply wp_Fold; cbn; auto using to_of_val.
    iNext. iExists _; iFrame "Hz".
    rewrite -interp_subst; destruct z; trivial.
    (* unshelving *)
    Unshelve. all: eauto using to_of_val.
  Qed.

  Lemma typed_binary_interp_Fork Δ Γ e e' {HΔ : ✓✓ Δ}
      (IHHtyped : Δ ∥ Γ ⊩ e ≤log≤ e' ∷ TUnit) :
    Δ ∥ Γ ⊩ Fork e ≤log≤ Fork e' ∷ TUnit.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    iPvs (step_fork _ _ _ j K _ _ with "* [-]") as {j'} "[Hz1 Hz2]"; first by iFrame.
    iApply wp_fork; iNext; iSplitL "Hz1".
    + iExists UnitV; iFrame "Hz1"; eauto.
    + iApply wp_wand_l; iSplitR; [|iApply (IHHtyped _ _ _ _ [])]; eauto.
    (* unshelving *)
    Unshelve. all: trivial.
  Qed.

  Lemma typed_binary_interp_Alloc Δ Γ e e' τ {HΔ : ✓✓ Δ}
      (IHHtyped : Δ ∥ Γ ⊩ e ≤log≤ e' ∷ τ) :
    Δ ∥ Γ ⊩ Alloc e ≤log≤ Alloc e' ∷ Tref τ.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    smart_wp_bind (AllocCtx) v v' "[Hv #Hiv]"
                  (IHHtyped _ _ _ j (K ++ [AllocCtx])).
    iApply wp_pvs.
    iPvs (step_alloc _ _ _ j K (# v') v' _ _ with "* [-]") as {l'} "[Hj Hl']"; eauto.
    iApply wp_alloc; auto 1 using to_of_val.
    iFrame "Hheap". iNext. iIntros {l} "Hl".
    iAssert ((∃ w : val * val, l ↦ᵢ w.1 ★ l' ↦ₛ w.2 ★
                                 ((@interp _ _ _ (N .@ 1) τ) Δ) w)%I)
      with "[Hl Hl']" as "Hinv".
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
      (IHHtyped : Δ ∥ Γ ⊩ e ≤log≤ e' ∷ (Tref τ)) :
    Δ ∥ Γ ⊩ Load e ≤log≤ Load e' ∷ τ.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    smart_wp_bind (LoadCtx) v v' "[Hv #Hiv]"
                  (IHHtyped _ _ _ j (K ++ [LoadCtx])).
    iDestruct "Hiv" as {l} "[% Hinv]"; simplify_eq/=.
    iApply wp_pvs.
    iInv (N .@ 1 .@ l) as {w} "[Hw1 [Hw2 #Hw3]]".
    iTimeless "Hw2".
    iPvs (step_load _ _ _ j K (l.2) 1 (w.2) _ with "[Hv Hw2]") as "[Hv Hw2]".
    iFrame "Hspec Hv"; trivial.
    iApply (wp_load _ _ _ 1); [|iFrame "Hheap"]; trivial.
    SolveDisj 2 l.
    iFrame "Hw1". iIntros "> Hw1". iSplitL "Hw1 Hw2".
    + iNext; iExists w; by iFrame.
    + iPvsIntro.
      destruct w as [w1 w2]; iExists w2; iFrame "Hv Hw3"; trivial.
      (* unshelving *)
      Unshelve. all: eauto using to_of_val.
      SolveDisj 3 l.
  Qed.

  Lemma typed_binary_interp_Store Δ Γ e1 e2 e1' e2' τ {HΔ : ✓✓ Δ}
      (IHHtyped1 : Δ ∥ Γ ⊩ e1 ≤log≤ e1' ∷ (Tref τ))
      (IHHtyped2 : Δ ∥ Γ ⊩ e2 ≤log≤ e2' ∷ τ) :
    Δ ∥ Γ ⊩ Store e1 e2 ≤log≤ Store e1' e2' ∷ TUnit.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    smart_wp_bind (StoreLCtx _) v v' "[Hv #Hiv]"
                  (IHHtyped1 _ _ _ j (K ++ [StoreLCtx _])).
    smart_wp_bind (StoreRCtx _) w w' "[Hw #Hiw]"
                  (IHHtyped2 _ _ _ j (K ++ [StoreRCtx _])).
    iDestruct "Hiv" as {l} "[% Hinv]"; simplify_eq/=.
    iApply wp_pvs.
    iInv (N .@ 1 .@ l) as {z} "[Hw1 [Hw2 #Hw3]]".
    eapply bool_decide_spec; eauto using to_of_val.
    iTimeless "Hw2".
    iPvs (step_store _ _ _ j K (l.2) (z.2) (# w') w' _ _ with "[Hw Hw2]")
      as "[Hw Hw2]".
    iFrame "Hspec Hw Hw2"; trivial.
    iApply (wp_store (N .@ 2)); auto using to_of_val.
    SolveDisj 2 l.
    iFrame "Hheap Hw1". iIntros "> Hw1".
    iSplitL "Hw1 Hw2".
    + iNext; iExists (w, w'); by iFrame.
    + iPvsIntro. iExists UnitV; iFrame "Hw" ; iSplit; trivial.
      (* unshelving *)
      Unshelve. all: eauto using to_of_val.
      SolveDisj 3 l.
  Qed.

  Lemma typed_binary_interp_CAS Δ Γ e1 e2 e3 e1' e2' e3' τ {HΔ : ✓✓ Δ}
      (HEqτ : EqType τ)
      (IHHtyped1 : Δ ∥ Γ ⊩ e1 ≤log≤ e1' ∷ Tref τ)
      (IHHtyped2 : Δ ∥ Γ ⊩ e2 ≤log≤ e2' ∷ τ)
      (IHHtyped3 : Δ ∥ Γ ⊩ e3 ≤log≤ e3' ∷ τ) :
    Δ ∥ Γ ⊩ CAS e1 e2 e3 ≤log≤ CAS e1' e2' e3' ∷ TBool.
  Proof.
    iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
    smart_wp_bind (CasLCtx _ _) v v' "[Hv #Hiv]"
                  (IHHtyped1 _ _ _ j (K ++ [CasLCtx _ _])).
    smart_wp_bind (CasMCtx _ _) w w' "[Hw #Hiw]"
                  (IHHtyped2 _ _ _ j (K ++ [CasMCtx _ _])).
    smart_wp_bind (CasRCtx _ _) u u' "[Hu #Hiu]"
                  (IHHtyped3 _ _ _ j (K ++ [CasRCtx _ _])).
    iDestruct "Hiv" as {l} "[% Hinv]"; simplify_eq/=.
    iApply wp_pvs.
    iInv (N .@ 1 .@ l) as { [z1 z2] } "[Hw1 [Hw2 #Hw3]]".
    eapply bool_decide_spec; eauto 10 using to_of_val.
    iTimeless "Hw2".
    destruct (val_dec_eq z1 w) as [|Hneq]; subst.
    + iPvs (step_cas_suc _ _ _ j K (l.2) (# w') w' z2 (# u') u' _ _ _
            with "[Hu Hw2]") as "[Hw Hw2]"; simpl.
      { iFrame "Hspec Hu Hw2". iNext.
        rewrite ?EqType_related_eq; trivial.
        iDestruct "Hiw" as "%". iDestruct "Hw3" as "%".
        repeat subst; trivial. }
      iApply (wp_cas_suc (N .@ 2)); eauto using to_of_val.
      SolveDisj 2 l.
      iFrame "Hheap Hw1". iIntros "> Hw1".
      iSplitL "Hw1 Hw2".
      * iNext; iExists (_, _); iFrame "Hw1 Hw2"; trivial.
      * iPvsIntro. iExists (♭v true); iFrame "Hw"; eauto.
    + iPvs (step_cas_fail _ _ _ j K (l.2) 1 (z2) (# w') w' (# u') u' _ _ _
            with "[Hu Hw2]") as "[Hw Hw2]"; simpl.
      { iFrame "Hspec Hu Hw2". iNext.
        rewrite ?EqType_related_eq; trivial.
        iDestruct "Hiw" as "%". iDestruct "Hw3" as "%"; subst; eauto. }
      iApply (wp_cas_fail (N .@ 2)); eauto using to_of_val.
      SolveDisj 2 l.
      iFrame "Hheap Hw1". iIntros "> Hw1". iSplitL "Hw1 Hw2".
      * iNext; iExists (_, _); iFrame "Hw1 Hw2"; trivial.
      * iPvsIntro. iExists (♭v false); iFrame "Hw". iExists _; iSplit; trivial.
        (* unshelving *)
        Unshelve. all: eauto using to_of_val. all: SolveDisj 3 l.
  Qed.

  Lemma typed_binary_interp Δ Γ e τ {HΔ : ∀ x vw, PersistentP (Δ x vw)}
    (Htyped : typed Γ e τ) : Δ ∥ Γ ⊩ e ≤log≤ e ∷ τ.
  Proof.
    revert Δ HΔ; induction Htyped; intros Δ HΔ.
    - iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
      destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
      { by rewrite -Hlen; apply lookup_lt_Some with τ. }
      rewrite /env_subst. repeat rewrite map_lookup. rewrite Hv; simpl.
      value_case.
      iExists _; iFrame "Htr".
      iApply (big_and_elem_of with "HΓ").
      apply elem_of_list_lookup_2 with x.
      rewrite lookup_zip_with; simplify_option_eq; destruct v; trivial.
    - iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
      value_case. iExists UnitV; eauto.
    - iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
      value_case. iExists (♯v _); eauto.
    - iIntros {vs Hlen ρ j K} "(#Hheap & #Hspec & #HΓ & Htr) /=".
      value_case. iExists (♭v _); eauto.
    - apply typed_binary_interp_nat_bin_op; trivial.
    - apply typed_binary_interp_Pair; trivial.
    - eapply typed_binary_interp_Fst; trivial.
    - eapply typed_binary_interp_Snd; trivial.
    - eapply typed_binary_interp_InjL; trivial.
    - eapply typed_binary_interp_InjR; trivial.
    - eapply typed_binary_interp_Case; eauto;
        match goal with H : _ |- _ => eapply (typed_n_closed _ _ _ H) end.
    - eapply typed_binary_interp_If; eauto.
    - eapply typed_binary_interp_Lam; eauto;
        match goal with H : _ |- _ => eapply (typed_n_closed _ _ _ H) end.
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
Delimit Scope bin_logrel_scope with bin_logrel.
