From iris_logrel.F_mu_ref_conc Require Export logrel_binary.
From iris.proofmode Require Import tactics pviewshifts invariants.
From iris_logrel.F_mu_ref_conc Require Import rules_binary.
From iris.algebra Require Export upred_big_op.

Section bin_log_def.
  Context `{heapIG Σ, cfgSG Σ}.
  Notation D := (prodC valC valC -n> iPropG lang Σ).

  Definition bin_log_related (Γ : list type) (e e' : expr) (τ : type) := ∀ Δ vvs ρ,
    env_PersistentP Δ →
    heapI_ctx ∧ spec_ctx ρ ∧
    ⟦ Γ ⟧* Δ vvs ⊢ ⟦ τ ⟧ₑ Δ (e.[env_subst (vvs.*1)], e'.[env_subst (vvs.*2)]).
End bin_log_def.

Notation "Γ ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related Γ e e' τ) (at level 74, e, e', τ at next level).

Section fundamental.
  Context `{heapIG Σ, cfgSG Σ}.
  Notation D := (prodC valC valC -n> iPropG lang Σ).
  Implicit Types e : expr.
  Implicit Types Δ : listC D.
  Hint Resolve to_of_val.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) ident(w)
        constr(Hv) uconstr(Hp) :=
    iApply (@wp_bind _ _ _ [ctx]);
    iApply wp_wand_l; iSplitR;
    [|iApply Hp; rewrite ?fill_app; simpl; repeat iSplitR; trivial];
    let Htmp := iFresh in
    iIntros {v} Htmp; iDestruct Htmp as {w} Hv;
    rewrite fill_app; simpl.

  Local Ltac value_case := iApply wp_value; [cbn; rewrite ?to_of_val; trivial|].

  (* Put all quantifiers at the outer level *)
  Lemma bin_log_related_alt {Γ e e' τ} : Γ ⊨ e ≤log≤ e' : τ → ∀ Δ vvs ρ j K,
    env_PersistentP Δ →
    heapI_ctx ★ spec_ctx ρ ★ ⟦ Γ ⟧* Δ vvs ★ j ⤇ fill K (e'.[env_subst (vvs.*2)])
    ⊢ WP e.[env_subst (vvs.*1)] {{ v, ∃ v',
        j ⤇ fill K (# v') ★ interp τ Δ (v, v') }}.
  Proof.
    iIntros {Hlog Δ vvs ρ j K ?} "(#Hh & #Hs & HΓ & Hj)".
    iApply (Hlog with "[HΓ] *"); iFrame; eauto.
  Qed.

  Notation "' H" := (bin_log_related_alt H) (at level 8).

  Lemma bin_log_related_var Γ x τ :
    Γ !! x = Some τ → Γ ⊨ Var x ≤log≤ Var x : τ.
  Proof.
    iIntros {? Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    iDestruct (interp_env_Some_l with "HΓ") as { [v v'] } "[% ?]"; first done.
    rewrite /env_subst !list_lookup_fmap; simplify_option_eq. value_case; eauto.
  Qed.

  Lemma bin_log_related_unit Γ : Γ ⊨ Unit ≤log≤ Unit : TUnit.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    value_case. iExists UnitV; eauto.
  Qed.

  Lemma bin_log_related_nat Γ n : Γ ⊨ ♯ n ≤log≤ ♯ n : TNat.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    value_case. iExists (♯v _); eauto.
  Qed.

  Lemma bin_log_related_bool Γ b : Γ ⊨ ♭ b ≤log≤ ♭ b : TBool.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    value_case. iExists (♭v _); eauto.
  Qed.

  Lemma bin_log_related_pair Γ e1 e2 e1' e2' τ1 τ2
      (IHHtyped1 : Γ ⊨ e1 ≤log≤ e1' : τ1)
      (IHHtyped2 : Γ ⊨ e2 ≤log≤ e2' : τ2) :
    Γ ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : TProd τ1 τ2.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (PairLCtx e2.[env_subst _]) v v' "[Hv #Hiv]"
      ('IHHtyped1 _ _ _ j (K ++ [PairLCtx e2'.[env_subst _] ])).
    smart_wp_bind (PairRCtx v) w w' "[Hw #Hiw]"
      ('IHHtyped2 _ _ _ j (K ++ [PairRCtx v'])).
    value_case. iExists (PairV v' w'); iFrame "Hw".
    iExists (v, v'), (w, w'); simpl; repeat iSplit; trivial.
  Qed.

  Lemma bin_log_related_fst Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TProd τ1 τ2) :
    Γ ⊨ Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (FstCtx) v v' "[Hv #Hiv]" ('IHHtyped _ _ _ j (K ++ [FstCtx])); cbn.
    iDestruct "Hiv" as { [w1 w1'] [w2 w2'] } "#[% [Hw1 Hw2]]"; simplify_eq.
    iPvs (step_fst _ _ j K (# w1') w1' (# w2') w2' with "* [-]") as "Hw"; eauto.
    iApply wp_fst; eauto.
  Qed.

  Lemma bin_log_related_snd Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TProd τ1 τ2) :
    Γ ⊨ Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (SndCtx) v v' "[Hv #Hiv]" ('IHHtyped _ _ _ j (K ++ [SndCtx])); cbn.
    iDestruct "Hiv" as { [w1 w1'] [w2 w2'] } "#[% [Hw1 Hw2]]"; simplify_eq.
    iPvs (step_snd _ _ j K (# w1') w1' (# w2') w2' with "* [-]") as "Hw"; eauto.
    iApply wp_snd; eauto.
  Qed.

  Lemma bin_log_related_injl Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τ1) :
    Γ ⊨ InjL e ≤log≤ InjL e' : (TSum τ1 τ2).
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (InjLCtx) v v' "[Hv #Hiv]"
      ('IHHtyped _ _ _ j (K ++ [InjLCtx])); cbn.
    value_case. iExists (InjLV v'); iFrame "Hv".
    iLeft; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_injr Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τ2) :
    Γ ⊨ InjR e ≤log≤ InjR e' : TSum τ1 τ2.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (InjRCtx) v v' "[Hv #Hiv]"
      ('IHHtyped _ _ _ j (K ++ [InjRCtx])); cbn.
    value_case. iExists (InjRV v'); iFrame "Hv".
    iRight; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_case Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3
      (Hclosed2 : ∀ f, e1.[iter (S (length Γ)) up f] = e1)
      (Hclosed3 : ∀ f, e2.[iter (S (length Γ)) up f] = e2)
      (Hclosed2' : ∀ f, e1'.[iter (S (length Γ)) up f] = e1')
      (Hclosed3' : ∀ f, e2'.[iter (S (length Γ)) up f] = e2')
      (IHHtyped1 : Γ ⊨ e0 ≤log≤ e0' : TSum τ1 τ2)
      (IHHtyped2 : τ1 :: Γ ⊨ e1 ≤log≤ e1' : τ3)
      (IHHtyped3 : τ2 :: Γ ⊨ e2 ≤log≤ e2' : τ3) :
    Γ ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    smart_wp_bind (CaseCtx _ _) v v' "[Hv #Hiv]"
      ('IHHtyped1 _ _ _ j (K ++ [CaseCtx _ _])); cbn.
    iDestruct "Hiv" as "[Hiv|Hiv]".
    - iDestruct "Hiv" as { [w w'] } "[% Hw]"; simplify_eq.
      iPvs (step_case_inl _ _ j K (# w') w' with "* [-]") as "Hz"; eauto.
      iApply wp_case_inl; auto 1 using to_of_val. iNext.
      asimpl. erewrite !n_closed_subst_head_simpl by (rewrite ?fmap_length; eauto).
      iApply ('IHHtyped2 _ ((w,w') :: vvs)); repeat iSplit; eauto.
      iApply interp_env_cons; auto.
    - iDestruct "Hiv" as { [w w'] } "[% Hw]"; simplify_eq.
      iPvs (step_case_inr _ _ j K (# w') w' with "* [-]") as "Hz"; eauto.
      iApply wp_case_inr; auto 1 using to_of_val. iNext.
      asimpl. erewrite !n_closed_subst_head_simpl by (rewrite ?fmap_length; eauto).
      iApply ('IHHtyped3 _ ((w,w') :: vvs)); repeat iSplit; eauto.
      iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_if Γ e0 e1 e2 e0' e1' e2' τ
      (IHHtyped1 : Γ ⊨ e0 ≤log≤ e0' : TBool)
      (IHHtyped2 : Γ ⊨ e1 ≤log≤ e1' : τ)
      (IHHtyped3 : Γ ⊨ e2 ≤log≤ e2' : τ) :
    Γ ⊨ If e0 e1 e2 ≤log≤ If e0' e1' e2' : τ.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (IfCtx _ _) v v' "[Hv #Hiv]"
      ('IHHtyped1 _ _ _ j (K ++ [IfCtx _ _])); cbn.
    iDestruct "Hiv" as { [] } "[% %]"; simplify_eq/=.
    - iPvs (step_if_true _ _ j K with "* [-]") as "Hz"; eauto.
      iApply wp_if_true. iNext. iApply 'IHHtyped2; eauto.
    - iPvs (step_if_false _ _ j K with "* [-]") as "Hz"; eauto.
      iApply wp_if_false. iNext. iApply 'IHHtyped3; eauto.
  Qed.

  Lemma bin_log_related_nat_binop Γ op e1 e2 e1' e2'
      (IHHtyped1 : Γ ⊨ e1 ≤log≤ e1' : TNat)
      (IHHtyped2 : Γ ⊨ e2 ≤log≤ e2' : TNat) :
    Γ ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : binop_res_type op.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (BinOpLCtx _ _) v v' "[Hv #Hiv]"
                  ('IHHtyped1 _ _ _ j (K ++ [BinOpLCtx _ _])); cbn.
    smart_wp_bind (BinOpRCtx _ _) w w' "[Hw #Hiw]"
                  ('IHHtyped2 _ _ _ j (K ++ [BinOpRCtx _ _])); cbn.
    iDestruct "Hiv" as {n} "[% %]"; simplify_eq/=.
    iDestruct "Hiw" as {n'} "[% %]"; simplify_eq/=.
    iPvs (step_nat_binop _ _ j K with "* [-]") as "Hz"; eauto.
    iApply wp_nat_binop. iNext. iPvsIntro. iExists _; iSplitL; eauto.
    destruct op; simpl; try destruct eq_nat_dec; try destruct le_dec;
      try destruct lt_dec; eauto.
  Qed.

  Lemma bin_log_related_rec Γ (e e' : expr) τ1 τ2
      (Hclosed : ∀ f, e.[iter (S (S (length Γ))) up f] = e)
      (Hclosed' : ∀ f, e'.[iter (S (S (length Γ))) up f] = e')
      (IHHtyped : TArrow τ1 τ2 :: τ1 :: Γ ⊨ e ≤log≤ e' : τ2) :
    Γ ⊨ Rec e ≤log≤ Rec e' : TArrow τ1 τ2.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    value_case. iExists (RecV _). iIntros "{$Hj} !".
    iLöb as "IH". iIntros { [v v'] } "#Hiv". iIntros {j' K'} "Hj".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_rec; auto 1 using to_of_val. iNext.
    iPvs (step_rec _ _ j' K' _ (# v') v' with "* [-]") as "Hz"; eauto.
    asimpl. change (Rec ?e) with (# (RecV e)).
    erewrite !n_closed_subst_head_simpl_2 by (rewrite ?fmap_length; eauto).
    iApply ('IHHtyped _ ((_,_) :: (v,v') :: vvs)); repeat iSplit; eauto.
    iApply interp_env_cons; iSplit; [|iApply interp_env_cons]; auto.
  Qed.

  Lemma bin_log_related_app Γ e1 e2 e1' e2' τ1 τ2
      (IHHtyped1 : Γ ⊨ e1 ≤log≤ e1' : TArrow τ1 τ2)
      (IHHtyped2 : Γ ⊨ e2 ≤log≤ e2' : τ1) :
    Γ ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (AppLCtx (e2.[env_subst (vvs.*1)])) v v' "[Hv #Hiv]"
      ('IHHtyped1 _ _ _ j (K ++ [(AppLCtx (e2'.[env_subst (vvs.*2)]))])); cbn.
    smart_wp_bind (AppRCtx v) w w' "[Hw #Hiw]"
                  ('IHHtyped2 _ _ _ j (K ++ [AppRCtx v'])); cbn.
    iApply ("Hiv" $! (w, w') with "Hiw *"); simpl; eauto.
  Qed.

  Lemma bin_log_related_tlam Γ e e' τ
      (IHHtyped : (subst (ren (+1)) <$> Γ) ⊨ e ≤log≤ e' : τ) :
    Γ ⊨ TLam e ≤log≤ TLam e' : TForall τ.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    value_case. iExists (TLamV _).
    iIntros "{$Hj} /= !"; iIntros {τi} "%". iIntros {j' K'} "Hv /=".
    iApply wp_tlam; iNext.
    iPvs (step_tlam _ _ j' K' (e'.[env_subst (vvs.*2)]) with "* [-]") as "Hz"; eauto.
    iApply 'IHHtyped; repeat iSplit; eauto. by iApply interp_env_ren.
  Qed.

  Lemma bin_log_related_tapp Γ e e' τ τ'
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TForall τ) :
    Γ ⊨ TApp e ≤log≤ TApp e' : τ.[τ'/].
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (TAppCtx) v v' "[Hj #Hv]"
      ('IHHtyped _ _ _ j (K ++ [TAppCtx])); cbn.
    iApply wp_wand_r; iSplitL.
    { iSpecialize ("Hv" $! (interp τ' Δ) with "[#]"); [iPureIntro; apply _|].
      iApply "Hv"; eauto. }
    iIntros {w} "Hw". iDestruct "Hw" as {w'} "[Hw #Hiw]".
    iExists _; rewrite -interp_subst; eauto.
  Qed.

  Lemma bin_log_related_fold Γ e e' τ
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τ.[(TRec τ)/]) :
    Γ ⊨ Fold e ≤log≤ Fold e' : TRec τ.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    iApply (@wp_bind _ _ _ [FoldCtx]);
      iApply wp_wand_l; iSplitR;
        [|iApply ('IHHtyped _ _ _ j (K ++ [FoldCtx]));
          rewrite ?fill_app; simpl; repeat iSplitR; trivial].
    iIntros {v}; iDestruct 1 as {w} "[Hv #Hiv]"; rewrite fill_app.
    value_case. iExists (FoldV w); iFrame "Hv".
    rewrite fixpoint_unfold /= -interp_subst.
    iAlways; iExists (_, _); eauto.
  Qed.

  Lemma bin_log_related_unfold Γ e e' τ
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TRec τ) :
    Γ ⊨ Unfold e ≤log≤ Unfold e' : τ.[(TRec τ)/].
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    iApply (@wp_bind _ _ _ [UnfoldCtx]);
      iApply wp_wand_l; iSplitR;
        [|iApply ('IHHtyped _ _ _ j (K ++ [UnfoldCtx]));
          rewrite ?fill_app; simpl; repeat iSplitR; trivial].
    iIntros {v}. iDestruct 1 as {v'} "[Hw #Hiw]"; rewrite fill_app.
    rewrite /= fixpoint_unfold /=.
    change (fixpoint _) with (interp (TRec τ) Δ).
    iDestruct "Hiw" as { [w w'] } "#[% Hiz]"; simplify_eq/=.
    iPvs (step_Fold _ _ j K (# w') w' with "* [-]") as "Hz"; eauto.
    iApply wp_fold; cbn; auto.
    iNext; iPvsIntro; iExists _; iFrame "Hz". by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_fork Γ e e'
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TUnit) :
    Γ ⊨ Fork e ≤log≤ Fork e' : TUnit.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    iPvs (step_fork _ _ j K with "* [-]") as {j'} "[Hj Hj']"; eauto.
    iApply wp_fork; iNext; iSplitL "Hj".
    - iExists UnitV; eauto.
    - iApply wp_wand_l; iSplitR; [|iApply ('IHHtyped _ _ _ _ [])]; eauto.
  Qed.

  Lemma bin_log_related_alloc Γ e e' τ
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τ) :
    Γ ⊨ Alloc e ≤log≤ Alloc e' : Tref τ.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (AllocCtx) v v' "[Hv #Hiv]" ('IHHtyped _ _ _ j (K ++ [AllocCtx])).
    iPvs (step_alloc _ _ j K (# v') v' with "* [-]") as {l'} "[Hj Hl]"; eauto.
    iApply wp_alloc; auto.
    iIntros "{$Hh} >"; iIntros {l} "Hl'".
    iPvs (inv_alloc (logN .@ (l,l')) _ (∃ w : val * val,
      l ↦ᵢ w.1 ★ l' ↦ₛ w.2 ★ interp τ Δ w)%I with "[Hl Hl']") as "HN"; eauto.
    { iNext; iExists (v, v'); by iFrame. }
    iPvsIntro; iExists (LocV l'). iFrame "Hj". iExists (l, l'); eauto.
  Qed.

  Lemma bin_log_related_load Γ e e' τ
      (IHHtyped : Γ ⊨ e ≤log≤ e' : (Tref τ)) :
    Γ ⊨ Load e ≤log≤ Load e' : τ.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (LoadCtx) v v' "[Hv #Hiv]" ('IHHtyped _ _ _ j (K ++ [LoadCtx])).
    iDestruct "Hiv" as { [l l'] } "[% Hinv]"; simplify_eq/=.
    iInv (logN .@ (l,l')) as { [w w'] } "[Hw1 [Hw2 #Hw]]"; simpl.
    iTimeless "Hw2".
    iPvs (step_load _ _ j K l' 1 w' with "[Hv Hw2]") as "[Hv Hw2]";
      [unfold logN, specN; solve_ndisj|by iFrame|].
    iApply (wp_load _ _ 1); [|iFrame "Hh"]; trivial.
      unfold logN, heapN; solve_ndisj.
    iIntros "{$Hw1} > Hw1". iPvsIntro. iSplitL "Hw1 Hw2".
    - iNext; iExists (w,w'); by iFrame.
    - iExists w'; by iFrame.
  Qed.

  Lemma bin_log_related_store Γ e1 e2 e1' e2' τ
      (IHHtyped1 : Γ ⊨ e1 ≤log≤ e1' : (Tref τ))
      (IHHtyped2 : Γ ⊨ e2 ≤log≤ e2' : τ) :
    Γ ⊨ Store e1 e2 ≤log≤ Store e1' e2' : TUnit.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (StoreLCtx _) v v' "[Hv #Hiv]"
      ('IHHtyped1 _ _ _ j (K ++ [StoreLCtx _])).
    smart_wp_bind (StoreRCtx _) w w' "[Hw #Hiw]"
      ('IHHtyped2 _ _ _ j (K ++ [StoreRCtx _])).
    iDestruct "Hiv" as { [l l'] } "[% Hinv]"; simplify_eq/=.
    iInv (logN .@ (l,l')) as { [v v'] } "[Hv1 [Hv2 #Hv]]".
    { eapply bool_decide_spec; eauto using to_of_val. }
    iTimeless "Hv2".
    iPvs (step_store _ _ j K l' v' (# w') w' with "[Hw Hv2]")
      as "[Hw Hv2]"; [eauto|unfold logN, specN; solve_ndisj|by iFrame|].
    iApply wp_store; auto using to_of_val. unfold logN, heapN; solve_ndisj.
    iIntros "{$Hh $Hv1} > Hv1". iPvsIntro. iSplitL "Hv1 Hv2".
    - iNext; iExists (w, w'); by iFrame.
    - iExists UnitV; iFrame; auto.
  Qed.

  Lemma bin_log_related_CAS Γ e1 e2 e3 e1' e2' e3' τ
      (HEqτ : EqType τ)
      (IHHtyped1 : Γ ⊨ e1 ≤log≤ e1' : Tref τ)
      (IHHtyped2 : Γ ⊨ e2 ≤log≤ e2' : τ)
      (IHHtyped3 : Γ ⊨ e3 ≤log≤ e3' : τ) :
    Γ ⊨ CAS e1 e2 e3 ≤log≤ CAS e1' e2' e3' : TBool.
  Proof.
    iIntros {Δ vvs ρ ?} "#(Hh & Hs & HΓ)"; iIntros {j K} "Hj /=".
    smart_wp_bind (CasLCtx _ _) v v' "[Hv #Hiv]"
      ('IHHtyped1 _ _ _ j (K ++ [CasLCtx _ _])).
    smart_wp_bind (CasMCtx _ _) w w' "[Hw #Hiw]"
      ('IHHtyped2 _ _ _  j (K ++ [CasMCtx _ _])).
    smart_wp_bind (CasRCtx _ _) u u' "[Hu #Hiu]"
      ('IHHtyped3 _ _ _  j (K ++ [CasRCtx _ _])).
    iDestruct "Hiv" as { [l l'] } "[% Hinv]"; simplify_eq/=.
    iInv (logN .@ (l,l')) as { [v v'] } "[Hv1 [Hv2 #Hv]]".
    { eapply bool_decide_spec; eauto 10 using to_of_val. }
    iTimeless "Hv2".
    destruct (decide (v = w)) as [|Hneq]; subst.
    - iPvs (step_cas_suc _ _ j K l' (# w') w' v' (# u') u'
            with "[Hu Hv2]") as "[Hw Hv2]"; simpl; eauto;
        first (unfold logN, specN; solve_ndisj).
      { iIntros "{$Hs $Hu $Hv2} >".
        rewrite ?interp_EqType_agree; trivial. by iSimplifyEq. }
      iApply wp_cas_suc; eauto using to_of_val;
        first (unfold logN, heapN; solve_ndisj).
      iIntros "{$Hh $Hv1} > Hv1". iPvsIntro. iSplitL "Hv1 Hv2".
      + iNext; iExists (_, _); by iFrame.
      + iExists (♭v true); iFrame; eauto.
    - iPvs (step_cas_fail _ _ j K l' 1 v' (# w') w' (# u') u'
            with "[Hu Hv2]") as "[Hw Hv2]"; simpl; eauto;
        first (unfold logN, specN; solve_ndisj).
      { iIntros "{$Hs $Hu $Hv2} >".
        rewrite ?interp_EqType_agree; trivial. by iSimplifyEq. }
      iApply wp_cas_fail; eauto using to_of_val;
        first (unfold logN, heapN; solve_ndisj).
      iIntros "{$Hh $Hv1} > Hv1". iPvsIntro. iSplitL "Hv1 Hv2".
      + iNext; iExists (_, _); by iFrame.
      + iExists (♭v false); eauto.
  Qed.

  Theorem binary_fundamental Γ e τ :
    Γ ⊢ₜ e : τ → Γ ⊨ e ≤log≤ e : τ.
  Proof.
    induction 1.
    - by apply bin_log_related_var.
    - by apply bin_log_related_unit.
    - by apply bin_log_related_nat.
    - by apply bin_log_related_bool.
    - apply bin_log_related_nat_binop; eauto.
    - apply bin_log_related_pair; eauto.
    - eapply bin_log_related_fst; eauto.
    - eapply bin_log_related_snd; eauto.
    - eapply bin_log_related_injl; eauto.
    - eapply bin_log_related_injr; eauto.
    - eapply bin_log_related_case; eauto;
        match goal with H : _ |- _ => eapply (typed_n_closed _ _ _ H) end.
    - eapply bin_log_related_if; eauto.
    - eapply bin_log_related_rec; eauto;
        match goal with H : _ |- _ => eapply (typed_n_closed _ _ _ H) end.
    - eapply bin_log_related_app; eauto.
    - eapply bin_log_related_tlam; eauto with typeclass_instances.
    - eapply bin_log_related_tapp; eauto.
    - eapply bin_log_related_fold; eauto.
    - eapply bin_log_related_unfold; eauto.
    - eapply bin_log_related_fork; eauto.
    - eapply bin_log_related_alloc; eauto.
    - eapply bin_log_related_load; eauto.
    - eapply bin_log_related_store; eauto.
    - eapply bin_log_related_CAS; eauto.
  Qed.
End fundamental.
