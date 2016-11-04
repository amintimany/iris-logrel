From iris_logrel.F_mu_ref_conc Require Export context_refinement.
From iris.algebra Require Import frac dec_agree.
From iris.base_logic Require Import big_op auth.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.

Lemma basic_soundness Σ `{irisPreG lang Σ, authG Σ heapUR, authG Σ cfgUR}
    e e' τ v thp hp :
  (∀ `{cfgSG Σ}, [] ⊨ e ≤log≤ e' : τ) →
  rtc step ([e], ∅) (of_val v :: thp, hp) →
  (∃ thp' hp' v', rtc step ([e'], ∅) (of_val v' :: thp', hp')).
Proof.
  intros Hlog Hsteps.
  cut (adequate e ∅ (λ _, ∃ thp' h v, rtc step ([e'], ∅) (of_val v :: thp', h))).
  { destruct 1; naive_solver. }
  eapply (wp_adequacy Σ); iIntros (?) "Hσ".
  iMod (auth_alloc to_heap ownP heapN _ ∅ with "[Hσ]")
    as (γh) "[#Hh1 Hh2]"; auto; first done.
  iMod (own_alloc (● (to_cfg ([e'], ∅) : cfgUR)
    ⋅ ◯ (({[ 0 := Excl' e' ]} : tpoolUR, ∅) : cfgUR))) as (γc) "[Hcfg1 Hcfg2]".
  { rewrite -auth_both_op auth_valid_discrete /= prod_included /= to_empty_heap.
    eauto using to_cfg_valid. }
  iMod (inv_alloc specN _ (∃ ρ', own γc (● ρ') ★ (■ ([e'], ∅) →⋆ of_cfg ρ'))%I
    with "[Hcfg1]") as "#Hcfg"; trivial.
  { iNext. iExists _. iIntros "{$Hcfg1} !%". rewrite from_to_cfg; constructor. }
  rewrite -(empty_env_subst e).
  iApply wp_fupd; iApply wp_wand_r; iSplitL; [iApply (bin_log_related_alt
    (Hlog (CFGSG _ (HeapIG _ _ _ γh) _ γc)) [] [] ([e'], ∅) 0 [])|]; simpl.
  { rewrite /heapI_ctx /spec_ctx /auth_ctx /tpool_mapsto /auth_own /=.
    rewrite empty_env_subst -interp_env_nil. by iFrame "Hh1 Hcfg Hcfg2". }
  iIntros (v1); iDestruct 1 as (v2) "[Hj #Hinterp]".
  iInv specN as (ρ) ">[Hown Hsteps]" "Hclose"; iDestruct "Hsteps" as %Hsteps'.
  rewrite /tpool_mapsto /auth.auth_own /=.
  iCombine "Hj" "Hown" as "Hown".
  iDestruct (own_valid with "Hown") as %[[[tp h] Hρ] [Htp ?]]%auth_valid_discrete.
  move: Hρ; rewrite /= right_id pair_op left_id leibniz_equiv_iff=> ?; simplify_eq/=.
  iMod ("Hclose" with "[-]").
  { iDestruct "Hown" as "[Ho1 Ho2]". rewrite /auth_inv; eauto. }
  iIntros "!> !%". exists (of_tpool tp), (of_heap h), v2.
  destruct tp as [|[[]|]]; by inversion_clear Htp.
Qed.

Lemma binary_soundness Σ `{irisPreG lang Σ, authG Σ heapUR, authG Σ cfgUR}
    Γ e e' τ :
  (∀ f, e.[upn (length Γ) f] = e) →
  (∀ f, e'.[upn (length Γ) f] = e') →
  (∀ `{cfgSG Σ}, Γ ⊨ e ≤log≤ e' : τ) →
  Γ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros He He' Hlog K thp σ v ?. eapply (basic_soundness Σ)=> ?.
  eapply (bin_log_related_under_typed_ctx _ _ _ _ []); eauto.
Qed.
