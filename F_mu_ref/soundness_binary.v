From iris_logrel.F_mu_ref Require Export context_refinement.
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
  iMod (own_alloc (● (Excl' e', ∅)
    ⋅ ◯ ((Excl' e', ∅) : cfgUR))) as (γc) "[Hcfg1 Hcfg2]".
  { apply auth_valid_discrete_2. split=>//. }
  set (Hcfg := CFGSG _ (HeapG _ _ _ γh) _ γc).
  iMod (inv_alloc specN _ (spec_inv ([e'], ∅)) with "[Hcfg1]") as "#Hcfg".
  { iNext. iExists e', ∅. rewrite {2}/to_heap fin_maps.map_fmap_empty. auto. }
  rewrite -(empty_env_subst e).
  iApply wp_fupd; iApply wp_wand_r; iSplitL; [iApply (bin_log_related_alt
    (Hlog _) [] [] ([e'], ∅) [])|]; simpl.
  { rewrite /heap_ctx /spec_ctx /auth_ctx /tpool_mapsto /auth_own /=.
    rewrite empty_env_subst -interp_env_nil. by iFrame "Hh1 Hcfg Hcfg2". }
  iIntros (v1); iDestruct 1 as (v2) "[Hj #Hinterp]".
  iInv specN as ">Hinv" "Hclose". iDestruct "Hinv" as (e'' σ) "[Hown Hsteps]".
  iDestruct "Hsteps" as %Hsteps'.
  rewrite /tpool_mapsto /auth.auth_own /=.
  iDestruct (own_valid_2 with "[$Hown $Hj]") as %Hvalid.
  move: Hvalid=> /auth_valid_discrete_2
    [/prod_included [Hv2 _] _]. apply Excl_included, leibniz_equiv in Hv2. subst.
  iMod ("Hclose" with "[-]") as "_"; [iExists _, σ; auto|].
  iIntros "!> !%"; eauto.
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
