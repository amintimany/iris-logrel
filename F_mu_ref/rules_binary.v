From iris.program_logic Require Import lifting.
From iris.algebra Require Import frac dec_agree gmap list.
From iris.base_logic Require Import big_op auth.
From iris_logrel.F_mu_ref Require Export rules.
From iris.proofmode Require Import tactics.
Import uPred.

Definition specN := nroot .@ "spec".

(** The CMRA for the heap of the specification. *)
Definition cfgUR := prodUR (optionUR (exclR exprC)) heapUR.

(** The CMRA for the thread pool. *)
Class cfgSG Σ :=
  CFGSG { ctg_heapG :> heapG Σ; cfg_inG :> authG Σ cfgUR; cfg_name : gname }.

Section definitionsS.
  Context `{cfgSG Σ}.

  Definition heapS_mapsto (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own cfg_name (◯ (∅, {[ l := (q, DecAgree v) ]})).

  Definition tpool_mapsto (e: expr) : iProp Σ :=
    own cfg_name (◯ (Excl' e, ∅)).

  Definition spec_inv (ρ : cfg lang) : iProp Σ :=
    (∃ e σ, own cfg_name (● (Excl' e , to_heap σ)) ∗ ■ rtc step ρ ([e],σ))%I.
  Definition spec_ctx (ρ : cfg lang) : iProp Σ :=
    inv specN (spec_inv ρ).

  Global Instance heapS_mapsto_timeless l q v : TimelessP (heapS_mapsto l q v).
  Proof. apply _. Qed.
  Global Instance spec_ctx_persistent ρ : PersistentP (spec_ctx ρ).
  Proof. apply _. Qed.
End definitionsS.
Typeclasses Opaque heapS_mapsto tpool_mapsto.

Notation "l ↦ₛ{ q } v" := (heapS_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : uPred_scope.
Notation "l ↦ₛ v" := (heapS_mapsto l 1 v) (at level 20) : uPred_scope.
Notation "⤇ e" := (tpool_mapsto e) (at level 20) : uPred_scope.

Section cfg.
  Context `{cfgSG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types g : heapUR.
  Implicit Types e : expr.
  Implicit Types v : val.

  (** Conversion to tpools and back *)
  Lemma step_insert_no_fork K e σ e' σ' :
    head_step e σ e' σ' [] → step ([fill K e], σ) ([fill K e'], σ').
  Proof. intros Hst. eapply (step_atomic _ _ _ _ _ _ [] [] []); eauto.
         by apply: Ectx_step'.
  Qed.

  Lemma step_pure E ρ K e e' :
    (∀ σ, head_step e σ e' σ []) →
    nclose specN ⊆ E →
    spec_ctx ρ ∗ ⤇ fill K e ={E}=∗ ⤇ fill K e'.
  Proof.
    iIntros (??) "[#Hspec Hj]". rewrite /spec_ctx /tpool_mapsto.
    iInv specN as ">Hinv" "Hclose". iDestruct "Hinv" as (e2 σ) "[Hown %]".
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%Excl_included%leibniz_equiv _]%prod_included ?]%auth_valid_discrete_2.
    subst.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, option_local_update,
       (exclusive_local_update _ (Excl (fill K e'))). }
    iFrame "Hj". iApply "Hclose". iNext. iExists (fill K e'), σ.
    iFrame. iPureIntro. eapply rtc_r, step_insert_no_fork; eauto.
  Qed.

  Lemma step_alloc E ρ K e v:
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ρ ∗ ⤇ fill K (Alloc e) ={E}=∗ ∃ l, ⤇ fill K (Loc l) ∗ l ↦ₛ v.
  Proof.
    iIntros (??) "[#Hinv Hj]". rewrite /spec_ctx /tpool_mapsto.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e2 σ) "[Hown %]".
    destruct (exist_fresh (dom (gset positive) σ)) as [l Hl%not_elem_of_dom].
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%Excl_included%leibniz_equiv _]%prod_included ?]%auth_valid_discrete_2.
    subst.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, option_local_update,
       (exclusive_local_update _ (Excl (fill K (Loc l)))). }
    iMod (own_update with "Hown") as "[Hown Hl]".
    { eapply auth_update_alloc, prod_local_update_2,
        (alloc_singleton_local_update _ l (1%Qp,DecAgree v)); last done.
      by apply lookup_to_heap_None. }
    iExists l. rewrite /heapS_mapsto. iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (fill K (Loc l)), (<[l:=v]>σ).
    rewrite to_heap_insert; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_load E ρ K l q v:
    nclose specN ⊆ E →
    spec_ctx ρ ∗ ⤇ fill K (Load (Loc l)) ∗ l ↦ₛ{q} v
    ={E}=∗ ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e2 σ) "[Hown %]".
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%Excl_included%leibniz_equiv _]%prod_included ?]%auth_valid_discrete_2.
    subst.
    iDestruct (own_valid_2 _ with "Hown Hl")
      as %[[_ ?%heap_singleton_included]%prod_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, option_local_update,
        (exclusive_local_update _ (Excl (fill K (of_val v)))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (fill K (of_val v)), σ.
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_store E ρ K l v' e v:
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ρ ∗ ⤇ fill K (Store (Loc l) e) ∗ l ↦ₛ v'
    ={E}=∗ ⤇ fill K Unit ∗ l ↦ₛ v.
  Proof.
    iIntros (??) "(#Hinv & Hj & Hl)".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e2 σ) "[Hown %]".
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%Excl_included%leibniz_equiv _]%prod_included ?]%auth_valid_discrete_2.
    subst.
    iDestruct (own_valid_2 _ with "Hown Hl")
      as %[[_ Hl%heap_singleton_included]%prod_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, option_local_update,
        (exclusive_local_update _ (Excl (fill K Unit))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2, singleton_local_update,
        (exclusive_local_update _ (1%Qp, DecAgree v)); last done.
      by rewrite /to_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (fill K Unit), (<[l:=v]>σ).
    rewrite to_heap_insert; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_lam E ρ K e1 e2 v :
    to_val e2 = Some v → nclose specN ⊆ E →
    spec_ctx ρ ∗ ⤇ fill K (App (Lam e1) e2)
    ={E}=∗ ⤇ fill K (e1.[e2/]).
  Proof. intros ?; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_tlam E ρ K e :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ ⤇ fill K (TApp (TLam e)) ={E}=∗ ⤇ fill K e.
  Proof. apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_Fold E ρ K e v :
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ρ ∗ ⤇ fill K (Unfold (Fold e)) ={E}=∗ ⤇ fill K e.
  Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_fst E ρ K e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E →
    spec_ctx ρ ∗ ⤇ fill K (Fst (Pair e1 e2)) ={E}=∗ ⤇ fill K e1.
  Proof. intros H1 H2; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_snd E ρ K e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E →
    spec_ctx ρ ∗ ⤇ fill K (Snd (Pair e1 e2)) ={E}=∗ ⤇ fill K e2.
  Proof. intros H1 H2; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_case_inl E ρ K e0 v0 e1 e2 :
    to_val e0 = Some v0 → nclose specN ⊆ E →
    spec_ctx ρ ∗ ⤇ fill K (Case (InjL e0) e1 e2)
      ={E}=∗ ⤇ fill K (e1.[e0/]).
  Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_case_inr E ρ K e0 v0 e1 e2 :
    to_val e0 = Some v0 → nclose specN ⊆ E →
    spec_ctx ρ ∗ ⤇ fill K (Case (InjR e0) e1 e2)
      ={E}=∗ ⤇ fill K (e2.[e0/]).
  Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

End cfg.
