From iris.program_logic Require Import lifting.
From iris.algebra Require Import frac dec_agree gmap list.
From iris.base_logic Require Import big_op auth.
From iris_logrel.F_mu_ref_conc Require Export rules.
From iris.proofmode Require Import tactics.
Import uPred.

Definition specN := nroot .@ "spec".

(** The CMRA for the heap of the specification. *)
Definition tpoolUR : ucmraT := gmapUR nat (exclR exprC).
Definition cfgUR := prodUR tpoolUR heapUR.

Fixpoint to_tpool_go (i : nat) (tp : list expr) : tpoolUR :=
  match tp with
  | [] => ∅
  | e :: tp => <[i:=Excl e]>(to_tpool_go (S i) tp)
  end.
Definition to_tpool : list expr → tpoolUR := to_tpool_go 0.

(** The CMRA for the thread pool. *)
Class cfgSG Σ :=
  CFGSG { ctg_heapG :> heapIG Σ; cfg_inG :> authG Σ cfgUR; cfg_name : gname }.

Section definitionsS.
  Context `{cfgSG Σ}.

  Definition heapS_mapsto (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own cfg_name (◯ (∅, {[ l := (q, DecAgree v) ]})).

  Definition tpool_mapsto (j : nat) (e: expr) : iProp Σ :=
    own cfg_name (◯ ({[ j := Excl e ]}, ∅)).

  Definition spec_inv (ρ : cfg lang) : iProp Σ :=
    (∃ tp σ, own cfg_name (● (to_tpool tp, to_heap σ)) ∗ ■ rtc step ρ (tp,σ))%I.
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
Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : uPred_scope.

Section cfg.
  Context `{cfgSG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types g : heapUR.
  Implicit Types e : expr.
  Implicit Types v : val.

  (** Conversion to tpools and back *)
  Lemma to_tpool_valid es : ✓ to_tpool es.
  Proof.
    rewrite /to_tpool. move: 0.
    induction es as [|e es]=> n //. by apply insert_valid.
  Qed.

  Lemma tpool_lookup tp j : to_tpool tp !! j = Excl <$> tp !! j.
  Proof.
    cut (∀ i, to_tpool_go i tp !! (i + j) = Excl <$> tp !! j).
    { intros help. apply (help 0). }
    revert j. induction tp as [|e tp IH]=> //= -[|j] i /=.
    - by rewrite Nat.add_0_r lookup_insert.
    - by rewrite -Nat.add_succ_comm lookup_insert_ne; last lia.
  Qed.
  Lemma tpool_lookup_Some tp j e : to_tpool tp !! j = Excl' e → tp !! j = Some e.
  Proof. rewrite tpool_lookup fmap_Some. naive_solver. Qed.
  Hint Resolve tpool_lookup_Some.

  Lemma to_tpool_insert tp j e :
    j < length tp →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    intros. apply: map_eq=> i. destruct (decide (i = j)) as [->|].
    - by rewrite tpool_lookup lookup_insert list_lookup_insert.
    - rewrite tpool_lookup lookup_insert_ne // list_lookup_insert_ne //.
      by rewrite tpool_lookup.
  Qed.
  Lemma to_tpool_insert' tp j e :
    is_Some (to_tpool tp !! j) →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    rewrite tpool_lookup fmap_is_Some lookup_lt_is_Some. apply to_tpool_insert.
  Qed.

  Lemma to_tpool_snoc tp e :
    to_tpool (tp ++ [e]) = <[length tp:=Excl e]>(to_tpool tp).
  Proof.
    intros. apply: map_eq=> i.
    destruct (lt_eq_lt_dec i (length tp)) as [[?| ->]|?].
    - rewrite lookup_insert_ne; last lia. by rewrite !tpool_lookup lookup_app_l.
    - by rewrite lookup_insert tpool_lookup lookup_app_r // Nat.sub_diag.
    - rewrite lookup_insert_ne; last lia.
      rewrite !tpool_lookup ?lookup_ge_None_2 ?app_length //=;
         change (cofe_car exprC) with expr; lia.
  Qed.

  Lemma tpool_singleton_included tp j e :
    {[j := Excl e]} ≼ to_tpool tp → tp !! j = Some e.
  Proof.
    move=> /singleton_included [ex [/leibniz_equiv_iff]].
    rewrite tpool_lookup fmap_Some=> [[e' [-> ->]] /Excl_included ?]. by f_equal.
  Qed.
  Lemma tpool_singleton_included' tp j e :
    {[j := Excl e]} ≼ to_tpool tp → to_tpool tp !! j = Excl' e.
  Proof. rewrite tpool_lookup. by move=> /tpool_singleton_included=> ->. Qed.

  Lemma step_insert K tp j e σ e' σ' efs :
    tp !! j = Some (fill K e) → head_step e σ e' σ' efs →
    step (tp, σ) (<[j:=fill K e']> tp ++ efs, σ').
  Proof.
    intros. rewrite -(take_drop_middle tp j (fill K e)) //.
    rewrite insert_app_r_alt take_length_le ?Nat.sub_diag /=;
      eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite -(assoc_L (++)) /=.
    eapply step_atomic; eauto. by apply: Ectx_step'.
  Qed.

  Lemma step_insert_no_fork K tp j e σ e' σ' :
    tp !! j = Some (fill K e) → head_step e σ e' σ' [] →
    step (tp, σ) (<[j:=fill K e']> tp, σ').
  Proof. rewrite -(right_id_L [] (++) (<[_:=_]>_)). by apply step_insert. Qed.

  Lemma step_pure E ρ j K e e' :
    (∀ σ, head_step e σ e' σ []) →
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K e ={E}=∗ j ⤇ fill K e'.
  Proof.
    iIntros (??) "[#Hspec Hj]". rewrite /spec_ctx /tpool_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K e'))). }
    iFrame "Hj". iApply "Hclose". iNext. iExists (<[j:=fill K e']> tp), σ.
    rewrite to_tpool_insert'; last eauto.
    iFrame. iPureIntro. eapply rtc_r, step_insert_no_fork; eauto.
  Qed.

  Lemma step_alloc E ρ j K e v:
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (Alloc e) ={E}=∗ ∃ l, j ⤇ fill K (Loc l) ∗ l ↦ₛ v.
  Proof.
    iIntros (??) "[#Hinv Hj]". rewrite /spec_ctx /tpool_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    destruct (exist_fresh (dom (gset positive) σ)) as [l Hl%not_elem_of_dom].
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K (Loc l)))). }
    iMod (own_update with "Hown") as "[Hown Hl]".
    { eapply auth_update_alloc, prod_local_update_2,
        (alloc_singleton_local_update _ l (1%Qp,DecAgree v)); last done.
      by apply lookup_to_heap_None. }
    iExists l. rewrite /heapS_mapsto. iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (Loc l)]> tp), (<[l:=v]>σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_load E ρ j K l q v:
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (Load (Loc l)) ∗ l ↦ₛ{q} v
    ={E}=∗ j ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_valid_discrete_2.
    iDestruct (own_valid_2 _ with "Hown Hl")
      as %[[_ ?%heap_singleton_included]%prod_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (of_val v)))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (of_val v)]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_store E ρ j K l v' e v:
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (Store (Loc l) e) ∗ l ↦ₛ v'
    ={E}=∗ j ⤇ fill K Unit ∗ l ↦ₛ v.
  Proof.
    iIntros (??) "(#Hinv & Hj & Hl)".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included _]%auth_valid_discrete_2.
    iDestruct (own_valid_2 _ with "Hown Hl")
      as %[[_ Hl%heap_singleton_included]%prod_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K Unit))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2, singleton_local_update,
        (exclusive_local_update _ (1%Qp, DecAgree v)); last done.
      by rewrite /to_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K Unit]> tp), (<[l:=v]>σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_cas_fail E ρ j K l q v' e1 v1 e2 v2:
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E → v' ≠ v1 →
    spec_ctx ρ ∗ j ⤇ fill K (CAS (Loc l) e1 e2) ∗ l ↦ₛ{q} v'
    ={E}=∗ j ⤇ fill K (#♭ false) ∗ l ↦ₛ{q} v'.
  Proof.
    iIntros (????) "(#Hinv & Hj & Hl)".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_valid_discrete_2.
    iDestruct (own_valid_2 _ with "Hown Hl")
      as %[[_ ?%heap_singleton_included]%prod_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (#♭ false)))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (#♭ false)]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_cas_suc E ρ j K l e1 v1 v1' e2 v2:
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E → v1 = v1' →
    spec_ctx ρ ∗ j ⤇ fill K (CAS (Loc l) e1 e2) ∗ l ↦ₛ v1'
    ={E}=∗ j ⤇ fill K (#♭ true) ∗ l ↦ₛ v2.
  Proof.
    iIntros (????) "(#Hinv & Hj & Hl)"; subst.
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included _]%auth_valid_discrete_2.
    iDestruct (own_valid_2 _ with "Hown Hl")
      as %[[_ Hl%heap_singleton_included]%prod_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (#♭ true)))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2, singleton_local_update,
        (exclusive_local_update _ (1%Qp, DecAgree v2)); last done.
      by rewrite /to_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (#♭ true)]> tp), (<[l:=v2]>σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_rec E ρ j K e1 e2 v :
    to_val e2 = Some v → nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (App (Rec e1) e2)
    ={E}=∗ j ⤇ fill K (e1.[Rec e1,e2/]).
  Proof. intros ?; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_tlam E ρ j K e :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (TApp (TLam e)) ={E}=∗ j ⤇ fill K e.
  Proof. apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_Fold E ρ j K e v :
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (Unfold (Fold e)) ={E}=∗ j ⤇ fill K e.
  Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_fst E ρ j K e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (Fst (Pair e1 e2)) ={E}=∗ j ⤇ fill K e1.
  Proof. intros H1 H2; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_snd E ρ j K e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (Snd (Pair e1 e2)) ={E}=∗ j ⤇ fill K e2.
  Proof. intros H1 H2; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_case_inl E ρ j K e0 v0 e1 e2 :
    to_val e0 = Some v0 → nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (Case (InjL e0) e1 e2)
      ={E}=∗ j ⤇ fill K (e1.[e0/]).
  Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_case_inr E ρ j K e0 v0 e1 e2 :
    to_val e0 = Some v0 → nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (Case (InjR e0) e1 e2)
      ={E}=∗ j ⤇ fill K (e2.[e0/]).
  Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_if_false E ρ j K e1 e2 :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (If (#♭ false) e1 e2) ={E}=∗ j ⤇ fill K e2.
  Proof. apply step_pure => σ; econstructor. Qed.

  Lemma step_if_true E ρ j K e1 e2 :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (If (#♭ true) e1 e2) ={E}=∗ j ⤇ fill K e1.
  Proof. apply step_pure => σ; econstructor. Qed.

  Lemma step_nat_binop E ρ j K op a b :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (BinOp op (#n a) (#n b))
      ={E}=∗ j ⤇ fill K (of_val (binop_eval op a b)).
  Proof. apply step_pure => σ; econstructor. Qed.

  Lemma step_fork E ρ j K e :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (Fork e) ={E}=∗ ∃ j', j ⤇ fill K Unit ∗ j' ⤇ e.
  Proof.
    iIntros (?) "[#Hspec Hj]". rewrite /spec_ctx /tpool_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_valid_discrete_2.
    assert (j < length tp) by eauto using lookup_lt_Some.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K Unit))). }
    iMod (own_update with "Hown") as "[Hown Hfork]".
    { eapply auth_update_alloc, prod_local_update_1,
        (alloc_singleton_local_update _ (length tp) (Excl e)); last done.
      rewrite lookup_insert_ne ?tpool_lookup; last omega.
      by rewrite lookup_ge_None_2. }
    iExists (length tp). iFrame "Hj Hfork". iApply "Hclose". iNext.
    iExists (<[j:=fill K Unit]> tp ++ [e]), σ.
    rewrite to_tpool_snoc insert_length to_tpool_insert //. iFrame. iPureIntro.
    eapply rtc_r, step_insert; eauto. econstructor; eauto.
  Qed.
End cfg.
