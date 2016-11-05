From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.algebra Require Import frac dec_agree gmap.
From iris.base_logic Require Import big_op auth.
From iris_logrel.F_mu_ref_conc Require Export lang.
From iris.proofmode Require Import tactics.
Import uPred.

Definition heapN : namespace := nroot .@ "heap".
Definition heapUR : ucmraT := gmapUR loc (prodR fracR (dec_agreeR val)).

(** The CMRA for the heap of the implementation. This is linked to the
    physical heap. *)
Class heapIG Σ := HeapIG {
  heapI_irisG :> irisG lang Σ;
  heapI_inG :> authG Σ heapUR;
  heapI_name : gname
}.

Definition to_heap : state → heapUR := fmap (λ v, (1%Qp, DecAgree v)).

Section definitionsI.
  Context `{heapIG Σ}.

  Definition heapI_mapsto_def (l : loc) (q : Qp) (v: val) : iProp Σ :=
    auth_own heapI_name ({[ l := (q, DecAgree v) ]}).
  Definition heapI_mapsto_aux : { x | x = @heapI_mapsto_def }. by eexists. Qed.
  Definition heapI_mapsto := proj1_sig heapI_mapsto_aux.
  Definition heapI_mapsto_eq : @heapI_mapsto = @heapI_mapsto_def :=
    proj2_sig heapI_mapsto_aux.

  Definition heapI_ctx : iProp Σ := auth_ctx heapI_name heapN to_heap ownP.

  Global Instance heapI_mapsto_timeless l q v : TimelessP (heapI_mapsto l q v).
  Proof. rewrite heapI_mapsto_eq /heapI_mapsto_def. apply _. Qed.
  Global Instance heapI_ctx_persistent : PersistentP heapI_ctx.
  Proof. apply _. Qed.
End definitionsI.
Typeclasses Opaque heapI_ctx heapI_mapsto.

Notation "l ↦ᵢ{ q } v" := (heapI_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦ᵢ{ q }  v") : uPred_scope.
Notation "l ↦ᵢ v" := (heapI_mapsto l 1 v) (at level 20) : uPred_scope.

Section lang_rules.
  Context `{heapIG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types h g : heapUR.

  Ltac inv_head_step :=
    repeat match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : head_step ?e _ _ _ _ |- _ =>
       try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
       and can thus better be avoided. *)
       inversion H; subst; clear H
    end.

  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl.

  Local Hint Constructors head_step.
  Local Hint Resolve alloc_fresh.
  Local Hint Resolve to_of_val.

  (** Conversion to heaps and back *)
  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.
  Lemma heap_singleton_included σ l q v :
    {[l := (q, DecAgree v)]} ≼ to_heap σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included=> -[[q' av] [/leibniz_equiv_iff Hl Hqv]].
    move: Hl. rewrite /to_heap lookup_fmap fmap_Some=> -[v' [Hl [??]]]; subst.
    by move: Hqv=> /Some_pair_included_total_2 [_ /DecAgree_included ->].
  Qed.
  Lemma heap_singleton_included' σ l q v :
    {[l := (q, DecAgree v)]} ≼ to_heap σ → to_heap σ !! l = Some (1%Qp,DecAgree v).
  Proof.
    intros Hl%heap_singleton_included. by rewrite /to_heap lookup_fmap Hl.
  Qed.
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=(1%Qp, DecAgree v)]> (to_heap σ).
  Proof. by rewrite /to_heap -fmap_insert. Qed.

  (** General properties of mapsto *)
  Lemma heap_mapsto_op_eq l q1 q2 v : l ↦ᵢ{q1} v ★ l ↦ᵢ{q2} v ⊣⊢ l ↦ᵢ{q1+q2} v.
  Proof.
    by rewrite heapI_mapsto_eq -auth_own_op op_singleton pair_op dec_agree_idemp.
  Qed.

  Lemma heap_mapsto_op l q1 q2 v1 v2 :
    l ↦ᵢ{q1} v1 ★ l ↦ᵢ{q2} v2 ⊣⊢ v1 = v2 ∧ l ↦ᵢ{q1+q2} v1.
  Proof.
    destruct (decide (v1 = v2)) as [->|].
    { by rewrite heap_mapsto_op_eq pure_equiv // left_id. }
    apply (anti_symm (⊢)); last by apply pure_elim_l.
    rewrite heapI_mapsto_eq -auth_own_op auth_own_valid discrete_valid.
    eapply pure_elim; [done|] =>  /=.
    rewrite op_singleton pair_op dec_agree_ne // singleton_valid. by intros [].
  Qed.

  Lemma heap_mapsto_op_split l q v : (l ↦ᵢ{q} v)%I ≡ (l ↦ᵢ{q/2} v ★ l ↦ᵢ{q/2} v)%I.
  Proof. by rewrite heap_mapsto_op_eq Qp_div_2. Qed.

  Lemma heap_mapsto_dup_invalid l v1 v2 : l ↦ᵢ v1 ★ l ↦ᵢ v2 ⊢ False.
  Proof.
    rewrite heap_mapsto_op heapI_mapsto_eq /heapI_mapsto_def auth_own_valid.
    iIntros "[_ Hv]". iDestruct "Hv" as %Hv.
    revert Hv; rewrite singleton_valid=> -[Hv ?]. by destruct Hv.
  Qed.

  (** Base axioms for core primitives of the language: Stateful reductions. *)
    Lemma wp_alloc_pst E σ v :
    {{{ ▷ ownP σ }}} Alloc (of_val v) @ E
    {{{ l, RET (LocV l); σ !! l = None ∧ ownP (<[l:=v]>σ) }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    iApply (wp_lift_atomic_head_step (Alloc (of_val v)) σ); eauto.
    iFrame "HP". iNext. iIntros (v2 σ2 ef) "[% HP]". inv_head_step.
    match goal with H: _ = of_val v2 |- _ => apply (inj of_val (LocV _)) in H end.
    subst v2. iSplit. iApply "HΦ"; by iSplit. by iApply big_sepL_nil.
  Qed.

  Lemma wp_load_pst E σ l v :
    σ !! l = Some v →
    {{{ ▷ ownP σ }}} Load (Loc l) @ E {{{ RET v; ownP σ }}}.
  Proof.
    intros ? Φ. apply (wp_lift_atomic_det_head_step' σ v σ); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_store_pst E σ l v v' :
    σ !! l = Some v' →
    {{{ ▷ ownP σ }}} Store (Loc l) (of_val v) @ E
    {{{ RET UnitV; ownP (<[l:=v]>σ) }}}.
  Proof.
    intros. apply (wp_lift_atomic_det_head_step' σ (UnitV) (<[l:=v]>σ)); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_cas_fail_pst E σ l v1 v2 v' :
    σ !! l = Some v' → v' ≠ v1 →
    {{{ ▷ ownP σ }}} CAS (Loc l) (of_val v1) (of_val v2) @ E
    {{{ RET (BoolV false); ownP σ }}}.
  Proof.
    intros. apply (wp_lift_atomic_det_head_step' σ (BoolV false) σ); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_cas_suc_pst E σ l v1 v2 :
    σ !! l = Some v1 →
    {{{ ▷ ownP σ }}} CAS (Loc l) (of_val v1) (of_val v2) @ E
    {{{ RET (BoolV true); ownP (<[l:=v2]>σ) }}}.
  Proof.
    intros. apply (wp_lift_atomic_det_head_step' σ (BoolV true)
      (<[l:=v2]>σ)); eauto.
    intros; inv_head_step; eauto.
  Qed.

   Lemma wp_alloc E e v :
    to_val e = Some v → nclose heapN ⊆ E →
    {{{ heapI_ctx }}} Alloc e @ E {{{ l, RET (LocV l); l ↦ᵢ v }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "#Hinv HΦ". rewrite /heapI_ctx.
    iMod (auth_empty heapI_name) as "Ha".
    iMod (auth_open with "[$Hinv $Ha]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_alloc_pst with "Hσ"). iNext. iIntros (l) "[% Hσ]".
    iMod ("Hcl" with "* [Hσ]") as "Ha".
    { iFrame. iPureIntro. rewrite to_heap_insert.
      eapply alloc_singleton_local_update; by auto using lookup_to_heap_None. }
    iApply "HΦ". by rewrite heapI_mapsto_eq /heapI_mapsto_def.
  Qed.

  Lemma wp_load E l q v :
    nclose heapN ⊆ E →
    {{{ heapI_ctx ★ ▷ l ↦ᵢ{q} v }}} Load (Loc l) @ E {{{ RET v; l ↦ᵢ{q} v }}}.
  Proof.
    iIntros (? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heapI_ctx heapI_mapsto_eq /heapI_mapsto_def.
    iMod (auth_open with "[$Hinv $Hl]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_load_pst _ σ with "Hσ"); first eauto using heap_singleton_included.
    iNext; iIntros "Hσ".
    iMod ("Hcl" with "* [Hσ]") as "Ha"; first eauto. by iApply "HΦ".
  Qed.

  Lemma wp_store E l v' e v :
    to_val e = Some v → nclose heapN ⊆ E →
    {{{ heapI_ctx ★ ▷ l ↦ᵢ v' }}} Store (Loc l) e @ E
    {{{ RET UnitV; l ↦ᵢ v }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heapI_ctx heapI_mapsto_eq /heapI_mapsto_def.
    iMod (auth_open with "[$Hinv $Hl]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_store_pst _ σ with "Hσ"); first eauto using heap_singleton_included.
    iNext; iIntros "Hσ". iMod ("Hcl" with "* [Hσ]") as "Ha".
    { iFrame. iPureIntro. rewrite to_heap_insert.
      eapply singleton_local_update, exclusive_local_update; last done.
      by eapply heap_singleton_included'. }
    by iApply "HΦ".
  Qed.

  Lemma wp_cas_fail E l q v' e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 → nclose heapN ⊆ E →
    {{{ heapI_ctx ★ ▷ l ↦ᵢ{q} v' }}} CAS (Loc l) e1 e2 @ E
    {{{ RET (BoolV false); l ↦ᵢ{q} v' }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ?? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heapI_ctx heapI_mapsto_eq /heapI_mapsto_def.
    iMod (auth_open with "[$Hinv $Hl]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_cas_fail_pst _ σ with "Hσ"); [eauto using heap_singleton_included|done|].
    iNext; iIntros "Hσ".
    iMod ("Hcl" with "* [Hσ]") as "Ha"; first eauto. by iApply "HΦ".
  Qed.

  Lemma wp_cas_suc E l e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose heapN ⊆ E →
    {{{ heapI_ctx ★ ▷ l ↦ᵢ v1 }}} CAS (Loc l) e1 e2 @ E
    {{{ RET (BoolV true); l ↦ᵢ v2 }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heapI_ctx heapI_mapsto_eq /heapI_mapsto_def.
    iMod (auth_open with "[$Hinv $Hl]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_cas_suc_pst _ σ with "Hσ"); first by eauto using heap_singleton_included.
    iNext. iIntros "Hσ". iMod ("Hcl" with "* [Hσ]") as "Ha".
    { iFrame. iPureIntro. rewrite to_heap_insert.
      eapply singleton_local_update, exclusive_local_update; last done.
      by eapply heap_singleton_included'. }
    by iApply "HΦ".
  Qed.

  (** Helper Lemmas for weakestpre. *)

  Lemma wp_bind {E e} K Φ :
    WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
  Proof. exact: wp_ectx_bind. Qed.

  Lemma wp_rec E e1 e2 v Φ :
    to_val e2 = Some v →
    ▷ WP e1.[(Rec e1), e2 /] @ E {{ Φ }} ⊢ WP App (Rec e1) e2 @ E {{ Φ }}.
  Proof.
    intros <-%of_to_val.
    rewrite -(wp_lift_pure_det_head_step' (App _ _) e1.[Rec e1,of_val v/]); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_tlam E e Φ : ▷ WP e @ E {{ Φ }} ⊢ WP TApp (TLam e) @ E {{ Φ }}.
  Proof.
    rewrite -(wp_lift_pure_det_head_step' (TApp _) e); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_fold E e v Φ :
    to_val e = Some v → ▷ (|={E}=> Φ v) ⊢ WP Unfold (Fold e) @ E {{ Φ }}.
  Proof.
    intros <-%of_to_val.
    rewrite -(wp_lift_pure_det_head_step' (Unfold _) (of_val v))
      -?wp_value_fupd; eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_fst E e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ▷ (|={E}=> Φ v1) ⊢ WP Fst (Pair e1 e2) @ E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_head_step' (Fst _) e1)
      -?wp_value_fupd; eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_snd E e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ▷ (|={E}=> Φ v2) ⊢ WP Snd (Pair e1 e2) @ E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_head_step' (Snd _) e2)
      -?wp_value_fupd; eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_case_inl E e0 v0 e1 e2 Φ :
    to_val e0 = Some v0 →
    ▷ WP e1.[e0/] @ E {{ Φ }} ⊢ WP Case (InjL e0) e1 e2 @ E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_head_step' (Case _ _ _) (e1.[e0/])); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_case_inr E e0 v0 e1 e2 Φ :
    to_val e0 = Some v0 →
    ▷ WP e2.[e0/] @ E {{ Φ }} ⊢ WP Case (InjR e0) e1 e2 @ E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_head_step' (Case _ _ _) (e2.[e0/])); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_fork E e Φ :
    ▷ (|={E}=> Φ UnitV) ★ ▷ WP e {{ _, True }} ⊢ WP Fork e @ E {{ Φ }}.
  Proof.
  rewrite -(wp_lift_pure_det_head_step (Fork e) Unit [e]) //=; eauto.
  - by rewrite later_sep -(wp_value_fupd _ _ Unit) // big_sepL_singleton.
  - intros; inv_head_step; eauto.
  Qed.

  Lemma wp_if_true E e1 e2 Φ :
    ▷ WP e1 @ E {{ Φ }} ⊢ WP If (#♭ true) e1 e2 @ E {{ Φ }}.
  Proof.
    rewrite -(wp_lift_pure_det_head_step' (If _ _ _) e1); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_if_false E e1 e2 Φ :
    ▷ WP e2 @ E {{ Φ }} ⊢ WP If (#♭ false) e1 e2 @ E {{ Φ }}.
  Proof.
    rewrite -(wp_lift_pure_det_head_step' (If _ _ _) e2); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_nat_binop E op a b Φ :
    ▷ (|={E}=> Φ (binop_eval op a b)) ⊢ WP BinOp op (#n a) (#n b) @ E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_head_step' (BinOp op _ _) (of_val _))
      -?wp_value_fupd'; eauto.
    intros; inv_head_step; eauto.
  Qed.
End lang_rules.
