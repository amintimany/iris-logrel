From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.base_logic Require Export invariants big_op.
From iris.algebra Require Import frac dec_agree gmap.
From iris.base_logic.lib Require Import auth.
From iris_logrel.F_mu_ref Require Export lang.
From iris.proofmode Require Import tactics.
Import uPred.

Definition heapN : namespace := nroot .@ "heap".
Definition heapUR : ucmraT := gmapUR loc (prodR fracR (dec_agreeR val)).

(** The CMRA we need. *)
Class heapG Σ := HeapG {
  heap_irisG :> irisG lang Σ;
  heap_inG :> authG Σ heapUR;
  heap_name : gname
}.
(** The Functor we need. *)
Definition heapΣ : gFunctors := authΣ heapUR.

Definition to_heap : state → heapUR := fmap (λ v, (1%Qp, DecAgree v)).

Section definitions.
  Context `{heapG Σ}.

  Definition heap_mapsto_def (l : loc) (q : Qp) (v: val) : iProp Σ :=
    auth_own heap_name ({[ l := (q, DecAgree v) ]}).
  Definition heap_mapsto_aux : { x | x = @heap_mapsto_def }. by eexists. Qed.
  Definition heap_mapsto := proj1_sig heap_mapsto_aux.
  Definition heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def :=
    proj2_sig heap_mapsto_aux.

  Definition heap_ctx : iProp Σ := auth_ctx heap_name heapN to_heap ownP.
  Global Instance heap_ctx_always_stable : PersistentP heap_ctx.
  Proof. apply _. Qed.
  Global Instance heap_mapsto_timeless l q v : TimelessP (heap_mapsto l q v).
  Proof. rewrite heap_mapsto_eq /heap_mapsto_def. apply _. Qed.
End definitions.
Typeclasses Opaque heap_ctx heap_mapsto.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : uPred_scope.

Section lang_rules.
  Context `{heapG Σ}.
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
  Lemma heap_mapsto_op_eq l q1 q2 v : l ↦{q1} v ★ l ↦{q2} v ⊣⊢ l ↦{q1+q2} v.
  Proof.
    by rewrite heap_mapsto_eq -auth_own_op op_singleton pair_op dec_agree_idemp.
  Qed.

  Lemma heap_mapsto_op l q1 q2 v1 v2 :
    l ↦{q1} v1 ★ l ↦{q2} v2 ⊣⊢ v1 = v2 ∧ l ↦{q1+q2} v1.
  Proof.
    destruct (decide (v1 = v2)) as [->|].
    { by rewrite heap_mapsto_op_eq pure_equiv // left_id. }
    apply (anti_symm (⊢)); last by apply pure_elim_l.
    rewrite heap_mapsto_eq -auth_own_op auth_own_valid discrete_valid.
    eapply pure_elim; [done|] =>  /=.
    rewrite op_singleton pair_op dec_agree_ne // singleton_valid. by intros [].
  Qed.

  Lemma heap_mapsto_op_split l q v : (l ↦{q} v)%I ≡ (l ↦{q/2} v ★ l ↦{q/2} v)%I.
  Proof. by rewrite heap_mapsto_op_eq Qp_div_2. Qed.

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

  Lemma wp_alloc E e v :
    to_val e = Some v → nclose heapN ⊆ E →
    {{{ heap_ctx }}} Alloc e @ E {{{ l, RET (LocV l); l ↦ v }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "#Hinv HΦ". rewrite /heap_ctx.
    iMod (auth_empty heap_name) as "Ha".
    iMod (auth_open with "[$Hinv $Ha]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_alloc_pst with "Hσ"). iNext. iIntros (l) "[% Hσ]".
    iMod ("Hcl" with "* [Hσ]") as "Ha".
    { iFrame. iPureIntro. rewrite to_heap_insert.
      eapply alloc_singleton_local_update; by auto using lookup_to_heap_None. }
    iApply "HΦ". by rewrite heap_mapsto_eq /heap_mapsto_def.
  Qed.

  Lemma wp_load E l q v :
    nclose heapN ⊆ E →
    {{{ heap_ctx ★ ▷ l ↦{q} v }}} Load (Loc l) @ E {{{ RET v; l ↦{q} v }}}.
  Proof.
    iIntros (? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iMod (auth_open with "[$Hinv $Hl]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_load_pst _ σ with "Hσ"); first eauto using heap_singleton_included.
    iNext; iIntros "Hσ".
    iMod ("Hcl" with "* [Hσ]") as "Ha"; first eauto. by iApply "HΦ".
  Qed.

  Lemma wp_store E l v' e v :
    to_val e = Some v → nclose heapN ⊆ E →
    {{{ heap_ctx ★ ▷ l ↦ v' }}} Store (Loc l) e @ E
    {{{ RET UnitV; l ↦ v }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iMod (auth_open with "[$Hinv $Hl]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_store_pst _ σ with "Hσ"); first eauto using heap_singleton_included.
    iNext; iIntros "Hσ". iMod ("Hcl" with "* [Hσ]") as "Ha".
    { iFrame. iPureIntro. rewrite to_heap_insert.
      eapply singleton_local_update, exclusive_local_update; last done.
      by eapply heap_singleton_included'. }
    by iApply "HΦ".
  Qed.

  (** Helper Lemmas for weakestpre. *)
  Lemma wp_bind {E e} K Φ :
    WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
  Proof. exact: wp_ectx_bind. Qed.

  Lemma wp_bind_ctxi {E e} Ki Φ :
    WP e @ E {{ v, WP fill_item Ki (of_val v) @ E {{ Φ }} }} ⊢
       WP fill_item Ki e @ E {{ Φ }}.
  Proof. exact: weakestpre.wp_bind. Qed.

  Lemma wp_lam E e1 e2 v Φ :
    to_val e2 = Some v → ▷ WP e1.[e2 /] @ E {{ Φ }} ⊢ WP App (Lam e1) e2 @ E {{ Φ }}.
  Proof.
    intros <-%of_to_val.
    rewrite -(wp_lift_pure_det_head_step' (App _ _) e1.[of_val v /]); eauto.
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
    intros. rewrite -(wp_lift_pure_det_head_step' (Fst _) e1) -?wp_value_fupd; eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_snd E e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ▷ (|={E}=> Φ v2) ⊢ WP Snd (Pair e1 e2) @ E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_head_step' (Snd _) e2) -?wp_value_fupd; eauto.
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
    intros ?. rewrite -(wp_lift_pure_det_head_step' (Case _ _ _) (e2.[e0/])); eauto.
    intros; inv_head_step; eauto.
  Qed.
End lang_rules.
