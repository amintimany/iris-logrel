From iris.program_logic Require Export weakestpre invariants.
From iris.program_logic Require Import ectx_lifting.
From iris.algebra Require Import upred_big_op frac dec_agree gmap.
From iris.program_logic Require Import ownership auth.
From iris_logrel.F_mu_ref Require Export lang.
From iris.proofmode Require Import tactics weakestpre invariants.
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
Definition of_heap : heapUR → state := omap (maybe DecAgree ∘ snd).

Section definitions.
  Context `{heapG Σ}.

  Definition heap_mapsto (l : loc) (q : Qp) (v: val) : iProp Σ :=
    auth_own heap_name {[ l := (q, DecAgree v) ]}.
  Definition heap_inv (h : heapUR) : iProp Σ :=
    ownP (of_heap h).
  Definition heap_ctx : iProp Σ := auth_ctx heap_name heapN heap_inv.

  Global Instance heap_inv_proper : Proper ((≡) ==> (≡)) heap_inv.
  Proof. solve_proper. Qed.
  Global Instance heap_ctx_always_stable : PersistentP heap_ctx.
  Proof. apply _. Qed.
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
  Global Instance of_heap_proper : Proper ((≡) ==> (=)) of_heap.
  Proof. solve_proper. Qed.
  Lemma from_to_heap σ : of_heap (to_heap σ) = σ.
  Proof.
    apply map_eq=>l. rewrite lookup_omap lookup_fmap. by case (σ !! l).
  Qed.
  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma of_heap_insert l v h :
    of_heap (<[l:=(1%Qp, DecAgree v)]> h) = <[l:=v]> (of_heap h).
  Proof. by rewrite /of_heap -(omap_insert _ _ _ (1%Qp, DecAgree v)). Qed.
  Lemma of_heap_singleton_op l q v h :
    ✓ ({[l := (q, DecAgree v)]} ⋅ h) →
    of_heap ({[l := (q, DecAgree v)]} ⋅ h) = <[l:=v]> (of_heap h).
  Proof.
    intros Hv. apply map_eq=> l'; destruct (decide (l' = l)) as [->|].
    - move: (Hv l). rewrite /of_heap lookup_insert
                            lookup_omap (lookup_op _ h) lookup_singleton.
      case _:(h !! l)=>[[q' [v'|]]|] //=; last by move=> [??].
      move=> [? /dec_agree_op_inv [->]]. by rewrite dec_agree_idemp.
    - rewrite /of_heap lookup_insert_ne // !lookup_omap.
      by rewrite (lookup_op _ h) lookup_singleton_ne // left_id_L.
  Qed.
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=(1%Qp, DecAgree v)]> (to_heap σ).
  Proof. by rewrite /to_heap -fmap_insert. Qed.
  Lemma of_heap_None h l : ✓ h → of_heap h !! l = None → h !! l = None.
  Proof.
    move=> /(_ l). rewrite /of_heap lookup_omap.
      by case: (h !! l)=> [[q [v|]]|] //=; destruct 1; auto.
  Qed.
  Lemma heap_store_valid l h v1 v2 :
    ✓ ({[l := (1%Qp, DecAgree v1)]} ⋅ h) →
    ✓ ({[l := (1%Qp, DecAgree v2)]} ⋅ h).
  Proof.
    intros Hv l'; move: (Hv l'). destruct (decide (l' = l)) as [->|].
    - rewrite !lookup_op !lookup_singleton.
      by case: (h !! l)=> [x|] // /Some_valid /exclusive_l.
    - by rewrite !lookup_op !lookup_singleton_ne.
  Qed.
  Hint Resolve heap_store_valid.

  Lemma of_empty_heap : of_heap ∅ = ∅.
  Proof. unfold of_heap; apply map_eq => i; rewrite !lookup_omap; f_equal. Qed.

  (** General properties of mapsto *)
  Lemma heap_mapsto_op_eq l q1 q2 v : l ↦{q1} v ★ l ↦{q2} v ⊣⊢ l ↦{q1+q2} v.
  Proof. by rewrite -auth_own_op op_singleton pair_op dec_agree_idemp. Qed.

  Lemma heap_mapsto_op l q1 q2 v1 v2 :
    l ↦{q1} v1 ★ l ↦{q2} v2 ⊣⊢ v1 = v2 ∧ l ↦{q1+q2} v1.
  Proof.
    destruct (decide (v1 = v2)) as [->|].
    { by rewrite heap_mapsto_op_eq pure_equiv // left_id. }
    rewrite -auth_own_op op_singleton pair_op dec_agree_ne //.
    apply (anti_symm (⊢)); last by apply pure_elim_l.
    rewrite auth_own_valid gmap_validI (forall_elim l) lookup_singleton.
    rewrite option_validI prod_validI !discrete_valid /=.
    by apply pure_elim_r.
  Qed.

  Lemma heap_mapsto_op_split l q v : (l ↦{q} v)%I ≡ (l ↦{q/2} v ★ l ↦{q/2} v)%I.
  Proof. by rewrite heap_mapsto_op_eq Qp_div_2. Qed.

  (** Base axioms for core primitives of the language: Stateful reductions. *)
  Lemma wp_alloc_pst E σ e v Φ :
    to_val e = Some v →
    ▷ ownP σ ★ ▷ (∀ l, σ !! l = None ∧ ownP (<[l:=v]>σ) ={E}=★ Φ (LocV l))
      ⊢ WP Alloc e @ E {{ Φ }}.
  Proof.
    iIntros (<-%of_to_val) "[HP HΦ]".
    iApply (wp_lift_atomic_head_step (Alloc (of_val v)) σ); eauto.
    iFrame "HP". iNext. iIntros (v2 σ2 ef) "[% HP]". inv_head_step.
    match goal with H: _ = of_val v2 |- _ => apply (inj of_val (LocV _)) in H end.
    subst v2. iSplit. iApply "HΦ"; by iSplit. by iApply big_sepL_nil.
  Qed.

  Lemma wp_load_pst E σ l v Φ :
    σ !! l = Some v →
    ▷ ownP σ ★ ▷ (ownP σ ={E}=★ Φ v) ⊢ WP Load (Loc l) @ E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_atomic_det_head_step' σ v σ); eauto 10.
    intros; inv_head_step; eauto 10.
  Qed.

  Lemma wp_store_pst E σ l e v v' Φ :
    to_val e = Some v → σ !! l = Some v' →
    ▷ ownP σ ★ ▷ (ownP (<[l:=v]>σ) ={E}=★ Φ UnitV) ⊢ WP Store (Loc l) e @ E {{ Φ }}.
  Proof.
    intros.
    rewrite-(wp_lift_atomic_det_head_step' σ UnitV (<[l:=v]>σ)); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_alloc E e v Φ :
    to_val e = Some v → nclose heapN ⊆ E →
    heap_ctx ★ ▷ (∀ l, l ↦ v ={E}=★ Φ (LocV l)) ⊢ WP Alloc e @ E {{ Φ }}.
  Proof.
    iIntros (<-%of_to_val ?) "[#Hinv HΦ]". rewrite /heap_ctx.
    iVs (auth_empty heap_name) as "Hh".
    iVs (auth_open with "[Hh]") as (h) "[Hv [Hh Hclose]]"; eauto.
    rewrite left_id /heap_inv. iDestruct "Hv" as %?.
    iApply wp_alloc_pst; eauto. iFrame "Hh". iNext.
    iIntros (l) "[% Hh] !==>".
    iVs ("Hclose" $! {[ l := (1%Qp, DecAgree v) ]} with "[Hh]").
    { rewrite -of_heap_insert -(insert_singleton_op h); last by apply of_heap_None.
      iFrame "Hh". iPureIntro.
      by apply alloc_unit_singleton_local_update; first apply of_heap_None. }
    iApply "HΦ". by rewrite /heap_mapsto.
  Qed.

  Lemma wp_load E l q v Φ :
    nclose heapN ⊆ E →
    heap_ctx ★ ▷ l ↦{q} v ★ ▷ (l ↦{q} v ={E}=★ Φ v)
    ⊢ WP Load (Loc l) @ E {{ Φ }}.
  Proof.
    iIntros (?) "[#Hinv [Hl HΦ]]". rewrite /heap_ctx /heap_mapsto.
    iVs (auth_open with "[Hl]") as (h) "[% [Hl Hclose]]"; eauto.
    rewrite /heap_inv.
    iApply (wp_load_pst _ (<[l:=v]>(of_heap h)));first by rewrite lookup_insert.
    rewrite of_heap_singleton_op //. iFrame "Hl".
    iIntros "!> Hown !==>". iVs ("Hclose" with "* [Hown]").
    { iSplit; first done. rewrite of_heap_singleton_op //. by iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma wp_store E l v' e v Φ :
    to_val e = Some v → nclose heapN ⊆ E →
    heap_ctx ★ ▷ l ↦ v' ★ ▷ (l ↦ v ={E}=★ Φ UnitV)
    ⊢ WP Store (Loc l) e @ E {{ Φ }}.
  Proof.
    iIntros (<-%of_to_val ?) "[#Hinv [Hl HΦ]]". rewrite /heap_ctx /heap_mapsto.
    iVs (auth_open with "[Hl]") as (h) "[% [Hl Hclose]]"; eauto.
    rewrite /heap_inv.
    iApply (wp_store_pst _ (<[l:=v']>(of_heap h))); rewrite ?lookup_insert //.
    rewrite insert_insert !of_heap_singleton_op; eauto. iFrame "Hl".
    iIntros "!> Hl !==>".
    iVs ("Hclose" $! {[l := (1%Qp, DecAgree v)]} with "[Hl]").
    { iSplit.
      - iPureIntro; by apply singleton_local_update, exclusive_local_update.
      - rewrite of_heap_singleton_op //; eauto. }
    by iApply "HΦ".
  Qed.

  (** Helper Lemmas for weakestpre. *)

  Lemma wp_bind {E e} K Φ :
    WP e @ E {{ v, WP fill K (# v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
  Proof. exact: wp_ectx_bind. Qed.

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
      -?wp_value_pvs; eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_fst E e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ▷ (|={E}=> Φ v1) ⊢ WP Fst (Pair e1 e2) @ E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_head_step' (Fst _) e1) -?wp_value_pvs; eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_snd E e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ▷ (|={E}=> Φ v2) ⊢ WP Snd (Pair e1 e2) @ E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_head_step' (Snd _) e2) -?wp_value_pvs; eauto.
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
