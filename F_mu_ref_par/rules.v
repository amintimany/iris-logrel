Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import F_mu_ref_par.lang.
From iris.program_logic Require Export lifting.
From iris.algebra Require Import upred_big_op frac dec_agree list.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Import weakestpre.
Require Import iris.proofmode.tactics iris.proofmode.invariants.
Import uPred.

Section lang_rules.
  Definition heapR : cmraT := gmapR loc (fracR (dec_agreeR val)).

  (** The CMRA for the heap of the implementation. This is linked to the
      physical heap. *)
  Class heapIG Σ :=
    HeapIG {
        heapI_inG :> authG lang Σ heapR;
        heapI_name : gname
      }.

  Definition to_heap : state → heapR := fmap (λ v, Frac 1 (DecAgree v)).
  Definition of_heap : heapR → state :=
    omap (mbind (maybe DecAgree ∘ snd) ∘ maybe2 Frac).

  Section definitionsI.
    Context `{iI : heapIG Σ}.

    Definition heapI_mapsto (l : loc) (q : Qp) (v: val) : iPropG lang Σ :=
      auth_own heapI_name {[ l := Frac q (DecAgree v) ]}.
    Definition heapI_inv (h : heapR) : iPropG lang Σ :=
      ownP (of_heap h).
    Definition heapI_ctx (N : namespace) : iPropG lang Σ :=
      auth_ctx heapI_name N heapI_inv.

    Global Instance heapI_inv_proper : Proper ((≡) ==> (≡)) heapI_inv.
    Proof. solve_proper. Qed.
    Global Instance heapI_ctx_persistent N : PersistentP (heapI_ctx N).
    Proof. apply _. Qed.
  End definitionsI.
  Typeclasses Opaque heapI_ctx heapI_mapsto.

  Notation "l ↦ᵢ{ q } v" := (heapI_mapsto l q v)
    (at level 20, q at level 50, format "l  ↦ᵢ{ q }  v") : uPred_scope.
  Notation "l ↦ᵢ v" := (heapI_mapsto l 1 v) (at level 20) : uPred_scope.

  Section heap.
    Context {Σ : gFunctors}.
    Implicit Types N : namespace.
    Implicit Types P Q : iPropG lang Σ.
    Implicit Types Φ : val → iPropG lang Σ.
    Implicit Types σ : state.
    Implicit Types h g : heapR.

    Lemma wp_bind {E e} K Φ :
      WP e @ E {{ (λ v, WP (fill K (of_val v)) @ E {{Φ}}) }}
         ⊢ WP (fill K e) @ E {{Φ}}.
    Proof. apply weakestpre.wp_bind. Qed.

    Lemma wp_bindi {E e} Ki Φ :
      WP e @ E {{ (λ v, WP (fill_item Ki (of_val v)) @ E {{Φ}}) }} ⊢
         WP (fill_item Ki e) @ E {{Φ}}.
    Proof. apply weakestpre.wp_bind. Qed.

    Ltac inv_step :=
      repeat
        match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
        | H : prim_step _ _ _ _ _ |- _ => destruct H; subst
        | H : _ = fill ?K ?e |- _ =>
          destruct K as [|[]];
            simpl in H; first [subst e|discriminate H|injection H as H]
        (* ensure that we make progress for each subgoal *)
        | H : head_step ?e _ _ _ _, Hv : of_val ?v = fill ?K ?e |- _ =>
          apply val_head_stuck, (fill_not_val K) in H;
            by rewrite -Hv to_of_val in H (* maybe use a helper lemma here? *)
        | H : head_step ?e _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if e is a
                                     variable and can thus better be avoided. *)
            inversion H; subst; clear H
        end.

    Ltac reshape_val e tac :=
      let rec go e :=
          match e with
          | of_val ?v => v
          | Pair ?e1 ?e2 =>
            let v1 := reshape_val e1 in
            let v2 := reshape_val e2 in constr:(PairV v1 v2)
          | InjL ?e => let v := reshape_val e in constr:(InjLV v)
          | InjR ?e => let v := reshape_val e in constr:(InjRV v)
          | Loc ?l => constr:(LocV l)
          end in let v := go e in first [tac v | fail 2].

    Ltac reshape_expr e tac :=
      let rec go K e :=
          match e with
          | _ => tac (reverse K) e
          | App ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (AppRCtx v1 :: K) e2)
          | App ?e1 ?e2 => go (AppLCtx e2 :: K) e1
          | Pair ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (PairRCtx v1 :: K) e2)
          | Pair ?e1 ?e2 => go (PairLCtx e2 :: K) e1
          | Fst ?e => go (FstCtx :: K) e
          | Snd ?e => go (SndCtx :: K) e
          | InjL ?e => go (InjLCtx :: K) e
          | InjR ?e => go (InjRCtx :: K) e
          | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0
          | Alloc ?e => go (AllocCtx :: K) e
          | Load ?e => go (LoadCtx :: K) e
          | Store ?e1 ?e2 => reshape_val
                              e1 ltac:(fun v1 => go (StoreRCtx v1 :: K) e2)
          | Store ?e1 ?e2 => go (StoreLCtx e2 :: K) e1
          | CAS ?e0 ?e1 ?e2 =>
            reshape_val e0 ltac:
            (fun v0 => first
                      [ reshape_val e1 ltac:
                        (fun v1 => go (CasRCtx v0 v1 :: K) e2)
                      | go (CasMCtx v0 e2 :: K) e1 ])
          | CAS ?e0 ?e1 ?e2 => go (CasLCtx e1 e2 :: K) e0
          end in go (@nil ectx_item) e.

    Ltac do_step tac :=
      try match goal with |- language.reducible _ _ => eexists _, _, _ end;
      simpl;
      match goal with
      | |- prim_step ?e1 ?σ1 ?e2 ?σ2 ?ef =>
        reshape_expr e1 ltac:
        (fun K e1' =>
           eapply Ectx_step with K e1' _; [reflexivity|reflexivity|];
           first [apply alloc_fresh|econstructor; try reflexivity];
           rewrite ?to_of_val; tac)
      | |- head_step ?e1 ?σ1 ?e2 ?σ2 ?ef =>
        first [apply alloc_fresh|econstructor];
        rewrite ?to_of_val; tac
      end.

    Local Hint Extern 0 => do_step ltac:(eauto 2; fail).

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
      of_heap (<[l:=Frac 1 (DecAgree v)]> h) = <[l:=v]> (of_heap h).
    Proof. by rewrite /of_heap -(omap_insert _ _ _ (Frac 1 (DecAgree v))). Qed.
    Lemma of_heap_singleton_op l q v h :
      ✓ ({[l := Frac q (DecAgree v)]} ⋅ h) →
      of_heap ({[l := Frac q (DecAgree v)]} ⋅ h) = <[l:=v]> (of_heap h).
    Proof.
      intros Hv. apply map_eq=> l'; destruct (decide (l' = l)) as [->|].
      - move: (Hv l). rewrite /of_heap lookup_insert
                              lookup_omap (lookup_op _ h) lookup_singleton.
        case _:(h !! l)=>[[q' [v'|]|]|] //=; last by move=> [??].
        move=> [? /dec_agree_op_inv [->]]. by rewrite dec_agree_idemp.
      - rewrite /of_heap lookup_insert_ne // !lookup_omap.
          by rewrite (lookup_op _ h) lookup_singleton_ne // left_id.
    Qed.
    Lemma to_heap_insert l v σ :
      to_heap (<[l:=v]> σ) = <[l:=Frac 1 (DecAgree v)]> (to_heap σ).
    Proof. by rewrite /to_heap -fmap_insert. Qed.
    Lemma of_heap_None h l :
      ✓ h → of_heap h !! l = None → h !! l = None ∨ h !! l ≡ Some FracUnit.
    Proof.
      move=> /(_ l). rewrite /of_heap lookup_omap.
        by case: (h !! l)=> [[q [v|]|]|] //=; destruct 1; auto.
    Qed.
    Lemma heap_store_valid l h v1 v2 :
      ✓ ({[l := Frac 1 (DecAgree v1)]} ⋅ h) →
      ✓ ({[l := Frac 1 (DecAgree v2)]} ⋅ h).
    Proof.
      intros Hv l'; move: (Hv l'). destruct (decide (l' = l)) as [->|].
      - rewrite !lookup_op !lookup_singleton.
        case: (h !! l)=>[x|]; [|done]=> /frac_valid_inv_l=>-> //.
      - by rewrite !lookup_op !lookup_singleton_ne.
    Qed.
    Hint Resolve heap_store_valid.

    Context `{HIGΣ : heapIG Σ}.

    (** Allocation *)
    Lemma heap_alloc N E σ :
      authG lang Σ heapR → nclose N ⊆ E →
      ownP σ ⊢ (|={E}=> ∃ _ : heapIG Σ, heapI_ctx N ∧ Π★{map σ} (λ l v, l ↦ᵢ v)).
    Proof.
      intros. rewrite -{1}(from_to_heap σ). etrans.
      { rewrite [ownP _]later_intro.
        apply (auth_alloc (ownP ∘ of_heap) N E (to_heap σ)); last done.
        apply to_heap_valid. }
      apply pvs_mono, exist_elim=> γ.
      rewrite -(exist_intro (HeapIG _ _ γ)) /heapI_ctx; apply and_mono_r.
      rewrite /heapI_mapsto /heapI_name.
      induction σ as [|l v σ Hl IH] using map_ind.
      { rewrite big_sepM_empty; apply True_intro. }
      rewrite to_heap_insert big_sepM_insert //.
      rewrite (insert_singleton_op (to_heap σ));
        last rewrite lookup_fmap Hl; auto.
        (* FIXME: investigate why we have to unfold auth_own here. *)
        by rewrite auth_own_op IH.
    Qed.

    (** General properties of mapsto *)
    Lemma heap_mapsto_op_eq l q1 q2 v :
      (l ↦ᵢ{q1} v ★ l ↦ᵢ{q2} v)%I ≡ (l ↦ᵢ{q1+q2} v)%I.
    Proof. by rewrite -auth_own_op op_singleton Frac_op dec_agree_idemp. Qed.

    Lemma heap_mapsto_op l q1 q2 v1 v2 :
      (l ↦ᵢ{q1} v1 ★ l ↦ᵢ{q2} v2)%I ≡ (v1 = v2 ∧ l ↦ᵢ{q1+q2} v1)%I.
    Proof.
      destruct (decide (v1 = v2)) as [->|].
      { by rewrite heap_mapsto_op_eq const_equiv // left_id. }
      rewrite -auth_own_op op_singleton Frac_op dec_agree_ne //.
      apply (anti_symm (⊢)); last by apply const_elim_l.
      rewrite auth_own_valid gmap_validI (forall_elim l) lookup_singleton.
      rewrite option_validI frac_validI discrete_valid. by apply const_elim_r.
    Qed.

    Lemma heap_mapsto_op_split l q v :
      (l ↦ᵢ{q} v)%I ≡ (l ↦ᵢ{q/2} v ★ l ↦ᵢ{q/2} v)%I.
    Proof. by rewrite heap_mapsto_op_eq Qp_div_2. Qed.

    (** Base axioms for core primitives of the language: Stateful reductions. *)
    Lemma wp_alloc_pst E σ e v Φ :
      to_val e = Some v →
      (▷ ownP σ ★ ▷ (∀ l, σ !! l = None ∧ ownP (<[l:=v]>σ) -★ Φ (LocV l)))
        ⊢ WP Alloc e @ E {{ Φ }}.
    Proof.
      intros. set (φ e' σ' ef :=
                     ∃ l, ef = @None expr ∧
                          (to_val e') = (Some (LocV l)) ∧ σ' = <[l:=v]>σ ∧ σ !! l = None).
      rewrite -(wp_lift_atomic_step (Alloc e) φ σ) // /φ;
        last by intros; inv_step; eauto.
      apply sep_mono, later_mono; first done.
      apply forall_intro=>e2; apply forall_intro=>σ2; apply forall_intro=>ef.
      apply wand_intro_l.
      rewrite always_and_sep_l -assoc -always_and_sep_l.
      cbn; rewrite to_of_val.
      apply const_elim_l=>-[l [-> [-Heq [-> ?]]]]; inversion Heq; subst.
        by rewrite (forall_elim l) right_id const_equiv // left_id wand_elim_r.
        cbn; rewrite H; eauto.
    Qed.

    Lemma wp_load_pst E σ l v Φ :
      σ !! l = Some v →
      (▷ ownP σ ★ ▷ (ownP σ -★ Φ v)) ⊢ WP Load (Loc l) @ E {{ Φ }}.
    Proof.
      intros.
      rewrite -(wp_lift_atomic_det_step σ v σ None) ?right_id //; cbn; eauto.
        by intros; inv_step; eauto using to_of_val.
    Qed.

    Lemma wp_store_pst E σ l e v v' Φ :
      to_val e = Some v → σ !! l = Some v' →
      (▷ ownP σ ★ ▷ (ownP (<[l:=v]>σ) -★ Φ (UnitV)))
        ⊢ WP Store (Loc l) e @ E {{ Φ }}.
    Proof.
      intros. rewrite -(wp_lift_atomic_det_step σ (UnitV) (<[l:=v]>σ) None)
                         ?right_id //; cbn; eauto.
        by intros; inv_step; eauto.
    Qed.

    Lemma wp_cas_fail_pst E σ l e1 v1 e2 v2 v' Φ :
      to_val e1 = Some v1 → to_val e2 = Some v2 → σ !! l = Some v' → v' ≠ v1 →
      (▷ ownP σ ★ ▷ (ownP σ -★ Φ (♭v false)))
        ⊢ WP CAS (Loc l) e1 e2 @ E {{ Φ }}.
    Proof.
      intros. rewrite -(wp_lift_atomic_det_step σ (♭v false) σ None)
                         ?right_id //; last (by intros; inv_step; eauto);
                simpl; by eauto 10.
    Qed.

    Lemma wp_cas_suc_pst E σ l e1 v1 e2 v2 Φ :
      to_val e1 = Some v1 → to_val e2 = Some v2 → σ !! l = Some v1 →
      (▷ ownP σ ★ ▷ (ownP (<[l:=v2]>σ) -★ Φ (♭v true)))
        ⊢ WP CAS (Loc l) e1 e2 @ E {{ Φ }}.
    Proof.
      intros. rewrite -(wp_lift_atomic_det_step
                          σ (♭v true)  (<[l:=v2]>σ) None)
                         ?right_id //; last (by intros; inv_step; eauto);
                simpl; by eauto 10.
    Qed.

    (** Weakest precondition *)
    Lemma wp_alloc N E e v Φ :
      to_val e = Some v → nclose N ⊆ E →
      (heapI_ctx N ★ ▷  ∀ l, l ↦ᵢ v -★ Φ (LocV l)) ⊢ WP Alloc e @ E {{ Φ }}.
    Proof.
      iIntros {??} "[#Hinv HΦ]". rewrite /heapI_ctx.
      iPvs (auth_empty heapI_name) as "Hheap".
      iApply (auth_fsa heapI_inv (wp_fsa (Alloc e)) _ N); simpl; eauto.
      iFrame "Hinv Hheap". iIntros {h}. rewrite [∅ ⋅ h]left_id.
      iIntros "[% Hheap]". rewrite /heapI_inv.
      iApply wp_alloc_pst; first done. iFrame "Hheap". iNext.
      iIntros {l} "[% Hheap]". iExists (op {[ l := Frac 1 (DecAgree v) ]}), _, _.
      rewrite [{[ _ := _ ]} ⋅ ∅]right_id.
      rewrite -of_heap_insert -(insert_singleton_op h); last by apply of_heap_None.
      iFrame "Hheap". iSplit.
      { iPureIntro; split; first done. by apply (insert_valid h). }
      iIntros "Hheap". iApply "HΦ". by rewrite /heapI_mapsto.
    Qed.

    Lemma wp_load N E l q v Φ :
      nclose N ⊆ E →
      (heapI_ctx N ★ ▷ l ↦ᵢ{q} v ★ ▷ (l ↦ᵢ{q} v -★ Φ v))
        ⊢ WP Load (Loc l) @ E {{ Φ }}.
    Proof.
      iIntros {?} "[#Hh [Hl HΦ]]". rewrite /heapI_ctx /heapI_mapsto.
      iApply (auth_fsa' heapI_inv (wp_fsa _) id _ N _
                        heapI_name {[ l := Frac q (DecAgree v) ]}); simpl; eauto.
      iFrame "Hh Hl". iIntros {h} "[% Hl]". rewrite /heapI_inv.
      iApply (wp_load_pst _ (<[l:=v]>(of_heap h)));first by rewrite lookup_insert.
      rewrite of_heap_singleton_op //. iFrame "Hl". iNext.
      iIntros "$". by iSplit.
    Qed.

    Lemma wp_store N E l v' e v Φ :
      to_val e = Some v → nclose N ⊆ E →
      (heapI_ctx N ★ ▷ l ↦ᵢ v' ★ ▷ (l ↦ᵢ v -★ Φ UnitV))
        ⊢ WP Store (Loc l) e @ E {{ Φ }}.
    Proof.
      iIntros {??} "[#Hh [Hl HΦ]]". rewrite /heapI_ctx /heapI_mapsto.
      iApply (auth_fsa' heapI_inv (wp_fsa _) (alter (λ _, Frac 1 (DecAgree v)) l) _
                        N _ heapI_name {[ l := Frac 1 (DecAgree v') ]}); simpl; eauto.
      iFrame "Hh Hl". iIntros {h} "[% Hl]". rewrite /heapI_inv.
      iApply (wp_store_pst _ (<[l:=v']>(of_heap h))); rewrite ?lookup_insert //.
      rewrite alter_singleton insert_insert !of_heap_singleton_op; eauto.
      iFrame "Hl". iNext. iIntros "$". iFrame "HΦ". iPureIntro; naive_solver.
    Qed.

    Lemma wp_cas_fail N E l q v' e1 v1 e2 v2 Φ :
      to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 → nclose N ⊆ E →
      (heapI_ctx N ★ ▷ l ↦ᵢ{q} v' ★ ▷ (l ↦ᵢ{q} v' -★ Φ (♭v false)))
        ⊢ WP CAS (Loc l) e1 e2 @ E {{ Φ }}.
    Proof.
      iIntros {????} "[#Hh [Hl HΦ]]". rewrite /heapI_ctx /heapI_mapsto.
      iApply (auth_fsa' heapI_inv (wp_fsa _) id _ N _
                        heapI_name {[ l := Frac q (DecAgree v') ]}); simpl; eauto 10.
      iFrame "Hh Hl". iIntros {h} "[% Hl]". rewrite /heapI_inv.
      iApply (wp_cas_fail_pst _ (<[l:=v']>(of_heap h))); rewrite ?lookup_insert //.
      rewrite of_heap_singleton_op //. iFrame "Hl". iNext.
      iIntros "$". by iSplit.
    Qed.

    Lemma wp_cas_suc N E l e1 v1 e2 v2 Φ :
      to_val e1 = Some v1 → to_val e2 = Some v2 → nclose N ⊆ E →
      (heapI_ctx N ★ ▷ l ↦ᵢ v1 ★ ▷ (l ↦ᵢ v2 -★ Φ (♭v true)))
        ⊢ WP CAS (Loc l) e1 e2 @ E {{ Φ }}.
    Proof.
      iIntros {???} "[#Hh [Hl HΦ]]". rewrite /heapI_ctx /heapI_mapsto.
      iApply (auth_fsa' heapI_inv (wp_fsa _) (alter (λ _, Frac 1 (DecAgree v2)) l)
                        _ N _ heapI_name {[ l := Frac 1 (DecAgree v1) ]}); simpl; eauto 10.
      iFrame "Hh Hl". iIntros {h} "[% Hl]". rewrite /heapI_inv.
      iApply (wp_cas_suc_pst _ (<[l:=v1]>(of_heap h))); rewrite ?lookup_insert //.
      rewrite alter_singleton insert_insert !of_heap_singleton_op; eauto.
      iFrame "Hl". iNext. iIntros "$". iFrame "HΦ". iPureIntro; naive_solver.
    Qed.

    (** Helper Lemmas for weakestpre. *)

    Lemma wp_lam E e1 e2 v Φ :
      to_val e2 = Some v →
      ▷ WP e1.[(Lam e1), e2 /] @ E {{Φ}} ⊢ WP (App (Lam e1) e2) @ E {{Φ}}.
    Proof.
      intros <-%of_to_val.
      rewrite -(wp_lift_pure_det_step
                  (App _ _) e1.[(Lam e1), of_val v /] None) //=.
      - by rewrite right_id.
      - intros. inv_step; auto.
    Qed.

    Lemma wp_TLam E e Φ :
      ▷ WP e @ E {{Φ}} ⊢ WP (TApp (TLam e)) @ E {{Φ}}.
    Proof.
      rewrite -(wp_lift_pure_det_step (TApp _) e None) //=.
      - by rewrite right_id.
      - intros. inv_step; auto.
    Qed.

    Lemma wp_Fold E e v Φ :
      to_val e = Some v →
      ▷ Φ v ⊢ WP (Unfold (Fold e)) @ E {{Φ}}.
    Proof.
      intros <-%of_to_val.
      rewrite -(wp_lift_pure_det_step (Unfold _) (of_val v) None) //=; auto.
      - rewrite right_id; auto using uPred.later_mono, wp_value'.
      - intros. inv_step; auto.
    Qed.

    Lemma wp_fst E e1 v1 e2 v2 Φ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      ▷ Φ v1 ⊢ WP (Fst (Pair e1 e2)) @ E {{Φ}}.
    Proof.
      intros <-%of_to_val <-%of_to_val.
      rewrite -(wp_lift_pure_det_step (Fst (Pair _ _)) (of_val v1) None) //=.
      - rewrite right_id; auto using uPred.later_mono, wp_value'.
      - intros. inv_step; auto.
    Qed.

    Lemma wp_snd E e1 v1 e2 v2 Φ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      ▷ Φ v2 ⊢ WP (Snd (Pair e1 e2)) @ E {{Φ}}.
    Proof.
      intros <-%of_to_val <-%of_to_val.
      rewrite -(wp_lift_pure_det_step (Snd (Pair _ _)) (of_val v2) None) //=.
      - rewrite right_id; auto using uPred.later_mono, wp_value'.
      - intros. inv_step; auto.
    Qed.

    Lemma wp_case_inl E e0 v0 e1 e2 Φ :
      to_val e0 = Some v0 →
      ▷ WP e1.[e0/] @ E {{Φ}} ⊢ WP (Case (InjL e0) e1 e2) @ E {{Φ}}.
    Proof.
      intros <-%of_to_val.
      rewrite -(wp_lift_pure_det_step
                  (Case (InjL _) _ _) (e1.[of_val v0/]) None) //=.
      - rewrite right_id; auto using uPred.later_mono, wp_value'.
      - intros. inv_step; auto.
    Qed.

    Lemma wp_case_inr E e0 v0 e1 e2 Φ :
      to_val e0 = Some v0 →
      ▷ WP e2.[e0/] @ E {{Φ}} ⊢ WP (Case (InjR e0) e1 e2) @ E {{Φ}}.
    Proof.
      intros <-%of_to_val.
      rewrite -(wp_lift_pure_det_step
                  (Case (InjR _) _ _) (e2.[of_val v0/]) None) //=.
      - rewrite right_id; auto using uPred.later_mono, wp_value'.
      - intros. inv_step; auto.
    Qed.

    Lemma wp_fork E e Φ :
      (▷ Φ UnitV ★ ▷ WP e {{ _, True }}) ⊢ WP Fork e @ E {{ Φ }}.
    Proof.
      (rewrite -(wp_lift_pure_det_step (Fork e) Unit (Some e)) //=);
        last by intros; inv_step; eauto.
      rewrite later_sep -(wp_value _ _ (Unit)) //.
    Qed.

    Lemma wp_if_false E e1 e2 Φ :
      ▷ WP e2 @ E {{Φ}} ⊢ WP (If (♭ false) e1 e2) @ E {{Φ}}.
    Proof.
      rewrite -(wp_lift_pure_det_step (If (♭ false) _ _) (e2) None) //=.
      - rewrite right_id; auto using uPred.later_mono, wp_value'.
      - intros. inv_step; auto.
    Qed.

    Lemma wp_if_true E e1 e2 Φ :
      ▷ WP e1 @ E {{Φ}} ⊢ WP (If (♭ true) e1 e2) @ E {{Φ}}.
    Proof.
      rewrite -(wp_lift_pure_det_step (If (♭ true) _ _) (e1) None) //=.
      - rewrite right_id; auto using uPred.later_mono, wp_value'.
      - intros. inv_step; auto.
    Qed.

    Lemma wp_nat_bin_op E op a b Φ :
      ▷ Φ (NatBinOP_meaning op a b) ⊢ WP (NBOP op (♯ a) (♯ b)) @ E {{Φ}}.
    Proof.
      rewrite -(wp_lift_pure_det_step
                  (NBOP _ _ _) (of_val (NatBinOP_meaning op a b)) None) //=.
      - rewrite right_id; auto using uPred.later_mono, wp_value'.
      - intros. inv_step; auto.
    Qed.

  End heap.

End lang_rules.

Notation "l ↦ᵢ{ q } v" := (heapI_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦ᵢ{ q }  v") : uPred_scope.
Notation "l ↦ᵢ v" := (heapI_mapsto l 1 v) (at level 20) : uPred_scope.