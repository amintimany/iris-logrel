Require Import Coq.Relations.Relation_Operators.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import F_mu_ref_par.lang F_mu_ref_par.rules.
From iris.program_logic Require Export lifting.
From iris.algebra Require Import upred_big_op frac dec_agree list.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
(* From iris.proofmode Require Import weakestpre. *)
Require Import iris.proofmode.tactics iris.proofmode.invariants.
Import uPred.

Section lang_rules.
  (** The CMRA for the heap of the specification. *)
  Definition tpoolR : cmraT := listR (fracR (dec_agreeR expr)).

  Global Instance tpool_singleton :
    SingletonM nat (fracR (dec_agreeR expr)) tpoolR.
  Proof. typeclasses eauto. Defined.

  Definition to_tpool : (list expr) → tpoolR :=
    map (λ v, Frac 1 (DecAgree v)).
  Definition of_tpool : tpoolR → (list expr) :=
    omap (mbind (maybe DecAgree ∘ snd) ∘ maybe2 Frac).

  Lemma of_tpool_equiv_eq (tp tp' : tpoolR) :
    tp ≡ tp' → (of_tpool tp) = (of_tpool tp').
  Proof.
    induction 1 as [|x y tp1 tp2 H1 H2]; cbn; trivial.
    destruct x as [q [x|]|]; destruct y as [q' [y|]|]; simpl;
      inversion_clear H1 as [? ? ? ? ? [] []|]; subst; trivial.
    by apply (f_equal (cons _)).
  Qed.

  Lemma of_heap_lookup_equiv_eq (h h' : heapR) :
    h ≡ h' → ∀ i, h !! i = h' !! i.
  Proof.
    intros H i.
    specialize (H i).
    match type of H with
      ?A ≡ ?B =>
      match goal with
        |- ?A' = ?B' => change A with A' in *; change B with B' in *
      end
    end.
    destruct (h !! i) as [hi|]; destruct (h' !! i) as [hi'|];
      inversion H as [? ? H1|]; subst; trivial.
    inversion H1 as [? ? ? ? ? H2|]; subst; trivial.
    inversion H2; subst; trivial.
  Qed.
  Lemma of_heap_equiv_eq (h h' : heapR) :
    h ≡ h' → (of_heap h) = (of_heap h').
  Proof.
    intros H; unfold of_heap. apply map_eq => i.
    repeat rewrite lookup_omap. f_equal.
    apply of_heap_lookup_equiv_eq; trivial.
  Qed.

  Definition cfgR := prodR tpoolR heapR.

  Definition of_cfg (ρ : cfgR) : cfg lang := (of_tpool (ρ.1), of_heap (ρ.2)).
  Definition to_cfg (ρ : cfg lang) : cfgR := (to_tpool (ρ.1), to_heap (ρ.2)).

  Lemma of_cfg_equiv_eq (ρ ρ' : cfgR) :
    ρ ≡ ρ' → (of_cfg ρ) = (of_cfg ρ').
  Proof.
    intros [H1 H2]; destruct ρ as [tp hp]; destruct ρ' as [tp' hp'];
      unfold of_cfg; cbn in *.
    erewrite of_tpool_equiv_eq, of_heap_equiv_eq; eauto.
  Qed.

  (** The CMRA for the thread pool. *)
  Class cfgSG Σ :=
    CFGSG {
        cfg_inG :> authG lang Σ cfgR;
        cfg_name : gname
      }.

  Section definitionsS.
    Context `{icfg : cfgSG Σ}.

    Definition heapS_mapsto (l : loc) (q : Qp) (v: val) : iPropG lang Σ :=
      auth_own cfg_name (∅ : tpoolR, {[ l := Frac q (DecAgree v) ]}).

    Definition tpool_mapsto (j : nat) (q : Qp) (e: expr) : iPropG lang Σ :=
      auth_own cfg_name ({[ j := Frac q (DecAgree e : dec_agreeR _) ]},
                         ∅ : heapR).

    Definition Makes_Steps := clos_refl_trans _ (@step lang).

    Definition Spec_inv (ρ ρ' : cfgR) : iPropG lang Σ :=
      (■ Makes_Steps (of_cfg ρ) (of_cfg ρ'))%I.

    Definition Spec_ctx (S : namespace) (ρ : cfgR) : iPropG lang Σ :=
      auth_ctx cfg_name S (Spec_inv ρ).

    Global Instance Spec_inv_Proper : Proper ((≡) ==> (≡) ==> (≡)) Spec_inv.
    Proof.
      intros ρ1 ρ2 H ρ1' ρ2' H'; unfold Spec_inv.
      erewrite of_cfg_equiv_eq with ρ1 ρ2; eauto.
      erewrite of_cfg_equiv_eq with ρ1' ρ2'; eauto.
    Qed.

    Global Instance Spec_ctx_persistent N ρ :
      PersistentP (Spec_ctx N ρ).
    Proof. apply _. Qed.
  End definitionsS.
  Typeclasses Opaque heapS_mapsto tpool_mapsto.

  Notation "l ↦ₛ{ q } v" := (heapS_mapsto l q v)
    (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : uPred_scope.
  Notation "l ↦ₛ v" := (heapS_mapsto l 1 v) (at level 20) : uPred_scope.

  Notation "j ⤇{ q } e" :=
    (tpool_mapsto j q e)
      (at level 20, q at level 50, format "j  ⤇{ q }  e") : uPred_scope.
  Notation "j ⤇ e" := (tpool_mapsto j 1 e) (at level 20) : uPred_scope.

  Section cfg.
    Context {Σ : gFunctors}.
    Implicit Types N : namespace.
    Implicit Types P Q : iPropG lang Σ.
    Implicit Types Φ : val → iPropG lang Σ.
    Implicit Types σ : state.
    Implicit Types g : heapR.

    (** Conversion to tpools and back *)
    Global Instance of_tpool_proper : Proper ((≡) ==> (=)) of_tpool.
    Proof. solve_proper. Qed.
    Lemma from_to_tpool l : of_tpool (to_tpool l) = l.
    Proof. induction l; trivial. simpl; f_equal; trivial. Qed.
    Lemma to_tpool_valid l : ✓ to_tpool l.
    Proof. induction l; constructor; trivial.
           repeat (unfold valid, cmra_valid; cbn); auto.
    Qed.
    Global Instance of_cfg_proper : Proper ((≡) ==> (=)) of_cfg.
    Proof. solve_proper. Qed.
    Lemma from_to_cfg ρ : of_cfg (to_cfg ρ) = ρ.
    Proof. destruct ρ as [t h]; unfold to_cfg, of_cfg; simpl.
           by rewrite from_to_tpool from_to_heap.
    Qed.
    Lemma to_cfg_valid ρ : ✓ to_cfg ρ.
    Proof. constructor; cbn; auto using to_tpool_valid, to_heap_valid. Qed.


    (*
    Lemma of_tpool_insert e l :
      of_tpool (l ++ [(Some (DecAgree e : dec_agreeR _))]) =
      (of_tpool l) ++ [e].
    Proof.
      induction l as [|x l]; trivial. destruct x as [[]|]; simpl; trivial.
      by rewrite IHl.
    Qed.
    Lemma to_tpool_insert e l :
      to_tpool (l ++ [e]) = (to_tpool l) ++ [(Some (DecAgree e : dec_agreeR _))].
    Proof. by rewrite /to_tpool map_app. Qed.
    Lemma tpool_update_valid e1 e2 l1 l2 :
      ✓ (l1 ++ (Some (DecAgree e1 : dec_agreeR _)) :: l2) →
      ✓ (l1 ++ (Some (DecAgree e2 : dec_agreeR _)) :: l2).
    Proof.
      intros H1. apply Forall_app. apply Forall_app in H1.
      destruct H1 as [H1 H2]; split; trivial.
      inversion H2; subst. by constructor.
    Qed. *)
(*    Lemma tpool_unfold j e ρ ρ' :
      ✓ (({[ j := (Some (DecAgree e : dec_agreeR _)) ]}, ∅ : heapR) ⋅ ρ) →
      (({[ j := (Some (DecAgree e : dec_agreeR _)) ]}, ∅ : heapR) ⋅ ρ) ≡ ρ' →
      ∃ l1 l2 σ, List.length l1 = j ∧ ρ' = to_cfg ((l1 ++ e :: l2), σ).
    Proof.
      revert ρ ρ'; induction j => ρ ρ'.
      {
        destruct ρ as [tp hp]; cbn.
        inversion_clear 1; simpl in *.
        inversion_clear 1; simpl in *.
        destruct ρ' as [tp' hp']; simpl in *.
        eexists []; eexists []; eexists (of_heap hp'); split;
          unfold to_cfg; simpl; trivial.
        
        

        destruct ρ as [[|e' tp] hp]; cbn.
        inversion_clear 1; simpl in *.
        inversion_clear 1; simpl in *.
        destruct ρ' as [tp' hp']; simpl in *.
        eexists [] []
        
      intros H1. apply Forall_app. apply Forall_app in H1.
      destruct H1 as [H1 H2]; split; trivial.
      inversion H2; subst. by constructor.
    Qed.
    *)
   (* Hint Resolve tpool_update_valid. *)

    Context`{icfg : cfgSG Σ}.

    Lemma tpool_update_valid j e e' tp :
      ✓ ({[ j := (Frac 1 (DecAgree e : dec_agreeR _)) ]} ⋅ tp) →
      ✓ ({[ j := (Frac 1 (DecAgree e' : dec_agreeR _)) ]} ⋅ tp).
    Proof.
      intros H1.
      apply Forall_lookup => i x H2.
      destruct (eq_nat_dec j i); [subst|].
      - assert (H3 := proj1 (Forall_lookup _ _) H1 i). cbn in H3.
        rewrite list_op_lookup in H2. rewrite list_op_lookup in H3.
        rewrite list_Singleton_lookup in H2.
        rewrite list_Singleton_lookup in H3.
        match goal with
          [H : Some _ ⋅ ?B = Some _, H' : forall x, Some _ ⋅ ?B = Some x → _ |- _] =>
          destruct B as [y|]
        end.
        + unfold op, cmra_op in *; simpl in *.
          specialize (H3 (Frac 1 (DecAgree e) ⋅ y) Logic.eq_refl).
          rewrite (frac_valid_inv_l _ _ H3) in H2.
          inversion H2.
          repeat constructor; auto.
        + inversion H2. repeat constructor; auto.
      - assert (H3 := proj1 (Forall_lookup _ _) H1 i). cbn in H3.
        rewrite list_op_lookup in H2. rewrite list_op_lookup in H3.
        edestruct (list_Singleton_lookup_2 j i) with
        (Frac 1 (DecAgree e) : fracR (dec_agreeR _)) as [H4 | H4]; trivial;
          edestruct (list_Singleton_lookup_2 j i)
          with (Frac 1 (DecAgree e'): fracR (dec_agreeR _)) as [H5|H5]; trivial;
            rewrite H4 in H3; rewrite H5 in H2;
        match goal with
          [H : _ ⋅ ?B = Some _, H' : forall x, _ ⋅ ?B = Some x → _ |- _] =>
          destruct B as [[]|]
        end;
        unfold op, cmra_op in H2, H3; inversion H2; simpl in *;
          try (apply H3; trivial; fail).
        constructor.
    Qed.

    Lemma tpool_conv j e tp :
      ✓ ({[ j := (Frac 1 (DecAgree e : dec_agreeR _)) ]} ⋅ tp) → ∃ l1 l2,
      ∀ e', of_tpool ({[ j := (Frac 1 (DecAgree e' : dec_agreeR _)) ]} ⋅ tp) =
            l1 ++ e' :: l2.
    Proof.
      revert j. induction tp as [|t tp]; intros j H.
      - exists []; exists []; intros e'. clear H.
        induction j; simpl; trivial; simpl in *.
        rewrite list_op_nil in IHj; trivial.
      - destruct j; simpl in *.
        + inversion H; subst. rewrite (frac_valid_inv_l _ _ H2); simpl.
          eexists [], _; intros e'; trivial.
        + inversion H; subst.
          destruct t as [q [t|]|]; simpl in *.
          * edestruct IHtp as [l1 [l2 Hl]]; eauto.
            exists (t :: l1), l2 => e'; rewrite Hl; trivial.
          * inversion H2. inversion H1.
          * apply IHtp; trivial.
    Qed.

    Lemma step_alloc_base ρ j K e v :
      ✓ (({[j := (Frac 1 (DecAgree (fill K (Alloc e))))]}, ∅) ⋅ ρ) →
      to_val e = Some v →
      ∃ l, step
             (of_cfg (({[j := (Frac 1 (DecAgree (fill K (Alloc e))))]}, ∅) ⋅ ρ))
             (of_cfg (({[j := Frac 1 (DecAgree (fill K (Loc l)))]}, ∅) ⋅
                        (∅, ({[l := Frac 1 (DecAgree v)]})) ⋅ ρ)).
    Proof.
      intros H1 H2.
      destruct ρ as [tp th].
      set (l := fresh (dom (gset positive) (of_heap th))).
      exists l.
      unfold op, cmra_op; simpl. unfold prod_op; simpl.
      repeat rewrite left_id; rewrite right_id.
      unfold of_cfg; simpl.
      destruct H1 as [H11 H12]; simpl in *.
      destruct (tpool_conv _ _ _ H11) as [l1 [l2 H3]].
      repeat rewrite H3.
      rewrite of_heap_singleton_op.
      { eapply (step_atomic _ _ _ _ _ _ None _ _).
        - trivial.
        - simpl; rewrite app_nil_r; trivial.
        - econstructor; eauto. apply alloc_fresh; trivial. }
      admit.
    Admitted.

    Lemma wp_alloc N E ρ j K e v Φ :
      to_val e = Some v → nclose N ⊆ E →
      ((Spec_ctx N ρ ★ j ⤇ (fill K (Alloc e)))%I)
        ⊢ |={E}=>(∃ l, j ⤇ (fill K (Loc l)) ★ l ↦ₛ v)%I.
    Proof.
      iIntros {H1 H2} "[#Hinv HΦ]".
      unfold Spec_ctx, auth_ctx, tpool_mapsto, auth_own.
      iInv> N as {ρ'} "[Hown #Hstep]".
      iCombine "HΦ" "Hown" as "Hown".
      iDestruct (own_valid _ with "Hown !") as "Hvalid".
      iDestruct (auth_validI _ with "Hvalid") as "[Ha' %]";
        simpl; iClear "Hvalid".
      iDestruct "Ha'" as {ρ''} "Ha'"; iDestruct "Ha'" as %Ha'.
      rewrite ->(right_id _ _) in Ha'; setoid_subst.
      iDestruct "Hstep" as %Hstep.
      edestruct step_alloc_base as [l Hs]; eauto.
      


      destruct ρ'' as [tp hp]; simpl in *.
      unfold op, cmra_op in Hstep; cbn in Hstep.
      unfold prod_op in Hstep; cbn in Hstep.
      unfold of_cfg at 2 in Hstep.
      cbn in Hstep.


(*******************************)


      Lemma wp_load N E ρ j K l v Φ :
        nclose N ⊆ E →
        ((Spec_ctx N ρ ★ j ⤇ (fill K (Load (Loc l))) ★ l ↦ₛ v)%I)
          ⊢ |={E}=>(∃ l, j ⤇ (fill K (of_val v)) ★ l ↦ₛ v)%I.
      Proof.
        iIntros {H} "[#Hinv HΦ]".
        unfold Spec_ctx, auth_ctx, tpool_mapsto, heapS_mapsto, auth_own.
        iInv> N as {ρ'} "[Hown #Hstep]".
        rewrite -own_op.
        iCombine "HΦ" "Hown" as "Hown".
        iDestruct (own_valid _ with "Hown ! !") as "Hvalid".
        iDestruct (auth_validI _ with "Hvalid") as "[Ha' %]";
          simpl; iClear "Hvalid".
        iDestruct "Ha'" as {ρ''} "Ha'"; iDestruct "Ha'" as %Ha'.
        rewrite ->(right_id _ _) in Ha'; setoid_subst.
        iDestruct "Hstep" as %Hstep.
        destruct ρ'' as [tp hp]; simpl in *.
        unfold op, cmra_op in Hstep; simpl in Hstep.
        unfold prod_op in Hstep; simpl in Hstep.
        unfold of_cfg at 2 in Hstep.
        simpl in Hstep.
        
        iPvs (own_update  with "Hown") as "Hγ".
        iApply.
        
        
        iDestruct "Hstep" as %Hstp.
        destruct ρ'' as [tp hp]; simpl in *.
        iDestruct "Hstep" as {ρ'} "[% %]".



(*******************************)









      
      
      assert (Makes_Steps (of_cfg ρ) (of_cfg ρ'))
      

      
      iIntros {??} "(#? & Hγf & HΨ)". rewrite /auth_ctx /auth_own.
      iInv N as {a'} "[Hγ Hφ]".
      iTimeless "Hγ"; iTimeless "Hγf". iCombine "Hγ" "Hγf" as "Hγ".
      iDestruct (own_valid _ with "Hγ !") as "Hvalid".
      iDestruct (auth_validI _ with "Hvalid") as "[Ha' %]"; simpl; iClear "Hvalid".
      iDestruct "Ha'" as {b} "Ha'"; iDestruct "Ha'" as %Ha'.
      rewrite ->(left_id _ _) in Ha'; setoid_subst.
      iApply pvs_fsa_fsa; iApply fsa_wand_r; iSplitL "HΨ Hφ".
      { iApply "HΨ"; by iSplit. }
      iIntros {v} "HL". iDestruct "HL" as {L Lv ?} "(% & Hφ & HΨ)".
      iPvs (own_update _ with "Hγ") as "[Hγ Hγf]".
      { apply (auth_local_update_l L); tauto. }
      iPvsIntro. iSplitL "Hφ Hγ"; last by iApply "HΨ".
      iNext. iExists (L a ⋅ b). by iFrame "Hφ".
      
      unfold Spec_ctx, auth_ctx.
      iInv> N as {t} "[Hown #Hstp]".
      
      iApply (auth_fsa' ).
      

      
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
      (heapI_ctx N ★ ▷ l ↦ᵢ{q} v' ★ ▷ (l ↦ᵢ{q} v' -★ Φ (FALSEV)))
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
      (heapI_ctx N ★ ▷ l ↦ᵢ v1 ★ ▷ (l ↦ᵢ v2 -★ Φ (TRUEV)))
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
      to_val e2 = Some v → ▷ WP e1.[e2 /] @ E {{Φ}} ⊢ WP (App (Lam e1) e2) @ E {{Φ}}.
    Proof.
      intros <-%of_to_val.
      rewrite -(wp_lift_pure_det_step (App _ _) e1.[of_val v /] None) //=.
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
      rewrite -(wp_lift_pure_det_step (Case (InjL _) _ _) (e1.[of_val v0/]) None) //=.
      - rewrite right_id; auto using uPred.later_mono, wp_value'.
      - intros. inv_step; auto.
    Qed.

    Lemma wp_case_inr E e0 v0 e1 e2 Φ :
      to_val e0 = Some v0 →
      ▷ WP e2.[e0/] @ E {{Φ}} ⊢ WP (Case (InjR e0) e1 e2) @ E {{Φ}}.
    Proof.
      intros <-%of_to_val.
      rewrite -(wp_lift_pure_det_step (Case (InjR _) _ _) (e2.[of_val v0/]) None) //=.
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

  End heap.

End lang_rules.

Notation "l ↦ᵢ{ q } v" := (heapI_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦ᵢ{ q }  v") : uPred_scope.
Notation "l ↦ᵢ v" := (heapI_mapsto l 1 v) (at level 20) : uPred_scope.