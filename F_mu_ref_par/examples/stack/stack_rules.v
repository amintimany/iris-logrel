From iris.proofmode Require Import invariants ghost_ownership tactics.
From iris_logrel.F_mu_ref_par Require Import logrel_binary.
From iris.algebra Require Import gmap dec_agree.
From iris.program_logic Require Import auth.
Import uPred.

Definition stackUR : ucmraT := gmapUR loc (dec_agreeR val).

Lemma stackR_self_op (h : stackUR) : h ≡ h ⋅ h.
Proof.
  intros i. rewrite lookup_op.
  match goal with
    |- ?A ≡ ?B ⋅ ?B => change B with A; destruct A as [c|]
  end; trivial.
  destruct c as [c|]; cbv -[equiv decide];
    try destruct decide; trivial; tauto.
Qed.

Class stackG Σ :=
  StackG { stack_inG :> authG lang Σ stackUR; stack_name : gname }.

Section Rules.
  Context `{stackG Σ}.
  Notation D := (prodC valC valC -n> iPropG lang Σ).

  Definition stack_mapsto (l : loc) (v: val) : iPropG lang Σ :=
    auth_own stack_name {[ l := DecAgree v ]}.

  Notation "l ↦ˢᵗᵏ v" := (stack_mapsto l v) (at level 20) : uPred_scope.

  Lemma stack_mapsto_dup l v : l ↦ˢᵗᵏ v ⊢ l ↦ˢᵗᵏ v ★ l ↦ˢᵗᵏ v.
  Proof.
    by rewrite /stack_mapsto /auth_own -own_op -auth_frag_op -stackR_self_op.
  Qed.

  Lemma stack_mapstos_agree l v w:
    l ↦ˢᵗᵏ v ★ l ↦ˢᵗᵏ w ⊢ l ↦ˢᵗᵏ v ★ l ↦ˢᵗᵏ w ∧ v = w.
  Proof.
    iIntros "H".
    rewrite -own_op.
    iDestruct (own_valid _ with "#H") as %Hvalid.
    rewrite own_op. unfold stack_mapsto, auth_own.
    iDestruct "H" as "[$ $]".
    specialize (Hvalid l). rewrite lookup_op ?lookup_singleton in Hvalid.
    cbv -[decide] in Hvalid; destruct decide; trivial.
  Qed.

  Program Definition StackLink_pre (Q : D) : D -n> D := λne P v,
    (∃ l w, v.1 = LocV l ★ l ↦ˢᵗᵏ w ★
            ((w = InjLV UnitV ∧ v.2 = FoldV (InjLV UnitV)) ∨
            (∃ y1 z1 y2 z2, w = InjRV (PairV y1 (FoldV z1)) ★
              v.2 = FoldV (InjRV (PairV y2 z2)) ★ Q (y1, y2) ★ ▷ P(z1, z2))))%I.
  Solve Obligations with solve_proper.

  Global Instance StackLink_pre_contractive Q : Contractive (StackLink_pre Q).
  Proof.
    intros n P1 P2 HP v; simpl. repeat (apply exist_ne => ?).
    repeat apply sep_ne; trivial. rewrite or_ne; trivial.
    repeat (apply exist_ne => ?).
    repeat apply sep_ne; trivial.
    apply later_contractive => i ?. by apply HP.
  Qed.

  Definition StackLink Q := fixpoint (StackLink_pre Q).

  Lemma StackLink_unfold Q v :
    StackLink Q v ≡ (∃ l w,
      v.1 = LocV l ★ l ↦ˢᵗᵏ w ★
      ((w = InjLV UnitV ∧ v.2 = FoldV (InjLV UnitV)) ∨
      (∃ y1 z1 y2 z2, w = InjRV (PairV y1 (FoldV z1))
                      ★ v.2 = FoldV (InjRV (PairV y2 z2))
                      ★ Q (y1, y2) ★ ▷ @StackLink Q (z1, z2))))%I.
  Proof. by rewrite {1}/StackLink fixpoint_unfold. Qed.

  Global Opaque StackLink. (* So that we can only use the unfold above. *)

  Lemma StackLink_dup (Q : D) v `{∀ vw, PersistentP (Q vw)} :
    StackLink Q v ⊢ StackLink Q v ★ StackLink Q v.
  Proof.
    iIntros "H". iLöb {v} as "Hlat". rewrite StackLink_unfold.
    iDestruct "H" as {l w} "[% [Hl Hr]]"; subst.
    iDestruct (stack_mapsto_dup with "[Hl]") as "[Hl1 Hl2]"; eauto.
    iDestruct "Hr" as "[#Hr|Hr]".
    { iSplitL "Hl1".
      - iExists _, _; iFrame "Hl1"; eauto.
      - iExists _, _; iFrame "Hl2"; eauto. }
    iDestruct "Hr" as {y1 z1 y2 z2} "[#H1 [#H2 [#HQ H']]]".
    rewrite later_forall; setoid_rewrite later_wand.
    iDestruct ("Hlat" $! (z1, z2) with "H'") as "[HS1 HS2]".
    iSplitL "Hl1 HS1".
    - iExists _, _; iFrame "Hl1"; eauto 10.
    - iExists _, _; iFrame "Hl2"; eauto 10.
  Qed.

  Lemma stackR_valid (h : stackUR) (i : loc) :
    ✓ h → h !! i = None ∨ ∃ v, h !! i = Some (DecAgree v).
  Proof.
    intros Hh; specialize (Hh i).
    by match type of Hh with
      ✓ ?A => match goal with
             | |- ?B = _ ∨ (∃ _, ?C = _) =>
               change B with A; change C with A;
                 destruct A as [[c|]|]; inversion H; eauto
             end
    end.
  Qed.

  Lemma stackR_alloc (h : stackUR) (i : loc) (v : val) :
    h !! i = None → ● h ~~> ● (<[i := DecAgree v]> h) ⋅ ◯ {[i := DecAgree v]}.
  Proof.
    intros H1; apply cmra_total_update.
    intros n z H2. rewrite (insert_singleton_op h); auto.
    destruct z as [[ze |] zo];
      unfold validN, cmra_validN in *; simpl in *; trivial.
    destruct H2 as [H21 H22]; split.
    - revert H21; rewrite !left_id. apply cmra_preservingN_l.
    - intros j. rewrite lookup_op.
      destruct (decide (i = j)) as [|Hneq]; subst.
      + rewrite H1. rewrite lookup_singleton. constructor.
      + rewrite lookup_singleton_ne; trivial.
        specialize (H22 j).
        revert H22.
        match goal with
          |- ✓{_} ?B → ✓{_} (_ ⋅ ?A) =>
          change B with A; destruct A; by try constructor
        end.
  Qed.

  Lemma dec_agree_valid_op_eq (x y : dec_agreeR val) :
    ✓ (Some x ⋅ Some y) → x = y.
  Proof.
    intros H1.
    destruct x as [x|]; destruct y as [y|]; trivial;
      cbv -[decide] in H1; try destruct decide; subst; simpl; intuition trivial.
  Qed.

  Lemma stackR_auth_is_subheap (h h' : stackUR) :
    ✓ (● h ⋅ ◯ h') → ∀ i x, h' !! i = Some x → h !! i = Some x.
  Proof.
    intros H1 i x H2.
    destruct H1 as [H11 H12]; simpl in H11.
    specialize (H11 1).
    destruct H11 as [z H11].
    revert H11; rewrite ucmra_unit_left_id => H11.
    eapply cmra_extend in H11; [| by apply cmra_valid_validN].
    destruct H11 as [[z1 z2] [H31 [H32 H33]]]; simpl in *.
    specialize (H32 i).
    assert (H4 : ✓ (z1 ⋅ z2))by (by rewrite -H31).
    apply leibniz_equiv.
    rewrite H31. rewrite lookup_op.
    specialize (H4 i). rewrite ?lookup_op in H4.
    revert H32; rewrite H2 => H32.
    match type of H32 with
      ?C ≡{_}≡ _ =>
      match goal with
        |- ?A ⋅ ?B ≡ _ =>
        change C with A in *; destruct A as [a|]; inversion H32; subst
      end
    end.
    match type of H32 with
      ?C ≡{_}≡ _ =>
      match goal with
        |- ?A ⋅ ?B ≡ _ => destruct B
      end
    end.
    - set (H5 := dec_agree_valid_op_eq _ _ H4); clearbody H5. subst.
      inversion H3; subst.
      destruct x as [x|]; cbv -[decide]; try destruct decide;
        constructor; intuition trivial.
    - inversion H3; subst. constructor; trivial.
  Qed.

  Context {iI : heapIG Σ}.

  Definition stack_owns (h : stackUR) :=
    (ghost_ownership.own stack_name (● h)
        ★ [★ map] l ↦ v ∈ h, match v with
                             | DecAgree v' => l ↦ᵢ v'
                             | _ => True
                             end)%I.

  Lemma stack_owns_alloc E h l v :
    stack_owns h ★ l ↦ᵢ v
      ={E}=> stack_owns (<[l := DecAgree v]> h) ★ l ↦ˢᵗᵏ v.
  Proof.
    iIntros "[[Hown Hall] Hl]".
    iDestruct (own_valid _ with "#Hown") as "Hvalid".
    iDestruct (auth_validI _ with "Hvalid") as "[Ha' Hb]";
      simpl; iClear "Hvalid".
    iDestruct "Hb" as %H1.
    iDestruct "Ha'" as {h'} "Ha'"; iDestruct "Ha'" as %Ha'.
    rewrite ->(left_id _ _) in Ha'; setoid_subst.
    specialize (H1 l).
    match type of H1 with
      ✓ ?A => change A with (h' !! l) in H1
    end.
    destruct (h' !! l) as [[w|]|] eqn:Heq; inversion H1.
    - rewrite -{2}(insert_id _ _ _ Heq) -insert_delete.
      rewrite big_sepM_insert; [|apply lookup_delete_None; auto].
      iDestruct "Hall" as "[Hl' Hall]".
      iExFalso. iApply heap_mapsto_dup_invalid; by iFrame "Hl Hl'".
    - iPvs (own_update with "Hown") as "Hown".
      by apply stackR_alloc.
      iDestruct "Hown" as "[Hown Hl']".
      iPvsIntro. iSplitR "Hl'"; [|unfold stack_mapsto, auth_own; trivial].
      iCombine "Hl" "Hall" as "Hall".
      unfold stack_owns. iFrame "Hown".
      rewrite big_sepM_insert; trivial.
  Qed.

  Lemma stack_owns_open h l v :
    stack_owns h ★ l ↦ˢᵗᵏ v
      ⊢ ghost_ownership.own stack_name (● h)
           ★ ([★ map] l ↦ v ∈ delete l h,
            match v with
            | DecAgree v' => l ↦ᵢ v'
            | DecAgreeBot => True
            end) ★ l ↦ᵢ v ★ l ↦ˢᵗᵏ v.
  Proof.
    iIntros "[[Hown Hall] Hl]".
    unfold stack_mapsto, auth_own.
    iCombine "Hown" "Hl" as "Hown".
    iDestruct (own_valid _ with "#Hown") as %Hvalid.
    iDestruct "Hown" as "[Hown Hl]".
    assert (Heq : h !! l = Some (DecAgree v)).
    eapply stackR_auth_is_subheap; eauto using lookup_singleton.
    rewrite -{1}(insert_id _ _ _ Heq) -insert_delete.
    rewrite big_sepM_insert; [|apply lookup_delete_None; auto].
    iDestruct "Hall" as "[$ $]"; by iFrame.
  Qed.

  Lemma stack_owns_close h l v :
    ghost_ownership.own stack_name (● h)
       ★ ([★ map] l ↦ v ∈ delete l h,
        match v with
        | DecAgree v' => l ↦ᵢ v'
        | DecAgreeBot => True
        end)
       ★ l ↦ᵢ v ★ l ↦ˢᵗᵏ v ⊢ stack_owns h ★ l ↦ˢᵗᵏ v.
  Proof.
    iIntros "[Hown [Hall [Hl Hl']]]".
    unfold stack_mapsto, auth_own.
    iCombine "Hown" "Hl'" as "Hown".
    iDestruct (own_valid _ with "#Hown") as %Hvalid.
    iDestruct "Hown" as "[Hown Hl']".
    assert (Heq : h !! l = Some (DecAgree v)).
    eapply stackR_auth_is_subheap; eauto using lookup_singleton.
    iCombine "Hl" "Hall" as "Hall".
    rewrite -(big_sepM_insert (λ l v,
        match v with
        | DecAgree v' => (l ↦ᵢ v')%I
        | DecAgreeBot => True%I
        end) _ _ (DecAgree v)); eauto using lookup_delete.
    rewrite insert_delete insert_id; auto using lookup_delete.
    unfold stack_owns. by iFrame.
  Qed.

  Lemma stack_owns_open_close h l v :
    stack_owns h ★ l ↦ˢᵗᵏ v
      ⊢ l ↦ᵢ v ★ (l ↦ᵢ v -★ (stack_owns h ★ l ↦ˢᵗᵏ v)).
  Proof.
    iIntros "[Howns Hls]".
    iDestruct (stack_owns_open with "[Howns Hls]") as "[Hh [Hm [Hl Hls]]]".
    { by iFrame "Howns Hls". }
    iFrame "Hl". iIntros "Hl".
    iApply stack_owns_close. by iFrame.
  Qed.

  Lemma stack_owns_later_open_close h l v :
    ▷ stack_owns h ★ l ↦ˢᵗᵏ v
      ⊢ ▷ (l ↦ᵢ v ★ (l ↦ᵢ v -★ (stack_owns h ★ l ↦ˢᵗᵏ v))).
  Proof. iIntros "H >". by iApply stack_owns_open_close. Qed.
End Rules.
