From iris.proofmode Require Import invariants ghost_ownership tactics.
From iris_logrel.F_mu_ref_par Require Import lang rules logrel_binary.
From iris.algebra Require Import gmap dec_agree auth upred_big_op.
From iris.program_logic Require Import ownership auth.
Import uPred.

Definition stackR : cmraT := gmapR loc (dec_agreeR val).

Lemma stackR_self_op (h : stackR) : h ≡ h ⋅ h.
Proof.
  intros i. rewrite lookup_op.
  match goal with
    |- ?A ≡ ?B ⋅ ?B => change B with A; destruct A as [c|]
  end; trivial.
  destruct c as [c|]; cbv -[equiv decide];
    try destruct decide; trivial; tauto.
Qed.

Class stackG Σ :=
  StackG {
      stack_inG :> authG lang Σ stackR;
      stack_name : gname
    }.

Section Rules.
  Context {Σ : gFunctors} {istk : stackG Σ}.

  Definition stack_mapsto (l : loc) (v: val) : iPropG lang Σ :=
    auth_own stack_name ({[ l := (DecAgree v) ]}).

  Notation "l ↦ˢᵗᵏ v" := (stack_mapsto l v) (at level 20) : uPred_scope.

  Lemma stack_mapsto_dup l v : True%I ⊢ (l ↦ˢᵗᵏ v -★ (l ↦ˢᵗᵏ v ★ l ↦ˢᵗᵏ v))%I.
  Proof.
    iIntros "H".
    unfold stack_mapsto, auth_own.
    rewrite -own_op -auth_frag_op.
    rewrite -stackR_self_op; trivial.
  Qed.

  Program Definition StackLink_pre (Q : bivalC -n> iPropG lang Σ)
    {HQ : BiVal_to_IProp_Persistent Q} :
    (bivalC -n> iPropG lang Σ) -n> bivalC  -n> iPropG lang Σ :=
    {|
      cofe_mor_car :=
        λ P,
        {|
          cofe_mor_car :=
            λ v, (∃ l w, v.1 = LocV l ★ l ↦ˢᵗᵏ w ★
                                    ((w = InjLV UnitV ∧
                                      v.2 = FoldV (InjLV UnitV)) ∨
                                     (∃ y1 z1 y2 z2,
                                         (w = InjRV (PairV y1 (FoldV z1)))
                                           ★ (v.2 = FoldV (InjRV (PairV y2 z2)))
                                           ★ Q (y1, y2) ★ ▷ P(z1, z2)
                                     )
                                    )
                 )%I
        |}
    |}.
  Next Obligation.
  Proof.
    intros Q HQ P n [v1 v2] [w1 w2] [Hv1 Hv2]; simpl in *;
      by rewrite Hv1 Hv2.
  Qed.
  Next Obligation.
  Proof.
    intros Q HQ n P1 P2 HP v; simpl in *.
    repeat (apply exist_ne => ?). repeat apply sep_ne; trivial.
    rewrite or_ne; trivial. repeat (apply exist_ne => ?).
      by rewrite HP.
  Qed.

  Global Instance StackLink_pre_contractive Q {HQ} :
    Contractive (@StackLink_pre Q HQ).
  Proof.
    intros n P1 P2 HP v; simpl. repeat (apply exist_ne => ?).
    repeat apply sep_ne; trivial. rewrite or_ne; trivial.
    repeat (apply exist_ne => ?).
    repeat apply sep_ne; trivial.
    apply later_contractive => i H. by apply HP.
  Qed.

  Definition StackLink Q {HQ} := fixpoint (@StackLink_pre Q HQ).

  Lemma StackLink_unfold Q {HQ} v :
    @StackLink Q HQ v ≡
               (∃ l w, v.1 = LocV l ★ l ↦ˢᵗᵏ w ★
                                  ((w = InjLV UnitV ∧
                                    v.2 = FoldV (InjLV UnitV)) ∨
                                   (∃ y1 z1 y2 z2,
                                       (w = InjRV (PairV y1 (FoldV z1)))
                                         ★ (v.2 = FoldV (InjRV (PairV y2 z2)))
                                         ★ Q (y1, y2)
                                         ★ ▷ @StackLink Q HQ (z1, z2)
                                   )
                                  )
               )%I.
  Proof.
    unfold StackLink at 1.
    rewrite fixpoint_unfold; trivial.
  Qed.

  Global Opaque StackLink. (* So that we can only use the unfold above. *)

  Lemma StackLink_dup_lem Q {HQ}:
    True%I ⊢ (∀ v, @StackLink Q HQ v -★ @StackLink Q HQ v ★ @StackLink Q HQ v)%I.
  Proof.
    etrans; [|apply löb].
    iIntros "Hlat".
    rewrite later_forall.
    iIntros {v} "H".
    rewrite StackLink_unfold.
    iDestruct "H" as {l w} "[% [Hl Hr]]"; subst.
    iPoseProof (stack_mapsto_dup with "[Hl]") as "Hl'"; eauto.
    iDestruct "Hl'" as "[Hl1 Hl2]".
    iDestruct "Hr" as "[#Hr|Hr]".
    {
      iSplitL "Hl1".
      - iExists _, _; iFrame "Hl1"; iSplitL; trivial; iLeft; trivial.
      - iExists _, _; iFrame "Hl2"; iSplitL; trivial; iLeft; trivial.
    }
    {
      iDestruct "Hr" as {y1 z1 y2 z2} "[#H1 [#H2 [#HQ H']]]".
      iPoseProof ("Hlat" $! (z1, z2)) as "Hlat".
      rewrite later_wand.
      iPoseProof ("Hlat" with "H'") as "Hlat".
      rewrite later_sep. iDestruct "Hlat" as "[HS1 HS2]".
      iSplitL "Hl1 HS1".
      - iExists _, _; iFrame "Hl1"; iSplitR; trivial.
        iRight. iExists _, _, _, _; repeat iSplitR; trivial.
      - iExists _, _; iFrame "Hl2"; iSplitR; trivial.
        iRight. iExists _, _, _, _; repeat iSplitR; trivial.
    }
  Qed.

  Lemma StackLink_dup Q {HQ} v :
    @StackLink Q HQ v ⊢ (@StackLink Q HQ v ★ @StackLink Q HQ v)%I.
  Proof. iIntros "H"; by iApply StackLink_dup_lem. Qed.

  Lemma stackR_valid (h : stackR) (i : loc) :
    ✓ h → h !! i = None ∨ ∃ v, h !! i = Some (DecAgree v).
  Proof.
    intros H; specialize (H i).
    match type of H with
      ✓ ?A => match goal with
             | |- ?B = _ ∨ (∃ _, ?C = _) =>
               change B with A; change C with A;
                 destruct A as [[c|]|]; inversion H; eauto
             end
    end.
  Qed.

  Lemma stackR_alloc (h : stackR) (i : loc) (v : val) :
    h !! i = None → (● h) ~~> (● (<[i := DecAgree v]> h)
                               ⋅ ◯ {[i := DecAgree v]}).
  Proof.
    intros H1 n z H2. rewrite (insert_singleton_op h); auto.
    destruct z as [[ze | |] zo];
      unfold validN, cmra_validN in *; simpl in *; trivial.
    destruct H2 as [H21 H22]; split.
    - destruct H21 as [u H21].
      eexists ({[i := DecAgree v]} ⋅ u). rewrite H21.
      rewrite ?cmra_unit_left_id.
      rewrite ?assoc.
      rewrite (comm _ _ zo). apply cmra_op_ne'; trivial.
      rewrite -assoc. by rewrite -stackR_self_op.
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

  Lemma option_dec_agree_equiv_eq (x y : option (dec_agreeR val)) :
    x ≡ y → x = y.
  Proof.
    intros H1.
    destruct x as [[x|]|]; destruct y as [[y|]|]; cbv in H1;
      inversion H1; subst; auto with f_equal.
  Qed.

  Lemma dec_agree_valid_op_eq (x y : dec_agreeR val) :
    ✓ (Some x ⋅ Some y) → x = y.
  Proof.
    intros H1.
    destruct x as [x|]; destruct y as [y|]; trivial;
      cbv -[decide] in H1; try destruct decide; subst; simpl; intuition trivial.
  Qed.

  Lemma stackR_auth_is_subheap (h h' : stackR) :
    ✓ (● h ⋅ ◯ h') → ∀ i x, h' !! i = Some x → h !! i = Some x.
  Proof.
    intros H1 i x H2.
    destruct H1 as [H11 H12]; simpl in H11.
    specialize (H11 1).
    destruct H11 as [z H11].
    revert H11; rewrite cmra_unit_left_id => H11.
    eapply cmra_extend in H11; [| by apply cmra_valid_validN].
    destruct H11 as [[z1 z2] [H31 [H32 H33]]]; simpl in *.
    specialize (H32 i).
    assert (H4 : ✓ (z1 ⋅ z2))by (by rewrite -H31).
    apply option_dec_agree_equiv_eq.
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
      inversion H1; subst.
      destruct x as [x|]; cbv -[decide]; try destruct decide;
        constructor; intuition trivial.
    - inversion H1; subst. constructor; trivial.
  Qed.

  Context {iI : heapIG Σ}.

  Definition stack_owns (h : stackR) :=
    (
      (ghost_ownership.own stack_name (● h))
        ★ Π★{map h} (λ l v, match v with
                            | DecAgree v' => l ↦ᵢ v'
                            | _ => True
                            end)
    )%I.

  Lemma stack_owns_alloc E h l v :
    ((stack_owns h ★ l ↦ᵢ v)%I)
      ⊢ |={E}=> (stack_owns (<[l := DecAgree v]> h) ★ l ↦ˢᵗᵏ v)%I.
  Proof.
    iIntros "[[Hown Hall] Hl]".
    iDestruct (own_valid _ with "Hown !") as "Hvalid".
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
    - rewrite <- (insert_delete _ _ _ Heq).
      rewrite big_sepM_insert; [|apply lookup_delete_None; auto].
      iDestruct "Hall" as "[Hl' Hall]".
      iExFalso. iApply heap_mapsto_dup_invalid; by iFrame "Hl Hl'".
    - iPvs (own_update with "Hown") as "Hown".
      by apply stackR_alloc.
      rewrite own_op. iDestruct "Hown" as "[Hown Hl']".
      iPvsIntro. iSplitR "Hl'"; [|unfold stack_mapsto, auth_own; trivial].
      iCombine "Hl" "Hall" as "Hall".
      unfold stack_owns. iFrame "Hown".
      rewrite big_sepM_insert; trivial.
  Qed.

  Lemma stack_owns_open h l v :
    ((stack_owns h ★ l ↦ˢᵗᵏ v)%I)
      ⊢ ((ghost_ownership.own stack_name (● h))
           ★ Π★{map delete l h}
           (λ l v,
            match v with
            | DecAgree v' => l ↦ᵢ v'
            | DecAgreeBot => True
            end)
           ★ l ↦ᵢ v ★ l ↦ˢᵗᵏ v)%I.
  Proof.
    iIntros "[[Hown Hall] Hl]".
    unfold stack_mapsto, auth_own.
    iCombine "Hown" "Hl" as "Hown".
    iDestruct (own_valid _ with "Hown !") as "Hvalid".
    iDestruct "Hvalid" as %Hvalid.
    rewrite own_op. iDestruct "Hown" as "[Hown Hl]".
    assert (Heq : h !! l = Some (DecAgree v)).
    eapply stackR_auth_is_subheap; eauto using lookup_singleton.
    rewrite <- (insert_delete _ _ _ Heq).
    rewrite big_sepM_insert; [|apply lookup_delete_None; auto].
    iDestruct "Hall" as "[Hl' Hall]".
    iFrame "Hl' Hown Hl". rewrite delete_insert; auto using lookup_delete.
  Qed.

  Lemma stack_owns_close h l v :
    ((ghost_ownership.own stack_name (● h))
       ★ Π★{map delete l h}
       (λ l v,
        match v with
        | DecAgree v' => l ↦ᵢ v'
        | DecAgreeBot => True
        end)
       ★ l ↦ᵢ v ★ l ↦ˢᵗᵏ v)%I ⊢ ((stack_owns h ★ l ↦ˢᵗᵏ v)%I).
  Proof.
    iIntros "[Hown [Hall [Hl Hl']]]".
    unfold stack_mapsto, auth_own.
    iCombine "Hown" "Hl'" as "Hown".
    iDestruct (own_valid _ with "Hown !") as "Hvalid".
    iDestruct "Hvalid" as %Hvalid.
    rewrite own_op. iDestruct "Hown" as "[Hown Hl']".
    assert (Heq : h !! l = Some (DecAgree v)).
    eapply stackR_auth_is_subheap; eauto using lookup_singleton.
    iCombine "Hl" "Hall" as "Hall".
    rewrite -(big_sepM_insert (λ l v,
        match v with
        | DecAgree v' => (l ↦ᵢ v')%I
        | DecAgreeBot => True%I
        end) _ _ (DecAgree v)); eauto using lookup_delete.
    rewrite insert_delete; auto using lookup_delete.
    unfold stack_owns. by iFrame "Hown Hl' Hall".
  Qed.

End Rules.