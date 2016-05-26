From iris.proofmode Require Import invariants ghost_ownership tactics.
From F_mu_ref_par Require Import lang examples.lock typing
     logrel_binary fundamental_binary rules_binary rules.
From iris.algebra Require Import gmap dec_agree auth.
From iris.program_logic Require Import ownership auth.
Import uPred.

Definition stackR : cmraT := gmapR loc (dec_agreeR val).

Class stackG Σ :=
  StackG {
      stack_inG :> authG lang Σ stackR;
      stack_name : gname
    }.

Section Rules.
  Context {Σ : gFunctors} {istk : stackG Σ}.

  Lemma stackR_self_op (h : stackR) : h ≡ h ⋅ h.
  Proof.
    intros i. rewrite lookup_op.
    match goal with
      |- ?A ≡ ?B ⋅ ?B => change B with A; destruct A as [c|]
    end; trivial.
    destruct c as [c|];
      unfold op, cmra_op; simpl;
          unfold op, cmra_op; simpl; trivial;
            destruct decide; trivial; tauto.
  Qed.

  Lemma stackR_get_auth (h : stackR) : (● h) ~~> (● h ⋅ ◯ h).
  Proof.
    intros n z H1. destruct z as [[ze | |] zo];
    unfold validN, cmra_validN in *; simpl in *; trivial.
    destruct H1 as [H1 H2]; split; trivial.
    destruct H1 as [u H1].
    eexists u. rewrite H1.
    rewrite ?cmra_unit_left_id.
    rewrite -assoc.
      by rewrite -stackR_self_op.
  Qed.

  Lemma dec_agree_valid_op_eq (x y : dec_agreeR val) :
    ✓ (Some x ⋅ Some y) → x = y.
  Proof.
    intros H1.
    destruct x as [x|]; destruct y as [y|]; trivial;
      cbv -[decide] in H1; try destruct decide; subst; simpl; intuition trivial.
  Qed.

  Lemma stackR_auth_is_subheap (h h' : stackR) :
    ✓ (● h ⋅ ◯ h') → ∀ i x, h' !! i ≡ Some x → h !! i ≡ Some x.
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

  Lemma stackR_alloc (h : stackR) (i : loc) (v : val) :
    h !! i = None → (● h) ~~> (● ({[i := DecAgree v]} ⋅ h)).
  Proof.
    intros H1 n z H2.
    destruct z as [[ze | |] zo];
      unfold validN, cmra_validN in *; simpl in *; trivial.
    destruct H2 as [H21 H22]; split.
    - destruct H21 as [u H21].
      eexists ({[i := DecAgree v]} ⋅ u). rewrite H21.
      rewrite ?cmra_unit_left_id.
      rewrite ?assoc.
      by rewrite (comm _ zo).
    - intros j. rewrite lookup_op.
      destruct (decide (i = j)) as [|Hneq]; subst.
      + rewrite H1. rewrite lookup_singleton; constructor.
      + rewrite lookup_singleton_ne; trivial.
        specialize (H22 j).
        revert H22.
        match goal with
          |- ✓{_} ?B → ✓{_} (_ ⋅ ?A) =>
          change B with A; destruct A; by try constructor
        end.
  Qed.

End Rules.