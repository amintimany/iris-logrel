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

  Global Instance tpool_Empty : Empty (fracR (dec_agreeR expr)).
  Proof. apply frac_empty. Defined.

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

    Notation "ρ →⋆ ρ'" := (Makes_Steps ρ ρ') (at level 20).

    Definition Spec_inv (ρ ρ' : cfgR) : iPropG lang Σ :=
      (■ (of_cfg ρ) →⋆ (of_cfg ρ'))%I.

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

  Notation "ρ →⋆ ρ'" := (Makes_Steps ρ ρ') (at level 20).

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

    Context`{icfg : cfgSG Σ}.

    Lemma tpool_update_validN n j e e' tp :
      ✓{n} ({[ j := (Frac 1 (DecAgree e : dec_agreeR _)) ]} ⋅ tp) →
      ✓{n} ({[ j := (Frac 1 (DecAgree e' : dec_agreeR _)) ]} ⋅ tp).
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

    Lemma tpool_update_valid j e e' tp :
      ✓ ({[ j := (Frac 1 (DecAgree e : dec_agreeR _)) ]} ⋅ tp) →
      ✓ ({[ j := (Frac 1 (DecAgree e' : dec_agreeR _)) ]} ⋅ tp).
    Proof.
      intros H.
      apply cmra_valid_validN => n; eapply cmra_valid_validN in H;
                                  eauto using tpool_update_validN.
    Qed.

    Global Instance prod_LocalUpdate
           {A B : cmraT} {Lv : A → Prop} (L : A → A) {LU : LocalUpdate Lv L}
           {Lv' : B → Prop} (L' : B → B) {LU' : LocalUpdate Lv' L'} :
      @LocalUpdate (prodR A B) (λ x, Lv (x.1) ∧ Lv' (x.2)) (prod_map L L').
    Proof.
      constructor.
      - intros n x1 x2 [Hx1 Hx2]; constructor; simpl; trivial;
        apply local_update_ne; trivial.
      - intros n [x1 x2] [y1 y2] [H11 H12] [H21 H22]; constructor;
          simpl in *; trivial;
        eapply local_updateN; eauto.
    Qed.

    Lemma of_tpool_singleton j e :
      of_tpool ({[ j := (Frac 1 (DecAgree e)) ]}) = [e].
    Proof. induction j; simpl; auto. Qed.

    Lemma of_tpool_2_singletons j k e e' :
      j < k →
      of_tpool ({[ j := (Frac 1 (DecAgree e)) ]}
                  ⋅ {[ k := (Frac 1 (DecAgree e')) ]}) = [e; e'].
    Proof.
      revert k; induction j => k; destruct k; simpl; auto with omega => H.
      - apply (f_equal (cons _)), of_tpool_singleton.
      - apply IHj; omega.
    Qed.

    Lemma of_tpool_app tp tp' :
      of_tpool (tp ++ tp') = of_tpool tp ++ of_tpool tp'.
    Proof.
      revert tp'; induction tp as [|x tp] => tp'; simpl; trivial.
      destruct x as [? [x|]|]; simpl; rewrite IHtp; trivial.
    Qed.

    Lemma list_op_units k tp :
      of_tpool (repeat ∅ k ⋅ tp) = of_tpool tp.
    Proof.
      revert k; induction tp as [|x tp] => k.
      - destruct k; simpl; trivial. induction k; simpl; trivial.
      - destruct k; simpl; trivial. destruct x as [? x|]; simpl; [|apply IHtp].
        destruct x; simpl; [|apply IHtp]. rewrite IHtp; trivial.
    Qed.

    Lemma tpool_conv j e tp :
      ✓ ({[ j := (Frac 1 (DecAgree e : dec_agreeR _)) ]} ⋅ tp) → ∃ l1 l2,
        (∀ e', of_tpool ({[ j := (Frac 1 (DecAgree e' : dec_agreeR _)) ]} ⋅ tp) =
               l1 ++ e' :: l2) ∧
        (∀ e' k e'',
            k > j → k > List.length tp →
            of_tpool
              ({[ j := (Frac 1 (DecAgree e' : dec_agreeR _)) ]}
                 ⋅ {[ k := (Frac 1 (DecAgree e'' : dec_agreeR _)) ]} ⋅ tp) =
            l1 ++ e' :: l2 ++ [e'']).
    Proof.
      revert j. induction tp as [|t tp]; intros j H.
      - exists []; exists []; split.
        + intros e'. clear H.
          induction j; simpl; trivial; simpl in *.
          rewrite list_op_nil in IHj; trivial.
        + intros e' k e'' H1 H2; simpl in *. replace [] with (∅ : tpoolR)
            by trivial; rewrite right_id.
          apply of_tpool_2_singletons; auto with omega.
      - destruct j; simpl in *.
        + inversion H; subst. rewrite (frac_valid_inv_l _ _ H2); simpl.
          eexists [], _; split.
          * intros e'; simpl; trivial.
          * intros e' k e'' Hc1 Hc2. destruct k; auto with omega.
            simpl; apply (f_equal (cons _)).
            set (W := @list_op_app); unfold op, cmra_op in W; simpl in W;
              rewrite W; clear W.
            rewrite of_tpool_app list_op_units; trivial.
            rewrite repeat_length.
            match type of Hc2 with
              _ > S ?A =>
              match goal with (* A and B are convertible! *)
                |- ?B ≤ _ => change B with A; omega
              end
            end.
        + inversion H; subst.
          destruct t as [q [t|]|]; simpl in *.
          * edestruct IHtp as [l1 [l2 [Hl1 Hl2]]]; eauto.
            exists (t :: l1), l2; split.
            -- intros e'; rewrite Hl1; trivial.
            -- intros e' k e'' Hx1 Hx2. destruct k; simpl; auto with omega.
               apply (f_equal (cons _)), Hl2; auto with omega.
          * inversion H2. inversion H1.
          * edestruct IHtp as [l1 [l2 [Hl1 Hl2]]]; eauto.
            exists l1, l2; split; trivial.
            intros e' k e'' Hx1 Hx2; destruct k; simpl; auto with omega.
            apply Hl2; auto with omega.
    Qed.
(*
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
*)
    Lemma thread_update j e e' h ρ :
      ✓ (({[j := Frac 1 (DecAgree e)]}, h) ⋅ ρ) →
      (● (({[j := Frac 1 (DecAgree e)]}, h) ⋅ ρ : cfgR)
        ⋅ ◯ (({[j := Frac 1 (DecAgree e)]}, h)))
        ~~> (● (({[j := Frac 1 (DecAgree e')]}, h) ⋅ ρ)
             ⋅ ◯ (({[j := Frac 1 (DecAgree e')]}, h))).
    Proof.
      intros H.
      replace ({[j := Frac 1 (DecAgree e')]} : tpoolR) with
      (alter (λ _ : fracR (dec_agreeR expr), Frac 1 (DecAgree e')) j
             {[j := Frac 1 (DecAgree e)]}) by (by rewrite list_alter_singleton).
      apply (@auth_local_update_l
               _ _ _ _ _
               (@prod_LocalUpdate _ heapR _ _ _ _ _ (local_update_id))).
      - split; trivial. eexists (Frac 1 _);
                          by rewrite list_Singleton_lookup; split.
      - simpl. rewrite list_alter_singleton.
        inversion H; constructor; simpl in *; trivial.
        eapply tpool_update_valid; eauto.
    Qed.

(*    Lemma thread_alloc_update j e e' h ρ :
      ✓ (({[j := Frac 1 (DecAgree e)]}, h) ⋅ ρ) →
      (● (({[j := Frac 1 (DecAgree e)]}, h) ⋅ ρ : cfgR)
        ⋅ ◯ (({[j := Frac 1 (DecAgree e)]}, h)))
        ~~> (● (({[j := Frac 1 (DecAgree e')]}, h) ⋅ ρ)
             ⋅ ◯ (({[j := Frac 1 (DecAgree e')]}, h))).
    Proof.
      intros H.
      replace ({[j := Frac 1 (DecAgree e')]} : tpoolR) with
      (alter (λ _ : fracR (dec_agreeR expr), Frac 1 (DecAgree e')) j
             {[j := Frac 1 (DecAgree e)]}) by (by rewrite list_alter_singleton).
      apply (@auth_local_update_l
               _ _ _ _ _
               (@prod_LocalUpdate _ heapR _ _ _ _ _ (local_update_id))).
      - split; trivial. eexists (Frac 1 _);
                          by rewrite list_Singleton_lookup; split.
      - simpl. rewrite list_alter_singleton.
        inversion H; constructor; simpl in *; trivial.
        eapply tpool_update_valid; eauto.
    Qed. *)

    Lemma step_pure_base j K e e' h ρ :
      ✓ (({[j := Frac 1 (DecAgree (fill K e))]}, h) ⋅ ρ : cfgR) →
      (∀ σ, head_step e σ e' σ None) →
      step (of_cfg (({[j := Frac 1 (DecAgree (fill K e))]}, h) ⋅ ρ))
           (of_cfg (({[j := Frac 1 (DecAgree (fill K e'))]}, h) ⋅ ρ)).
    Proof.
      intros [H11 H12] H2; destruct ρ as [th hp]; simpl in *.
      unfold op, cmra_op; simpl. unfold prod_op; simpl.
      unfold of_cfg; simpl.
      destruct (tpool_conv _ _ _ H11) as [l1 [l2 [H3 _]]].
      repeat rewrite H3.
      eapply (step_atomic _ _ _ _ _ _ None _ _); simpl.
      - trivial.
      - simpl; rewrite app_nil_r; trivial.
      - econstructor; eauto.
    Qed.

    Lemma step_pure N E ρ j K e e' :
      (∀ σ, head_step e σ e' σ None) →
      nclose N ⊆ E →
      (Spec_ctx N ρ ★ j ⤇ (fill K e)%I) ⊢ |={E}=>(j ⤇ (fill K e'))%I.
    Proof.
      intros H1 H2.
      iIntros "[#Hspec Hj]".
      unfold Spec_ctx, auth_ctx, tpool_mapsto, auth_own.
      iInv> N as {ρ'} "[Hown #Hstep]".
      iCombine "Hj" "Hown" as "Hown".
      iDestruct (own_valid _ with "Hown !") as "Hvalid".
      iDestruct (auth_validI _ with "Hvalid") as "[Ha' %]";
        simpl; iClear "Hvalid".
      iDestruct "Ha'" as {ρ''} "Ha'"; iDestruct "Ha'" as %Ha'.
      rewrite ->(right_id _ _) in Ha'; setoid_subst.
      iDestruct "Hstep" as %Hstep.
      iPvs (own_update with "Hown") as "Hown".
      rewrite cmra_comm; apply thread_update; trivial.
      rewrite own_op; iDestruct "Hown" as "[H1 H2]".
      iSplitR "H2"; trivial.
      iExists _; iSplitL; trivial.
      iPvsIntro.
      iApply const_intro; eauto.
      eapply rt_trans; [exact Hstep|].
      apply rt_step. apply step_pure_base; trivial.
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
      destruct (tpool_conv _ _ _ H11) as [l1 [l2 [H3 _]]].
      repeat rewrite H3.
      rewrite of_heap_singleton_op.
      { eapply (step_atomic _ _ _ _ _ _ None _ _).
        - trivial.
        - simpl; rewrite app_nil_r; trivial.
        - econstructor; eauto. apply alloc_fresh; trivial. }
      admit.
    Admitted.

    Lemma step_alloc N E ρ j K e v:
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
      admit.
    Admitted.

    Lemma step_load N E ρ j K l q v:
      nclose N ⊆ E →
      ((Spec_ctx N ρ ★ j ⤇ (fill K (Load (Loc l))) ★ l ↦ₛ{q} v)%I)
        ⊢ |={E}=>(j ⤇ (fill K (of_val v)) ★ l ↦ₛ{q} v)%I.
    Proof.
      iIntros {H1} "[#Hinv [Hj Hl]]".
      unfold Spec_ctx, auth_ctx, tpool_mapsto, auth_own.
      iInv> N as {ρ'} "[Hown #Hstep]".
      iCombine "HΦ" "Hown" as "Hown".
      iDestruct (own_valid _ with "Hown !") as "Hvalid".
      iDestruct (auth_validI _ with "Hvalid") as "[Ha' %]";
        simpl; iClear "Hvalid".
      iDestruct "Ha'" as {ρ''} "Ha'"; iDestruct "Ha'" as %Ha'.
      rewrite ->(right_id _ _) in Ha'; setoid_subst.
      iDestruct "Hstep" as %Hstep.
    Admitted.

    Lemma step_store N E ρ j K l v' e v:
      to_val e = Some v → nclose N ⊆ E →
      ((Spec_ctx N ρ ★ j ⤇ (fill K (Store (Loc l) e)) ★ l ↦ₛ v')%I)
        ⊢ |={E}=>(j ⤇ (fill K Unit) ★ l ↦ₛ v)%I.
    Proof.
    Admitted.

    Lemma step_cas_fail N E ρ j K l q v' e1 v1 e2 v2:
      to_val e1 = Some v1 → to_val e2 = Some v2 → nclose N ⊆ E →
      ((Spec_ctx N ρ ★ j ⤇ (fill K (CAS (Loc l) e1 e2))
                 ★ ▷ (■ (v' ≠ v1)) ★ l ↦ₛ{q} v')%I)
        ⊢ |={E}=>(j ⤇ (fill K (FALSE)) ★ l ↦ₛ{q} v')%I.
    Proof.
      iIntros {H1 H2 H3} "[#Hinv [Hj [#Hneq Hpt]]]".
      unfold Spec_ctx, auth_ctx, tpool_mapsto, auth_own.
      iInv> N as {ρ'} "[Hown #Hstep]".
      iTimeless "Hneq". iDestruct "Hneq" as %Hneq.
    Admitted.

    Lemma step_cas_suc N E ρ j K l e1 v1 v1' e2 v2:
      to_val e1 = Some v1 → to_val e2 = Some v2 → nclose N ⊆ E →
      ((Spec_ctx N ρ ★ j ⤇ (fill K (CAS (Loc l) e1 e2))
                 ★ ▷ (■ (v1 = v1')) ★ l ↦ₛ v1')%I)
        ⊢ |={E}=>(j ⤇ (fill K (TRUE)) ★ l ↦ₛ v2)%I.
    Proof.
      iIntros {H1 H2 H3} "[#Hinv [Hj [#Heq Hpt]]]".
      unfold Spec_ctx, auth_ctx, tpool_mapsto, auth_own.
      iInv> N as {ρ'} "[Hown #Hstep]".
      iTimeless "Heq". iDestruct "Heq" as %Heq; subst.
    Admitted.

    Lemma step_lam N E ρ j K e1 e2 v :
      to_val e2 = Some v → nclose N ⊆ E →
      (Spec_ctx N ρ ★ j ⤇ (fill K (App (Lam e1) e2))%I)
        ⊢ |={E}=>(j ⤇ (fill K ((e1.[e2/]))))%I.
    Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

    Lemma step_Tlam N E ρ j K e :
      nclose N ⊆ E →
      (Spec_ctx N ρ ★ j ⤇ (fill K (TApp (TLam e)))%I)
        ⊢ |={E}=>(j ⤇ (fill K (e)))%I.
    Proof. apply step_pure => σ; econstructor; eauto. Qed.

    Lemma step_Fold N E ρ j K e v :
      to_val e = Some v → nclose N ⊆ E →
      (Spec_ctx N ρ ★ j ⤇ (fill K (Unfold (Fold e)))%I)
        ⊢ |={E}=>(j ⤇ (fill K e))%I.
    Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

    Lemma step_fst N E ρ j K e1 v1 e2 v2 :
      to_val e1 = Some v1 → to_val e2 = Some v2 → nclose N ⊆ E →
      (Spec_ctx N ρ ★ j ⤇ (fill K (Fst (Pair e1 e2)))%I)
        ⊢ |={E}=>(j ⤇ (fill K e1))%I.
    Proof. intros H1 H2; apply step_pure => σ; econstructor; eauto. Qed.

    Lemma step_snd N E ρ j K e1 v1 e2 v2 :
      to_val e1 = Some v1 → to_val e2 = Some v2 → nclose N ⊆ E →
      (Spec_ctx N ρ ★ j ⤇ (fill K (Snd (Pair e1 e2)))%I)
        ⊢ |={E}=>(j ⤇ (fill K e2))%I.
    Proof. intros H1 H2; apply step_pure => σ; econstructor; eauto. Qed.

    Lemma step_case_inl N E ρ j K e0 v0 e1 e2 :
      to_val e0 = Some v0 → nclose N ⊆ E →
      ((Spec_ctx N ρ ★ j ⤇ (fill K (Case (InjL e0) e1 e2)))%I)
        ⊢ |={E}=>(j ⤇ (fill K (e1.[e0/])))%I.
    Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

    Lemma step_case_inr N E ρ j K e0 v0 e1 e2 :
      to_val e0 = Some v0 → nclose N ⊆ E →
      ((Spec_ctx N ρ ★ j ⤇ (fill K (Case (InjR e0) e1 e2)))%I)
        ⊢ |={E}=>(j ⤇ (fill K (e2.[e0/])))%I.
    Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

    Lemma step_fork N E ρ j K e :
      nclose N ⊆ E →
      ((Spec_ctx N ρ ★ j ⤇ (fill K (Fork e)))%I)
        ⊢ |={E}=>(∃ j', j ⤇ (fill K (Unit)) ★ j' ⤇ (fill K e))%I.
    Proof.
    Admitted.

  End cfg.

End lang_rules.

Notation "l ↦ₛ{ q } v" :=
  (heapS_mapsto l q v)
    (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : uPred_scope.
Notation "l ↦ₛ v" := (heapS_mapsto l 1 v) (at level 20) : uPred_scope.

Notation "j ⤇{ q } e" :=
  (tpool_mapsto j q e)
    (at level 20, q at level 50, format "j  ⤇{ q }  e") : uPred_scope.
Notation "j ⤇ e" := (tpool_mapsto j 1 e) (at level 20) : uPred_scope.