From iris.program_logic Require Import lifting.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Import ownership auth.
From iris_logrel.F_mu_ref_conc Require Export rules.
From iris.proofmode Require Import tactics weakestpre invariants.
Import uPred.

Definition specN := nroot .@ "spec".

(** The CMRA for the heap of the specification. *)
Definition tpoolUR : ucmraT := listUR (optionUR (exclR exprC)).

Definition to_tpool : list expr → tpoolUR := fmap (λ v, Excl' v).
Definition of_tpool : tpoolUR → list expr := omap (mbind (maybe Excl)).

Definition cfgUR := prodUR tpoolUR heapUR.

Definition of_cfg (ρ : cfgUR) : cfg lang := (of_tpool (ρ.1), of_heap (ρ.2)).
Definition to_cfg (ρ : cfg lang) : cfgUR := (to_tpool (ρ.1), to_heap (ρ.2)).

(** The CMRA for the thread pool. *)
Class cfgSG Σ :=
  CFGSG { cfg_inG :> authG lang Σ cfgUR; cfg_name : gname }.

Notation "cfg →⋆ cfg'" := (rtc step cfg cfg') (at level 20).

Section definitionsS.
  Context `{cfgSG Σ}.

  Definition heapS_mapsto (l : loc) (q : Qp) (v: val) : iPropG lang Σ :=
    auth_own cfg_name (∅ : tpoolUR, {[ l := (q, DecAgree v) ]}).

  Definition tpool_mapsto (j : nat) (e: expr) : iPropG lang Σ :=
    auth_own cfg_name ({[ j := Excl' e ]}, ∅ : heapUR).

  Definition spec_inv (ρ : cfg lang) (ρ' : cfgUR) : iPropG lang Σ :=
    (■ ρ →⋆ of_cfg ρ')%I.

  Definition spec_ctx (ρ : cfg lang) : iPropG lang Σ :=
    auth_ctx cfg_name specN (spec_inv ρ).

  Global Instance heapS_mapsto_timeless l q v : TimelessP (heapS_mapsto l q v).
  Proof. apply _. Qed.
  Global Instance spec_inv_Proper : Proper ((≡) ==> (≡) ==> (≡)) spec_inv.
  Proof. solve_proper. Qed.
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
  Implicit Types P Q : iPropG lang Σ.
  Implicit Types Φ : val → iPropG lang Σ.
  Implicit Types σ : state.
  Implicit Types g : heapUR.
  Implicit Types e : expr.
  Implicit Types v : val.

  (** Conversion to tpools and back *)
  Global Instance of_tpool_proper : Proper ((≡) ==> (=)) of_tpool.
  Proof. solve_proper. Qed.
  Lemma from_to_tpool l : of_tpool (to_tpool l) = l.
  Proof. induction l; trivial. simpl; f_equal; trivial. Qed.
  Lemma to_tpool_valid l : ✓ to_tpool l.
  Proof. by induction l; constructor. Qed.
  Global Instance of_cfg_proper : Proper ((≡) ==> (=)) of_cfg.
  Proof. solve_proper. Qed.
  Lemma from_to_cfg ρ : of_cfg (to_cfg ρ) = ρ.
  Proof.
    destruct ρ as [t h]; by rewrite /to_cfg /of_cfg /= from_to_tpool from_to_heap.
  Qed.
  Lemma to_cfg_valid ρ : ✓ to_cfg ρ.
  Proof. constructor; cbn; auto using to_tpool_valid, to_heap_valid. Qed.

  Global Instance step_proper : Proper ((≡) ==> (≡) ==> iff) (@step lang).
  Proof. by intros ??????; fold_leibniz; subst. Qed.

  Lemma tpool_update_validN n j e e' tp :
    ✓{n} ({[ j := Excl' e ]} ⋅ tp) → ✓{n} ({[ j := Excl' e' ]} ⋅ tp).
  Proof.
    rewrite !list_lookup_validN=> Htp i; move: Htp=> /(_ i).
    destruct (decide (j = i)); [subst|].
    - rewrite !list_lookup_op !list_lookup_singletonM.
      by case: (tp !! i)=> [[?|]|] //= => -[/exclusiveN_r ??].
    - rewrite !list_lookup_op.
      case (list_lookup_singletonM_ne j i (Excl' e)) => // ->;
      case (list_lookup_singletonM_ne j i (Excl' e')) => // ->;
      case (tp !! i)=>[?|] //; by rewrite -Some_op !left_id.
  Qed.

  Lemma tpool_update_valid j (e e' : expr) tp :
    ✓ ({[ j := Excl' e ]} ⋅ tp) → ✓ ({[ j := Excl' e' ]} ⋅ tp).
  Proof. rewrite !cmra_valid_validN; eauto using tpool_update_validN. Qed.

  Lemma cfg_valid_tpool_update j e e' hp ρ :
    ✓ (({[ j := Excl' e ]}, hp) ⋅ ρ : cfgUR) →
    ✓ (({[ j := Excl' e' ]}, hp) ⋅ ρ : cfgUR).
  Proof.
    intros [??]; constructor; naive_solver eauto using tpool_update_valid.
  Qed.

  Lemma of_tpool_singleton j e : of_tpool ({[ j := Excl' e ]}) = [e].
  Proof. induction j; simpl; auto. Qed.

  Lemma of_tpool_2_singletons j k e e' :
    j < k → of_tpool ({[ j := Excl' e ]} ⋅ {[ k := Excl' e' ]}) = [e; e'].
  Proof.
    revert k; induction j => k; destruct k; simpl; auto with omega => ?.
    - apply (f_equal (cons _)), of_tpool_singleton.
    - apply IHj; omega.
  Qed.

  Lemma of_tpool_app tp tp' :
    of_tpool (tp ++ tp') = of_tpool tp ++ of_tpool tp'.
  Proof.
    revert tp'; induction tp as [|x tp] => tp'; simpl; trivial.
    destruct x as [[x|]|]; simpl; rewrite IHtp; trivial.
  Qed.

  Lemma list_op_units k tp :
    of_tpool (replicate k ∅ ⋅ tp) = of_tpool tp.
  Proof.
    revert k; induction tp as [|x tp] => k.
    - destruct k; simpl; trivial. induction k; simpl; trivial.
    - destruct k; simpl; trivial. destruct x as [[?|]|]; by rewrite /= IHtp.
  Qed.

  Lemma tpool_conv j e tp :
    ✓ ({[ j := Excl' e ]} ⋅ tp) → ∃ l1 l2,
      (∀ e', of_tpool ({[ j := Excl' e' ]} ⋅ tp) = l1 ++ e' :: l2) ∧
      (∀ e' k e'',
        j < k → length tp < k →
        of_tpool ({[ j := Excl' e' ]} ⋅ {[ k := Excl' e'' ]} ⋅ tp) =
        l1 ++ e' :: l2 ++ [e'']).
  Proof.
    revert j. induction tp as [|t tp]=> j Hj.
    - exists [], []; split.
      + intros e'. clear Hj.
        induction j; simpl; trivial; simpl in *.
        rewrite ->(comm op) in IHj; trivial.
      + intros e' k e'' H1 H2; simpl in *. replace [] with (∅ : tpoolUR)
          by trivial; rewrite right_id.
        apply of_tpool_2_singletons; auto with omega.
    - destruct j as [j|]; simpl in *.
      + destruct t as [?|].
        { by move: Hj=> /Forall_cons [[/exclusive_r ? ?] ?]. }
        eexists [], (of_tpool tp); split; eauto.
        intros e' k e'' Hc1 Hc2. destruct k as [|k]; [omega|].
        simpl; apply (f_equal (cons _)). rewrite left_id.
        rewrite list_op_app ?replicate_length; last lia.
        by rewrite of_tpool_app list_op_units.
      + move: Hj=> /Forall_cons [Ht ?].
        destruct t as [[t|]|]; simpl in *.
        * edestruct IHtp as [l1 [l2 [Hl1 Hl2]]]; eauto.
          exists (t :: l1), l2; split.
          -- intros e'; rewrite Hl1; trivial.
          -- intros e' k e'' Hx1 Hx2. destruct k; simpl; auto with omega.
             apply (f_equal (cons _)), Hl2; auto with omega.
        * edestruct IHtp as [l1 [l2 [Hl1 Hl2]]]; eauto.
          exists l1, l2; split; trivial.
          intros e' k e'' Hx1 Hx2; destruct k; simpl; auto with omega.
          apply Hl2; auto with omega.
        * edestruct IHtp as [l1 [l2 [Hl1 Hl2]]]; eauto.
          exists l1, l2; split; trivial.
          intros e' k e'' Hx1 Hx2; destruct k; simpl; auto with omega.
          apply Hl2; auto with omega.
  Qed.

  Lemma thread_update j e e' h ρ :
    ✓ (({[j := Excl' e]}, h) ⋅ ρ) →
    ● (({[j := Excl' e]}, h) ⋅ ρ : cfgUR) ⋅ ◯ (({[j := Excl' e]}, h))
      ~~> ● (({[j := Excl' e']}, h) ⋅ ρ) ⋅ ◯ (({[j := Excl' e']}, h)).
  Proof.
    intros Hj. apply auth_update, prod_local_update; simpl; try done.
    by apply list_singleton_local_update, option_local_update, exclusive_local_update.
  Qed.

  Lemma singleton_tpoll_valid j e : ✓ ({[j := Some (1, DecAgree e)]}).
  Proof. induction j; simpl; repeat constructor; auto. Qed.

  Lemma tpool_valid_prepend_units_valid j (th : tpoolUR) :
    ✓ th → ✓ (replicate j ∅ ⋅ th).
  Proof.
    revert th; induction j => th Hj.
    - destruct th; inversion Hj; constructor; trivial.
    - destruct th; inversion Hj; constructor.
      + constructor.
      + by apply Forall_replicate.
      + rewrite left_id; trivial.
      + apply IHj; trivial.
  Qed.

  Lemma thread_alloc_safe k j (e e' : exprC) (tp : tpoolUR) :
    j < k → length tp < k →
    ✓ ({[j := Excl' e ]} ⋅ tp) →
    ✓ ({[j := Excl' e ]} ⋅ {[k := Excl' e' ]} ⋅ tp).
  Proof.
    intros H1 H2 H3.
    rewrite (comm op {[j := Excl' e]}) -assoc.
    rewrite list_op_app.
    - apply Forall_app ;split; [|repeat constructor; by auto].
      by apply tpool_valid_prepend_units_valid.
    - rewrite list_op_length list_singletonM_length replicate_length. lia.
  Qed.

  Lemma thread_alloc_update k j e e' h ρ :
    j < k → length (ρ.1) < k →
    ✓ (({[j := Excl' e ]}, h) ⋅ ρ) →
    ● (({[j := Excl' e ]}, h) ⋅ ρ : cfgUR) ⋅ ◯ ({[j := Excl' e]}, h)
      ~~> ● (({[j := Excl' e]} ⋅ {[k := Excl' e']}, h) ⋅ ρ)
           ⋅ ◯ ({[j := Excl' e]} ⋅ {[k := Excl' e']}, h).
  Proof.
    intros H1 H2 H3. apply auth_update, prod_local_update; simpl; last done.
    apply alloc_local_update=> n. by apply thread_alloc_safe.
  Qed.

  Lemma heap_alloc_safe l v h :
    ✓ h → h !! l = None →
    ✓ ({[l := (1%Qp, DecAgree v)]} ⋅ h : heapUR).
  Proof.
    intros H1 H2 i. rewrite lookup_op.
    destruct (decide (i = l)); subst.
    - rewrite H2 lookup_singleton; by repeat constructor.
    - by rewrite lookup_singleton_ne // left_id.
  Qed.

  Lemma heap_alloc_update l v th ρ :
    ✓ ((th, ∅) ⋅ ρ) → (ρ.2) !! l = None  →
    ● ((th, ∅) ⋅ ρ : cfgUR) ⋅ ◯ (th, ∅)
      ~~> ● ((th, {[l := (1%Qp, DecAgree v)]}) ⋅ ρ)
           ⋅ ◯ ((th, {[l := (1%Qp, DecAgree v)]})).
  Proof.
    intros H1 H2.
    apply auth_update, prod_local_update; simpl; first done.
    by apply alloc_unit_singleton_local_update.
  Qed.

  Lemma step_pure_base j K e e' h ρ :
    ✓ (({[j := Excl' (fill K e)]}, h) ⋅ ρ : cfgUR) →
    (∀ σ, head_step e σ e' σ None) →
    step (of_cfg (({[j := Excl' (fill K e)]}, h) ⋅ ρ))
         (of_cfg (({[j := Excl' (fill K e')]}, h) ⋅ ρ)).
  Proof.
    intros [H11 H12] H2; destruct ρ as [th hp]; simpl in *.
    rewrite !pair_op.
    destruct (tpool_conv _ _ _ H11) as [l1 [l2 [H3 _]]].
    unfold of_cfg; rewrite !H3.
    eapply (step_atomic _ _ _ _ _ _ None _ _); simpl.
    - trivial.
    - simpl; rewrite app_nil_r; trivial.
    - econstructor; eauto.
  Qed.

  Lemma step_pure E ρ j K e e' :
    (∀ σ, head_step e σ e' σ None) →
    nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K e ={E}=> j ⤇ fill K e'.
  Proof.
    iIntros {H1 H2} "[#Hspec Hj]".
    unfold spec_ctx, auth_ctx, tpool_mapsto, auth_own.
    iInv> specN as {ρ'} "[Hown #Hstep]".
    iCombine "Hj" "Hown" as "Hown".
    iDestruct (own_valid _ with "#Hown") as "Hvalid".
    iDestruct (auth_validI _ with "Hvalid") as "[Ha' %]";
      simpl; iClear "Hvalid".
    iDestruct "Ha'" as {ρ''} "Ha'"; iDestruct "Ha'" as %Ha'.
    rewrite ->(right_id _ _) in Ha'; setoid_subst.
    iDestruct "Hstep" as %Hstep.
    iPvs (own_update with "Hown") as "Hown".
    rewrite comm; apply thread_update; trivial.
    rewrite own_op; iDestruct "Hown" as "[H1 $]".
    iExists _; iSplitL; trivial.
    iPvsIntro; iPureIntro.
    eapply rtc_r; [exact Hstep|].
    eapply step_pure_base; trivial.
  Qed.

  Lemma step_alloc_base ρ j K e v :
    ✓ (({[j := Excl' (fill K (Alloc e))]}, ∅) ⋅ ρ) →
    to_val e = Some v →
    ∃ l, step
           (of_cfg (({[j := Excl' (fill K (Alloc e))]}, ∅) ⋅ ρ))
           (of_cfg (({[j := Excl' (fill K (Loc l))]}, ∅)
                      ⋅ (∅, ({[l := (1%Qp, DecAgree v)]})) ⋅ ρ))
         ∧ (ρ.2) !! l = None.
  Proof.
    intros H1 H2. destruct ρ as [tp th]; simpl.
    set (l := fresh (dom (gset positive) (of_heap th))). exists l.
    refine ((λ H, conj (_ H) H) _); [intros H3|].
    - rewrite !pair_op !left_id right_id.
      unfold of_cfg; simpl. destruct H1 as [H11 H12]; simpl in *.
      destruct (tpool_conv _ _ _ H11) as [l1 [l2 [H4 _]]]. repeat rewrite H4.
      rewrite of_heap_singleton_op.
      { eapply (step_atomic _ _ _ _ _ _ None _ _).
        - trivial.
        - simpl; rewrite app_nil_r; trivial.
        - econstructor; eauto. apply alloc_fresh; trivial. }
      apply heap_alloc_safe; trivial.
      revert H12; rewrite left_id; trivial.
    - destruct H1 as [H11 H12]; simpl in *; revert H12; rewrite left_id => H12.
      by eapply of_heap_None, (not_elem_of_dom (D := gset _)), is_fresh.
  Qed.

  Lemma step_alloc E ρ j K e v:
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (Alloc e) ={E}=> ∃ l, j ⤇ fill K (Loc l) ★ l ↦ₛ v.
  Proof.
    iIntros {H1 H2} "[#Hinv HΦ]".
    unfold spec_ctx, auth_ctx, tpool_mapsto, auth_own.
    iInv> specN as {ρ'} "[Hown #Hstep]".
    iCombine "HΦ" "Hown" as "Hown".
    iDestruct (own_valid _ with "#Hown") as "Hvalid".
    iDestruct (auth_validI _ with "Hvalid") as "[Ha' %]";
      simpl; iClear "Hvalid".
    iDestruct "Ha'" as {ρ''} "Ha'"; iDestruct "Ha'" as %Ha'.
    rewrite ->(right_id _ _) in Ha'; setoid_subst.
    iDestruct "Hstep" as %Hstep.
    edestruct step_alloc_base as [l [Hs Ho]]; eauto.
    iPvs (own_update with "Hown") as "Hown".
    rewrite comm; apply (thread_update _ _ (fill K (Loc l))); trivial.
    iPvs (own_update with "Hown") as "Hown".
    eapply (heap_alloc_update l v); trivial.
    eapply cfg_valid_tpool_update; eauto.
    rewrite pair_split.
    rewrite own_op; iDestruct "Hown" as "[H1 H2]".
    iSplitR "H2".
    - iExists _; iSplitL; trivial.
      iPvsIntro; iPureIntro.
      eapply rtc_r; [exact Hstep|]; trivial.
    - iPvsIntro. iExists _. rewrite -own_op; trivial.
  Qed.

  Lemma cfg_heap_update l v v' th ρ :
    ✓ ((th, {[l := (1%Qp, DecAgree v)]}) ⋅ ρ) →
    ● ((th, {[l := (1%Qp, DecAgree v)]}) ⋅ ρ : cfgUR)
       ⋅ ◯ (th, {[l := (1%Qp, DecAgree v)]})
      ~~> ● ((th, {[l := (1%Qp, DecAgree v')]}) ⋅ ρ)
           ⋅ ◯ (th, {[l := (1%Qp, DecAgree v')]}).
  Proof.
    intros Hl. apply auth_update, prod_local_update; simpl; first done.
    by apply singleton_local_update, exclusive_local_update.
  Qed.

  Lemma step_load_base ρ j K l q v :
    ✓ (({[j := Excl' (fill K (Load (Loc l)))]}, {[l := (q, DecAgree v)]}) ⋅ ρ) →
    step
      (of_cfg (({[j := Excl' (fill K (Load (Loc l)))]}, {[l := (q, DecAgree v)]}) ⋅ ρ))
      (of_cfg (({[j := Excl' (fill K (of_val v))]}, {[l := (q, DecAgree v)]}) ⋅ ρ)).
  Proof.
    destruct ρ as [tp th]; unfold of_cfg; simpl.
    intros [H11 H12]; simpl in *.
    destruct (tpool_conv _ _ _ H11) as [l1 [l2 [H2 _]]]. repeat rewrite H2.
    rewrite of_heap_singleton_op; trivial.
    eapply (step_atomic _ _ _ _ _ _ None _ _).
    - trivial.
    - simpl; rewrite app_nil_r; trivial.
    - econstructor; eauto. apply LoadS. apply lookup_insert.
  Qed.

  Lemma step_load E ρ j K l q v:
    nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (Load (Loc l)) ★ l ↦ₛ{q} v
      ={E}=> j ⤇ fill K (of_val v) ★ l ↦ₛ{q} v.
  Proof.
    iIntros {H1} "[#Hinv [Hj Hl]]".
    unfold spec_ctx, auth_ctx, tpool_mapsto, heapS_mapsto, auth_own.
    iInv> specN as {ρ'} "[Hown #Hstep]".
    iCombine "Hl" "Hown" as "Hown".
    iCombine "Hj" "Hown" as "Hown".
    iDestruct (own_valid _ with "#Hown") as %Hv%auth_valid_discrete.
    revert Hv; rewrite /= pair_op /= !left_id !right_id.
    intros [[ρ'' ->] ?].
    iDestruct "Hstep" as %Hstep.
    iPvs (own_update with "Hown") as "[H1 H2]".
    { rewrite assoc -auth_frag_op.
      rewrite -pair_split.
      rewrite comm; apply (thread_update _ _ (fill K (of_val v))); trivial. }
    iSplitR "H2".
    - iExists _; iSplitL; trivial.
      iPvsIntro. iPureIntro.
      eapply rtc_r; [exact Hstep|]. by apply step_load_base.
    - iPvsIntro. rewrite -own_op -auth_frag_op pair_op right_id left_id; trivial.
  Qed.

  Lemma step_store_base ρ j K l e v v' :
    to_val e = Some v' →
    ✓ (({[j := Excl' (fill K (Store (Loc l) e))]}, {[l := (1%Qp, DecAgree v)]}) ⋅ ρ) →
    step
      (of_cfg (({[j := Excl' (fill K (Store (Loc l) e))]}, {[l := (1%Qp, DecAgree v)]}) ⋅ ρ))
      (of_cfg (({[j := Excl' (fill K Unit)]}, {[l := (1%Qp, DecAgree v')]}) ⋅ ρ)).
  Proof.
    destruct ρ as [tp th]; unfold of_cfg; simpl.
    intros H1 [H21 H22]; simpl in *.
    destruct (tpool_conv _ _ _ H21) as [l1 [l2 [H3 _]]]. repeat rewrite H3.
    rewrite !of_heap_singleton_op; eauto using heap_store_valid.
    eapply (step_atomic _ _ _ _ _ _ None _ _).
    - trivial.
    - simpl; rewrite app_nil_r; trivial.
    - replace (<[l:=v']> (of_heap th)) with
      (<[l:=v']> (<[l:=v]> (of_heap th))) by (by rewrite insert_insert).
      econstructor; eauto.
      apply StoreS; trivial. eexists; apply lookup_insert.
  Qed.

  Lemma step_store E ρ j K l v' e v:
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (Store (Loc l) e) ★ l ↦ₛ v'
      ={E}=> j ⤇ fill K Unit ★ l ↦ₛ v.
  Proof.
    iIntros {H1 H2} "[#Hinv [Hj Hl]]".
    unfold spec_ctx, auth_ctx, tpool_mapsto, heapS_mapsto, auth_own.
    iInv> specN as {ρ'} "[Hown #Hstep]".
    iCombine "Hl" "Hown" as "Hown".
    iCombine "Hj" "Hown" as "Hown".
    iDestruct (own_valid _ with "#Hown") as %Hv%auth_valid_discrete.
    revert Hv; rewrite /= pair_op /= !left_id !right_id.
    intros [[ρ'' ->] ?].
    iDestruct "Hstep" as %Hstep.
    iPvs (own_update with "Hown") as "Hown".
    { rewrite assoc -auth_frag_op.
      rewrite -pair_split comm.
      by apply (thread_update _ _ (fill K Unit)). }
    iPvs (own_update with "Hown") as "[H1 H2]".
    { apply (cfg_heap_update _ _ v). eapply cfg_valid_tpool_update; eauto. }
    iSplitR "H2".
    - iExists _; iSplitL; trivial.
      iPvsIntro; iPureIntro.
      eapply rtc_r; [exact Hstep|]. by apply step_store_base.
    - iPvsIntro. rewrite -own_op -auth_frag_op pair_op right_id left_id; trivial.
  Qed.

  Lemma step_cas_fail_base ρ j K l q v' e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 →
    ✓ (({[j := Excl' (fill K (CAS (Loc l) e1 e2))]},
         {[l := (q, DecAgree v')]}) ⋅ ρ) →
    step
      (of_cfg (({[j := Excl' (fill K (CAS (Loc l) e1 e2))]},
                {[l := (q, DecAgree v')]}) ⋅ ρ))
      (of_cfg (({[j := Excl' (fill K (♭ false))]},
                {[l := (q, DecAgree v')]}) ⋅ ρ)).
  Proof.
    destruct ρ as [tp th]; unfold of_cfg; simpl.
    intros H1 H2 H3 [H41 H42]; simpl in *.
    destruct (tpool_conv _ _ _ H41) as [l1 [l2 [H5 _]]]. repeat rewrite H5.
    rewrite !of_heap_singleton_op; trivial.
    eapply (step_atomic _ _ _ _ _ _ None _ _).
    - trivial.
    - simpl; rewrite app_nil_r; trivial.
    - econstructor; eauto. eapply CasFailS; eauto. apply lookup_insert.
  Qed.

  Lemma step_cas_fail E ρ j K l q v' e1 v1 e2 v2:
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (CAS (Loc l) e1 e2) ★ ▷ ■ (v' ≠ v1) ★ l ↦ₛ{q} v'
      ={E}=> j ⤇ fill K (♭ false) ★ l ↦ₛ{q} v'.
  Proof.
    iIntros {H1 H2 H3} "[#Hinv [Hj [#Hneq Hl]]]".
    unfold spec_ctx, auth_ctx, tpool_mapsto, heapS_mapsto, auth_own.
    iInv> specN as {ρ'} "[Hown #Hstep]".
    iTimeless "Hneq". iDestruct "Hneq" as %Hneq.
    iCombine "Hl" "Hown" as "Hown".
    iCombine "Hj" "Hown" as "Hown".
    iDestruct (own_valid _ with "#Hown") as %Hv%auth_valid_discrete.
    revert Hv; rewrite /= pair_op /= !left_id !right_id.
    intros [[ρ'' ->] ?].
    iDestruct "Hstep" as %Hstep.
    iPvs (own_update with "Hown") as "[H1 H2]".
    { rewrite assoc -auth_frag_op.
      rewrite -pair_split comm.
      by apply (thread_update _ _ (fill K (♭ false))). }
    iSplitR "H2".
    - iExists _; iSplitL; trivial.
      iPvsIntro; iPureIntro; eauto.
      eapply rtc_r; [exact Hstep|]. by eapply step_cas_fail_base.
    - iPvsIntro. rewrite -own_op -auth_frag_op pair_op right_id left_id; trivial.
  Qed.

  Lemma step_cas_suc_base ρ j K l e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ✓ (({[j := Excl' (fill K (CAS (Loc l) e1 e2))]},
        {[l := (1%Qp, DecAgree v1)]}) ⋅ ρ) →
    step
      (of_cfg (({[j := Excl' (fill K (CAS (Loc l) e1 e2))]},
                {[l := (1%Qp, DecAgree v1)]}) ⋅ ρ))
      (of_cfg (({[j := Excl' (fill K (♭ true))]},
                {[l := (1%Qp, DecAgree v2)]}) ⋅ ρ)).
  Proof.
    destruct ρ as [tp th]; unfold of_cfg; simpl.
    intros H1 H2 [H31 H32]; simpl in *.
    destruct (tpool_conv _ _ _ H31) as [l1 [l2 [H4 _]]]. repeat rewrite H4.
    rewrite !of_heap_singleton_op; eauto using heap_store_valid.
    eapply (step_atomic _ _ _ _ _ _ None _ _).
    - trivial.
    - simpl; rewrite app_nil_r; trivial.
    - replace (<[l:=v2]> (of_heap th)) with
      (<[l:=v2]> (<[l:=v1]> (of_heap th))) by (by rewrite insert_insert).
      econstructor; eauto. eapply CasSucS; eauto. apply lookup_insert.
  Qed.

  Lemma step_cas_suc E ρ j K l e1 v1 v1' e2 v2:
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (CAS (Loc l) e1 e2) ★ ▷ ■ (v1 = v1') ★ l ↦ₛ v1'
      ={E}=> j ⤇ fill K (♭ true) ★ l ↦ₛ v2.
  Proof.
    iIntros {H1 H2 H3} "[#Hinv [Hj [#Heq Hl]]]".
    unfold spec_ctx, auth_ctx, tpool_mapsto, heapS_mapsto, auth_own.
    iInv> specN as {ρ'} "[Hown #Hstep]".
    iTimeless "Heq". iDestruct "Heq" as %Heq; subst.
    iCombine "Hl" "Hown" as "Hown".
    iCombine "Hj" "Hown" as "Hown".
    iDestruct (own_valid _ with "#Hown") as %Hv%auth_valid_discrete.
    revert Hv; rewrite /= pair_op /= !left_id !right_id.
    intros [[ρ'' ->] ?].
    iDestruct "Hstep" as %Hstep.
    iPvs (own_update with "Hown") as "Hown".
    { rewrite assoc -auth_frag_op.
      rewrite -pair_split comm.
      by apply (thread_update _ _ (fill K (♭ true))). }
    iPvs (own_update with "Hown") as "[H1 H2]".
    { apply (cfg_heap_update _ _ v2). by eapply cfg_valid_tpool_update. }
    iSplitR "H2".
    - iExists _; iSplitL; trivial.
      iPvsIntro; iPureIntro.
      eapply rtc_r; [exact Hstep|]. apply step_cas_suc_base; trivial.
    - iPvsIntro. rewrite -own_op -auth_frag_op pair_op right_id left_id; trivial.
  Qed.

  Lemma step_rec E ρ j K e1 e2 v :
    to_val e2 = Some v → nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (App (Rec e1) e2)
      ={E}=> j ⤇ fill K (e1.[Rec e1,e2/]).
  Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_tlam E ρ j K e :
    nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (TApp (TLam e)) ={E}=> j ⤇ fill K e.
  Proof. apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_Fold E ρ j K e v :
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (Unfold (Fold e)) ={E}=> j ⤇ fill K e.
  Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_fst E ρ j K e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (Fst (Pair e1 e2)) ={E}=> j ⤇ fill K e1.
  Proof. intros H1 H2; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_snd E ρ j K e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (Snd (Pair e1 e2)) ={E}=> j ⤇ fill K e2.
  Proof. intros H1 H2; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_case_inl E ρ j K e0 v0 e1 e2 :
    to_val e0 = Some v0 → nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (Case (InjL e0) e1 e2)
      ={E}=> j ⤇ fill K (e1.[e0/]).
  Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_case_inr E ρ j K e0 v0 e1 e2 :
    to_val e0 = Some v0 → nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (Case (InjR e0) e1 e2)
      ={E}=> j ⤇ fill K (e2.[e0/]).
  Proof. intros H1; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_if_false E ρ j K e1 e2 :
    nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (If (♭ false) e1 e2) ={E}=> j ⤇ fill K e2.
  Proof. apply step_pure => σ; econstructor. Qed.

  Lemma step_if_true E ρ j K e1 e2 :
    nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (If (♭ true) e1 e2) ={E}=> j ⤇ fill K e1.
  Proof. apply step_pure => σ; econstructor. Qed.

  Lemma step_nat_binop E ρ j K op a b :
    nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (BinOp op (♯ a) (♯ b))
      ={E}=> j ⤇ fill K (of_val (binop_eval op a b)).
  Proof. apply step_pure => σ; econstructor. Qed.

  Lemma step_fork_base k j K e h ρ :
    j < k → length (ρ.1) < k →
    ✓ (({[j := Excl' (fill K (Fork e))]}, h) ⋅ ρ) →
    step (of_cfg (({[j := Excl' (fill K (Fork e))]}, h) ⋅ ρ))
         (of_cfg (({[j := Excl' (fill K Unit)]} ⋅ {[k := Excl' e]}, h) ⋅ ρ)).
  Proof.
    intros Hl1 Hl2 [H11 H12]; destruct ρ as [th hp]; simpl in *.
    rewrite !pair_op /of_cfg /=.
    destruct (tpool_conv _ _ _ H11) as [l1 [l2 [H31 H32]]].
    rewrite H31 H32; trivial.
    eapply (step_atomic _ _ _ _ _ _ (Some _) _ _); simpl; trivial.
    econstructor; eauto. constructor.
  Qed.

  Lemma step_fork E ρ j K e :
    nclose specN ⊆ E →
    spec_ctx ρ ★ j ⤇ fill K (Fork e) ={E}=> ∃ j', j ⤇ fill K Unit ★ j' ⤇ e.
  Proof.
    iIntros {H1} "[#Hspec Hj]".
    unfold spec_ctx, auth_ctx, tpool_mapsto, auth_own.
    iInv> specN as {ρ'} "[Hown #Hstep]".
    iCombine "Hj" "Hown" as "Hown".
    iDestruct (own_valid _ with "#Hown") as %Hv%auth_valid_discrete.
    revert Hv; rewrite /= pair_op /= !left_id !right_id.
    intros [[ρ'' ->] ?].
    iDestruct "Hstep" as %Hstep.
    iPvs (own_update with "Hown") as "Hown".
    rewrite comm; apply (thread_update _ _ (fill K Unit)); trivial.
    set (k := S (max (length (ρ''.1)) j)).
    assert (Hx1 : k > j) by (unfold k; lia).
    assert (Hx2 : k > length (ρ''.1)) by (unfold k; lia).
    clearbody k.
    iPvs (own_update with "Hown") as "Hown".
    eapply (thread_alloc_update k _ _ e); trivial.
    - eapply cfg_valid_tpool_update; eauto.
    - rewrite own_op; iDestruct "Hown" as "[H1 H2]".
      iSplitR "H2"; trivial.
      + iExists _; iSplitL; trivial. iPvsIntro. iPureIntro.
        eapply rtc_r; [exact Hstep|]; eapply step_fork_base; trivial.
      + iPvsIntro. iExists _. by rewrite -own_op -auth_frag_op pair_op left_id.
  Qed.
End cfg.
