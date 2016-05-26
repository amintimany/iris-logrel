Require Import Coq.Logic.Eqdep_dec.
Require Import iris.proofmode.invariants iris.proofmode.weakestpre
        iris.proofmode.tactics.
Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.auth iris.algebra.dec_agree iris.algebra.frac
        iris.algebra.upred_big_op.
Require Import F_mu_ref_par.lang F_mu_ref_par.typing F_mu_ref_par.rules_binary
        F_mu_ref_par.rules F_mu_ref_par.logrel_binary
        F_mu_ref_par.fundamental_binary.
Require Import iris.program_logic.adequacy.
Import uPred.

Inductive context_item : Type :=
| CTX_Lam
| CTX_AppL (e2 : expr)
| CTX_AppR (e1 : expr)
(* Products *)
| CTX_PairL (e2 : expr)
| CTX_PairR (e1 : expr)
| CTX_Fst
| CTX_Snd
(* Sums *)
| CTX_InjL
| CTX_InjR
| CTX_CaseL (e1 : expr) (e2 : expr)
| CTX_CaseM (e0 : expr) (e2 : expr)
| CTX_CaseR (e0 : expr) (e1 : expr)
(* Nat bin op *)
| CTX_NBOPL (op : NatBinOP) (e2 : expr)
| CTX_NBOPR (op : NatBinOP) (e1 : expr)
(* If *)
| CTX_IfL (e1 : expr) (e2 : expr)
| CTX_IfM (e0 : expr) (e2 : expr)
| CTX_IfR (e0 : expr) (e1 : expr)
(* Recursive Types *)
| CTX_Fold
| CTX_Unfold
(* Polymorphic Types *)
| CTX_TLam
| CTX_TApp
(* Concurrency *)
| CTX_Fork
(* Reference Types *)
| CTX_Alloc
| CTX_Load
| CTX_StoreL (e2 : expr)
| CTX_StoreR (e1 : expr)
(* Compare and swap used for fine-grained concurrency *)
| CTX_CAS_L (e1 : expr) (e2 : expr)
| CTX_CAS_M (e0 : expr) (e2 : expr)
| CTX_CAS_R (e0 : expr) (e1 : expr).

Fixpoint fill_ctx_item (ctx : context_item) (e : expr) : expr :=
  match ctx with
  | CTX_Lam => Lam e
  | CTX_AppL e2 => App e e2
  | CTX_AppR e1 => App e1 e
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst => Fst e
  | CTX_Snd => Snd e
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL e1 e2 => Case e e1 e2
  | CTX_CaseM e0 e2 => Case e0 e e2
  | CTX_CaseR e0 e1 => Case e0 e1 e
  | CTX_NBOPL op e2 => NBOP op e e2
  | CTX_NBOPR op e1 => NBOP op e1 e
  | CTX_IfL e1 e2 => If e e1 e2
  | CTX_IfM e0 e2 => If e0 e e2
  | CTX_IfR e0 e1 => If e0 e1 e
  | CTX_Fold => Fold e
  | CTX_Unfold => Unfold e
  | CTX_TLam => TLam e
  | CTX_TApp => TApp e
  | CTX_Fork => Fork e
  | CTX_Alloc => Alloc e
  | CTX_Load => Load e
  | CTX_StoreL e2 => Store e e2
  | CTX_StoreR e1 => Store e1 e
  | CTX_CAS_L e1 e2 => CAS e e1 e2
  | CTX_CAS_M e0 e2 => CAS e0 e e2
  | CTX_CAS_R e0 e1 => CAS e0 e1 e
  end.

Definition context := list context_item.

Definition fill_ctx K e := foldr fill_ctx_item e K.

Local Open Scope bin_logrel_scope.

(** typed context *)
Inductive typed_context_item :
  context_item → (list type) → type → (list type) → type → Prop :=
| TP_CTX_Lam : ∀ Γ τ τ',
    typed_context_item CTX_Lam (TArrow τ τ' :: τ :: Γ) τ' Γ (TArrow τ τ')
| TP_CTX_AppL (e2 : expr) : ∀ Γ τ τ',
    typed Γ e2 τ →
    typed_context_item (CTX_AppL e2) Γ (TArrow τ τ') Γ τ'
| TP_CTX_AppR (e1 : expr) : ∀ Γ τ τ',
    typed Γ e1 (TArrow τ τ') →
    typed_context_item (CTX_AppR e1) Γ τ Γ τ'
| TP_CTX_PairL (e2 : expr) : ∀ Γ τ τ',
    typed Γ e2 τ' →
    typed_context_item (CTX_PairL e2) Γ τ Γ (TProd τ τ')
| TP_CTX_PairR (e1 : expr) : ∀ Γ τ τ',
    typed Γ e1 τ →
    typed_context_item (CTX_PairR e1) Γ τ' Γ (TProd τ τ')
| TP_CTX_Fst : ∀ Γ τ τ',
    typed_context_item CTX_Fst Γ (TProd τ τ') Γ τ
| TP_CTX_Snd : ∀ Γ τ τ',
    typed_context_item CTX_Snd Γ (TProd τ τ') Γ τ'
| TP_CTX_InjL : ∀ Γ τ τ',
    typed_context_item CTX_InjL Γ τ Γ (TSum τ τ')
| TP_CTX_InjR : ∀ Γ τ τ',
    typed_context_item CTX_InjR Γ τ' Γ (TSum τ τ')
| TP_CTX_CaseL (e1 : expr) (e2 : expr) : ∀ Γ τ1 τ2 τ',
    typed (τ1 :: Γ) e1 τ' → typed (τ2 :: Γ) e2 τ' →
    typed_context_item (CTX_CaseL e1 e2) Γ (TSum τ1 τ2) Γ τ'
| TP_CTX_CaseM (e0 : expr) (e2 : expr) : ∀ Γ τ1 τ2 τ',
    typed Γ e0 (TSum τ1 τ2) → typed (τ2 :: Γ) e2 τ' →
    typed_context_item (CTX_CaseM e0 e2) (τ1 :: Γ) τ' Γ τ'
| TP_CTX_CaseR (e0 : expr) (e1 : expr) : ∀ Γ τ1 τ2 τ',
    typed Γ e0 (TSum τ1 τ2) → typed (τ1 :: Γ) e1 τ' →
    typed_context_item (CTX_CaseR e0 e1) (τ2 :: Γ) τ' Γ τ'
| TP_CTX_IfL (e1 : expr) (e2 : expr) : ∀ Γ τ,
    typed Γ e1 τ → typed Γ e2 τ →
    typed_context_item (CTX_IfL e1 e2) Γ (TBool) Γ τ
| TP_CTX_IfM (e0 : expr) (e2 : expr) : ∀ Γ τ,
    typed Γ e0 (TBool) → typed Γ e2 τ →
    typed_context_item (CTX_IfM e0 e2) Γ τ Γ τ
| TP_CTX_IfR (e0 : expr) (e1 : expr) : ∀ Γ τ,
    typed Γ e0 (TBool) → typed Γ e1 τ →
    typed_context_item (CTX_IfR e0 e1) Γ τ Γ τ
| TP_CTX_NBOPL op (e2 : expr) : ∀ Γ,
    typed Γ e2 TNat →
    typed_context_item (CTX_NBOPL op e2) Γ TNat Γ (NatBinOP_res_type op)
| TP_CTX_NBOPR op (e1 : expr) : ∀ Γ,
    typed Γ e1 TNat →
    typed_context_item (CTX_NBOPR op e1) Γ TNat Γ (NatBinOP_res_type op)
| TP_CTX_Fold : ∀ Γ τ,
    typed_context_item CTX_Fold Γ τ.[(TRec τ)/] Γ (TRec τ)
| TP_CTX_Unfold : ∀ Γ τ,
    typed_context_item CTX_Unfold Γ (TRec τ) Γ τ.[(TRec τ)/]
| TP_CTX_TLam : ∀ Γ τ,
    typed_context_item
      CTX_TLam (map (λ t : type, t.[ren (+1)]) Γ) τ Γ (TForall τ)
| TP_CTX_TApp : ∀ Γ τ τ',
    typed_context_item CTX_TApp Γ (TForall τ) Γ τ.[τ'/]
| TP_CTX_Fork : ∀ Γ,
    typed_context_item CTX_Fork Γ TUnit Γ TUnit
| TPCTX_Alloc : ∀ Γ τ,
    typed_context_item CTX_Alloc Γ τ Γ (Tref τ)
| TP_CTX_Load : ∀ Γ τ,
    typed_context_item CTX_Load Γ (Tref τ) Γ τ
| TP_CTX_StoreL (e2 : expr) : ∀ Γ τ,
    typed Γ e2 τ →
    typed_context_item (CTX_StoreL e2) Γ (Tref τ) Γ TUnit
| TP_CTX_StoreR (e1 : expr) : ∀ Γ τ,
    typed Γ e1 (Tref τ) →
    typed_context_item (CTX_StoreR e1) Γ τ Γ TUnit
| TP_CTX_CasL (e1 : expr)  (e2 : expr) : ∀ Γ τ,
    EqType τ → typed Γ e1 τ → typed Γ e2 τ →
    typed_context_item (CTX_CAS_L e1 e2) Γ (Tref τ) Γ TBool
| TP_CTX_CasM (e0 : expr) (e2 : expr) : ∀ Γ τ,
    EqType τ → typed Γ e0 (Tref τ) → typed Γ e2 τ →
    typed_context_item (CTX_CAS_M e0 e2) Γ τ Γ TBool
| TP_CTX_CasR (e0 : expr) (e1 : expr) : ∀ Γ τ,
    EqType τ → typed Γ e0 (Tref τ) → typed Γ e1 τ →
    typed_context_item (CTX_CAS_R e0 e1) Γ τ Γ TBool.

Lemma typed_context_item_typed k Γ τ Γ' τ' e :
  typed Γ e τ → typed_context_item k Γ τ Γ' τ' →
  typed Γ' (fill_ctx_item k e) τ'.
Proof. intros H1 H2; induction H2; simpl; eauto using typed. Qed.

Inductive typed_context :
  context → (list type) → type → (list type) → type → Prop :=
| TPCTX_nil : ∀ Γ τ, typed_context nil Γ τ Γ τ
| TPCTX_cons : ∀ Γ1 τ1 Γ2 τ2 Γ3 τ3 k K,
    typed_context_item k Γ2 τ2 Γ3 τ3 →
    typed_context K Γ1 τ1 Γ2 τ2 →
    typed_context (k :: K) Γ1 τ1 Γ3 τ3.

Lemma typed_context_typed K Γ τ Γ' τ' e :
  typed Γ e τ → typed_context K Γ τ Γ' τ' → typed Γ' (fill_ctx K e) τ'.
Proof.
  intros H1 H2; induction H2; simpl; eauto using typed_context_item_typed.
Qed.

Definition context_refines Γ e e' τ (He : typed Γ e τ) (He' : typed Γ e' τ) :=
  ∀ K,
    typed_context K Γ τ [] TUnit →
    ∀ thp h v, rtc step ([fill_ctx K e], ∅) ((# v) :: thp, h) →
               ∃ thp' h' v',
                 rtc step ([fill_ctx K e'], ∅) ((# v') :: thp', h').

Section Soundness.
  Context {Σ : gFunctors}
          {iI : heapIG Σ} {iS : cfgSG Σ}
          {N : namespace}.

  Definition free_type_context : varC -n> bivalC -n> iPropG lang Σ :=
    {| cofe_mor_car := λ x, {| cofe_mor_car := λ y, (True)%I |} |}.

  Local Notation Δφ := free_type_context.

  Global Instance free_context_interp_Persistent : context_interp_Persistent Δφ.
  Proof. intros x v; apply const_persistent. Qed.

  Lemma wp_basic_soundness e e' τ :
    @bin_log_related _ _ _ N Δφ [] e e' τ _ →
    ((heapI_ctx (N .@ 2) ★ Spec_ctx (N .@ 3) (to_cfg ([e'], ∅)) ★ 0 ⤇ e')%I)
      ⊢ WP e {{_, ■ (∃ thp' h v, rtc step ([e'], ∅) ((# v) :: thp', h))}}.
  Proof.
    intros H1.
    specialize (H1 [] Logic.eq_refl (to_cfg ([e'], ∅)) 0 []); simpl in H1.
    rewrite ?empty_env_subst in H1.
    iIntros "[#Hheap [#Hspec Hj]]".
    iApply wp_pvs.
    iApply wp_wand_l; iSplitR; [|iApply H1; iFrame "Hheap Hspec Hj"; trivial].
    iIntros {v} "H". iDestruct "H" as {v'} "[Hj _]".
    unfold Spec_ctx, auth.auth_ctx, auth.auth_inv, Spec_inv, tpool_mapsto,
    auth.auth_own.
    iInv> (N .@ 3) as {ρ} "[Hown %]".
    iCombine "Hj" "Hown" as "Hown".
    iDestruct (own_valid _ with "Hown !") as "Hvalid".
    iDestruct (auth_validI _ with "Hvalid") as "[Ha' %]";
      simpl; iClear "Hvalid".
    iDestruct "Ha'" as {ρ'} "Ha'"; iDestruct "Ha'" as %Ha'.
    rewrite ->(right_id _ _) in Ha'; setoid_subst.
    iPvsIntro; iSplitL.
    - iExists _. rewrite own_op. iDestruct "Hown" as "[Ho1 Ho2]".
      iSplitL; trivial.
    - iApply const_intro; eauto.
      rewrite from_to_cfg in H.
      destruct ρ' as [th hp]; unfold op, cmra_op in *; simpl in *.
      unfold prod_op, of_cfg in *; simpl in *.
      destruct th as [|r th]; simpl in *; eauto.
      destruct H0 as [Hx1 Hx2]. simpl in *.
      destruct r as [q r|]; simpl in *; eauto.
      inversion Hx1 as [|? ? Hx]; subst.
      apply frac_valid_inv_l in Hx. inversion Hx.
  Qed.

  Lemma of_empty_heap : of_heap ∅ = ∅.
  Proof. unfold of_heap; apply map_eq => i; rewrite !lookup_omap; f_equal. Qed.

  Local Arguments of_heap : simpl never.

  Lemma basic_soundness e e' τ :
    @bin_log_related _ _ _ N Δφ [] e e' τ _ →
    ∀ v thp hp,
      rtc step ([e], ∅) ((# v) :: thp, hp) →
      (∃ thp' hp' v', rtc step ([e'], ∅) ((# v') :: thp', hp')).
  Proof.
    rewrite -of_empty_heap.
    intros H1 v thp hp H2.
    match goal with
      |- ?A =>
      eapply (@wp_adequacy_result
                lang _ ⊤ (λ _, A) e v thp (of_heap ∅)
                (to_globalF heapI_name (● (∅ : heapR))
                            ⋅ to_globalF cfg_name
                            (◯ ({[ 0 := Frac 1 (DecAgree e') ]},
                                ∅ : heapR) ⋅
                            ● ({[ 0 := Frac 1 (DecAgree e') ]},
                                ∅ : heapR))
                ) hp); eauto
    end.
    - admit.
    - iIntros "[Hp Hg]".
      rewrite ownership.ownG_op.
      repeat
        match goal with
          |- context [ (ownership.ownG (to_globalF ?gn ?A))] =>
          change (ownership.ownG (to_globalF gn A)) with
          (ghost_ownership.own gn A)
        end.
      rewrite own_op.
      iDestruct "Hg" as "[Hg1 [Hg2 Hg3]]".
      iPvs (inv_alloc (N .@ 2) _ (auth.auth_inv heapI_name heapI_inv)
            with "[Hg1 Hp]") as "#Hheap"; auto.
      + iNext. iExists _; iFrame "Hp". unfold ghost_ownership.own; trivial.
      + rewrite of_empty_heap.
        iPvs (inv_alloc (N .@ 3) _ (auth.auth_inv cfg_name
                                                  (Spec_inv (to_cfg ([e'], ∅))))
            with "[Hg3]") as "#Hspec"; auto.
        * iNext. iExists _. iFrame "Hg3".
          iApply const_intro; eauto.
          rewrite from_to_cfg.
          unfold of_cfg; simpl; rewrite of_empty_heap; constructor.
        * iApply wp_basic_soundness; eauto.
          unfold heapI_ctx, Spec_ctx, auth.auth_ctx, tpool_mapsto,
          auth.auth_own. iFrame "Hheap Hspec Hg2"; trivial.
  Admitted.

  Lemma bin_log_related_under_typed_context Γ e e' τ Γ' τ' K :
    typed Γ e τ → typed Γ e' τ →
    typed_context K Γ τ Γ' τ' →
    (∀ Δ {HΔ : context_interp_Persistent Δ},
        @bin_log_related _ _ _ N Δ Γ e e' τ HΔ) →
    ∀ Δ {HΔ : context_interp_Persistent Δ},
      @bin_log_related _ _ _ N Δ Γ' (fill_ctx K e) (fill_ctx K e') τ' HΔ.
  Proof.
    revert Γ τ Γ' τ' e e'.
    induction K as [|k K]=> Γ τ Γ' τ' e e' H1 H2; simpl.
    - inversion_clear 1; trivial.
    - inversion_clear 1 as [|? ? ? ? ? ? ? ? Hx1 Hx2]. intros H3 Δ HΔ.
      specialize (IHK _ _ _ _ e e' H1 H2 Hx2 H3).
      inversion Hx1; subst; simpl.
      + eapply typed_binary_interp_Lam; eauto using typed_context_typed.
      + eapply typed_binary_interp_App; eauto using typed_binary_interp.
      + eapply typed_binary_interp_App; eauto using typed_binary_interp.
      + eapply typed_binary_interp_Pair; eauto using typed_binary_interp.
      + eapply typed_binary_interp_Pair; eauto using typed_binary_interp.
      + eapply typed_binary_interp_Fst; eauto.
      + eapply typed_binary_interp_Snd; eauto.
      + eapply typed_binary_interp_InjL; eauto.
      + eapply typed_binary_interp_InjR; eauto.
      + eapply typed_binary_interp_Case;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_Case;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_Case;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_If;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_If;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_If;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_nat_bin_op;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_nat_bin_op;
          eauto using typed_context_typed, typed_binary_interp.
      + eapply typed_binary_interp_Fold; eauto.
      + eapply typed_binary_interp_Unfold; eauto.
      + eapply typed_binary_interp_TLam; eauto.
      + eapply typed_binary_interp_TApp; trivial.
      + eapply typed_binary_interp_Fork; trivial.
      + eapply typed_binary_interp_Alloc; trivial.
      + eapply typed_binary_interp_Load; trivial.
      + eapply typed_binary_interp_Store; eauto using typed_binary_interp.
      + eapply typed_binary_interp_Store; eauto using typed_binary_interp.
      + eapply typed_binary_interp_CAS; eauto using typed_binary_interp.
      + eapply typed_binary_interp_CAS; eauto using typed_binary_interp.
      + eapply typed_binary_interp_CAS; eauto using typed_binary_interp.
  Qed.

  Lemma Binary_Soundness Γ e e' τ
        (He : typed Γ e τ) (He' : typed Γ e' τ) :
    (∀ Δ {HΔ : context_interp_Persistent Δ},
        @bin_log_related _ _ _ N Δ Γ e e' τ HΔ) →
    context_refines Γ e e' τ He He'.
  Proof.
    intros H1 K HK htp hp v Hstp.
    eapply basic_soundness; eauto.
    eapply bin_log_related_under_typed_context; eauto.
  Qed.

End Soundness.