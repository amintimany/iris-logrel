Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import F_mu_ref.lang F_mu_ref.typing F_mu_ref.rules.
From iris.program_logic Require Export lifting.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
Require Import prelude.Vlist.
Import uPred.

(** interp : is a unary logical relation. *)
Section logrel.
  Context {Σ : gFunctors}.
  Implicit Types P Q R : iPropG lang Σ.
  Notation "# v" := (of_val v) (at level 20).

  Canonical Structure leibniz_val := leibnizC val.
  
  Class Val_to_IProp_AlwaysStable (f : leibniz_val -n> iPropG lang Σ) :=
    val_to_iprop_always_stable : ∀ v : val, Persistent ((cofe_mor_car _ _ f) v).

  Arguments val_to_iprop_always_stable /.

  Definition interp_unit : leibniz_val -n> iPropG lang Σ :=
    {|
      cofe_mor_car := λ w, (w = UnitV)%I
    |}.

  Definition interp_prod (τ1i τ2i : leibniz_val -n> iPropG lang Σ) : leibniz_val -n> iPropG lang Σ :=
    {|
      cofe_mor_car := λ w, (∃ w1 w2, w = PairV w1 w2 ∧ ▷ τ1i w1 ∧ ▷ τ2i w2)%I
    |}.

  Global Instance interp_prod_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_prod.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply exist_proper =>v. apply exist_proper=> v'.
    repeat apply and_proper; trivial; first [rewrite H1|rewrite H2]; trivial.
  Qed.
  
  Global Instance interp_prod_ne n : Proper (dist n ==> dist n ==> dist n) interp_prod.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply exist_ne =>v. apply exist_ne=> v'.
    repeat apply and_ne; trivial; first [rewrite H1|rewrite H2]; trivial.
  Qed.
  
  Definition interp_sum (τ1i τ2i : leibniz_val -n> iPropG lang Σ) : leibniz_val -n> iPropG lang Σ :=
    {|
      cofe_mor_car := λ w, ((∃ w1, w = InjLV w1 ∧ ▷ τ1i w1) ∨
                            (∃ w2, w = InjRV w2 ∧ ▷ τ2i w2))%I
    |}.

  Global Instance interp_sum_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_sum.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply or_proper; apply exist_proper =>v;
      apply and_proper; try rewrite H1; try rewrite H2; auto.
  Qed.
  
  Global Instance interp_sum_ne n : Proper (dist n ==> dist n ==> dist n) interp_sum.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply or_ne; apply exist_ne =>v;
      apply and_ne; try rewrite H1; try rewrite H2; auto.
  Qed.

  Definition interp_arrow (τ1i τ2i : leibniz_val -n> iPropG lang Σ) : leibniz_val -n> iPropG lang Σ :=
    {|
      cofe_mor_car := λ w, (□ ∀ v, ▷ τ1i v → WP (App (# w) (# v)) @ ⊤ {{τ2i}})%I
    |}.

  Global Instance interp_arrow_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_arrow.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_proper, forall_proper=> v;
      apply impl_proper;
      [rewrite H1; auto| apply wp_proper; auto].
  Qed.
  
  Global Instance interp_arrow_ne n : Proper (dist n ==> dist n ==> dist n) interp_arrow.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_ne, forall_ne=> v;
      apply impl_ne;
      [rewrite H1; auto| apply wp_ne; auto].
  Qed.
  
  Definition interp_var (k : nat) (x : var) (H : x < k)
    : (@cofe_Vlist (leibniz_val -n> iPropG lang Σ) k) -n> leibniz_val -n> iPropG lang Σ :=
    force_lookup_morph k x H.

  Definition interp_forall (τi : (leibniz_val -n> iPropG lang Σ) -n> (leibniz_val -n> iPropG lang Σ))
    : leibniz_val -n> iPropG lang Σ :=
    {|
      cofe_mor_car :=
        λ w,
        (∃ e, w = TLamV e ∧
        ∀ (τ'i : {f : (leibniz_val -n> iPropG lang Σ) | Val_to_IProp_AlwaysStable f}),
            □ (▷ WP e @ ⊤ {{λ v, (τi (`τ'i) v)}}))%I
    |}.

  Global Instance interp_forall_proper : Proper ((≡) ==> (≡)) interp_forall.
  Proof.
    intros τ τ' H1 v; cbn.
    apply exist_proper => e; apply and_proper; auto.
    apply forall_proper => τ'i.
    apply always_proper, later_proper, wp_proper =>v'.
    rewrite H1; trivial.
  Qed.
    
  Global Instance interp_forall_ne n : Proper (dist n ==> dist n) interp_forall.
  Proof.
    intros τ τ' H1 v; cbn.
    apply exist_ne => e; apply and_ne; auto.
    apply forall_ne => τ'i.
    apply always_ne, later_contractive =>i Hi.
    apply wp_ne=>w. eapply dist_le.
    rewrite H1; trivial. auto with omega.
  Qed.

  Definition interp_rec_pre
             (τi : (leibniz_val -n> iPropG lang Σ) -n> (leibniz_val -n> iPropG lang Σ))
             (rec_apr : (leibniz_val -n> iPropG lang Σ))
    : (leibniz_val -n> iPropG lang Σ) :=
    {|
      cofe_mor_car := λ w, (□ (∃ e, w = FoldV e ∧ ▷ WP e @ ⊤ {{ λ v, τi rec_apr v}}))%I
    |}.

  Global Instance interp_rec_pre_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_rec_pre.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_proper; apply exist_proper=>e; apply and_proper; trivial.
    apply later_proper, wp_proper=>v.
    rewrite H1 H2; trivial.
  Qed.
  
  Global Instance interp_rec_pre_ne n : Proper (dist n ==> dist n ==> dist n) interp_rec_pre.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_ne; apply exist_ne=>e; apply and_ne; trivial.
    apply later_contractive =>i Hi.
    apply wp_ne=>v.
    eapply dist_le.
    rewrite H1 H2; trivial.
    auto with omega.
  Qed.
  
  Global Instance interp_rec_pre_contr
           (τi : (leibniz_val -n> iPropG lang Σ) -n> (leibniz_val -n> iPropG lang Σ))
    :
      Contractive (interp_rec_pre τi).
  Proof.
    intros n f g H w; cbn.
    apply always_ne;apply exist_ne; intros e; apply and_ne; trivial.
    apply later_contractive =>i Hi.
    apply wp_ne; intros v; rewrite H; trivial.
  Qed.
  
  Definition interp_rec (τi : (leibniz_val -n> iPropG lang Σ) -n> (leibniz_val -n> iPropG lang Σ))
    := fixpoint (interp_rec_pre τi).

  Global Instance interp_rec_proper : Proper ((≡) ==> (≡)) interp_rec.
  Proof.
    intros τ τ' H1.
    unfold interp_rec.
    rewrite fixpoint_proper; eauto=>f.
    rewrite H1; trivial.
  Qed.
    
  Global Instance interp_rec_ne n : Proper (dist n ==> dist n) interp_rec.
  Proof.
    intros τ τ' H1.
    unfold interp_rec.
    rewrite fixpoint_ne; eauto=>f.
    rewrite H1; trivial.
  Qed.

  Context `{i : heapG Σ}.
  Context `{L : namespace}.

  Definition interp_ref_pred (l : loc) (τi : leibniz_val -n> iPropG lang Σ)
    : iPropG lang Σ :=
    (∃ v, l ↦ v ★ (τi v))%I.

  Global Instance interp_ref_pred_proper l : Proper ((≡) ==> (≡)) (interp_ref_pred l).
  Proof.
    intros f g H.
    apply exist_proper =>w; apply sep_proper; trivial.
  Qed.
    
  Global Instance interp_ref_pred_ne l n : Proper (dist n ==> dist n) (interp_ref_pred l).
  Proof.
    intros f g H.
    apply exist_ne =>w; apply sep_ne; trivial.
  Qed.

  Definition interp_ref (τi : leibniz_val -n> iPropG lang Σ)
    : leibniz_val -n> iPropG lang Σ :=
    {|
      cofe_mor_car :=
        λ w, (∃ l, w = LocV l ∧ inv (L .@ l) (interp_ref_pred l τi))%I
    |}.

  Global Instance interp_ref_proper : Proper ((≡) ==> (≡)) interp_ref.
  Proof.
    intros τ τ' H1 v; cbn.
    apply exist_proper => e; apply and_proper; auto.
    apply exist_proper => l; apply and_proper; auto.
    apply ownI_proper; rewrite H1; trivial.
  Qed.
    
  Global Instance interp_ref_ne n : Proper (dist n ==> dist n) interp_ref.
  Proof.
    intros τ τ' H1 v; cbn.
    apply exist_ne => e; apply and_ne; auto.
    apply exist_ne => l; apply and_ne; auto.
    apply ownI_contractive => j H2.
    eapply dist_le.
    rewrite H1; trivial. auto with omega.
  Qed.
  
  Program Fixpoint interp
           (k : nat) (τ : type) {struct τ}
    : closed_type k τ → (@cofe_Vlist (leibniz_val -n> iPropG lang Σ) k) -n> leibniz_val -n> iPropG lang Σ
    :=
        match τ as t return closed_type k t → _ with
        | TUnit => λ _, {| cofe_mor_car := λ Δ,interp_unit |}
        | TProd τ1 τ2 =>
          λ HC',
          {| cofe_mor_car :=
               λ Δ,interp_prod
                     (interp k τ1 (closed_type_prod_1 HC') Δ)
                     (interp k τ2 (closed_type_prod_2 HC') Δ)|}
        | TSum τ1 τ2 =>
          λ HC',
          {| cofe_mor_car :=
               λ Δ,interp_sum
                     (interp k τ1 (closed_type_sum_1 HC') Δ)
                     (interp k τ2 (closed_type_sum_2 HC') Δ)|}
        | TArrow τ1 τ2 =>
          λ HC',
          {|cofe_mor_car :=
              λ Δ, interp_arrow
                     (interp k τ1 (closed_type_arrow_1 HC') Δ)
                     (interp k τ2 (closed_type_arrow_2 HC') Δ)|}
        | TVar v => λ HC', {| cofe_mor_car := λ Δ,interp_var k v (closed_type_var HC') Δ |}
        | TForall τ' =>
          λ HC',
          {| cofe_mor_car :=
               λ Δ,
               interp_forall
                 (Vlist_cons_apply Δ (interp (S k) τ' (closed_type_forall HC'))) |}
        | TRec τ' =>
          λ HC',
          {| cofe_mor_car :=
               λ Δ, interp_rec
                      (Vlist_cons_apply Δ (interp (S k) τ' (closed_type_rec HC'))) |}
        | Tref τ' =>
          λ HC',
          {| cofe_mor_car :=
               λ Δ, interp_ref (interp k τ' (closed_type_ref HC') Δ) |}
        end%I.
  Solve Obligations with repeat intros ?; match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.

  Lemma interp_closed_irrel
        (k : nat) (τ : type) (HC HC': closed_type k τ)
        (Δ : Vlist (leibniz_val -n> iPropG lang Σ) k)
        (v : val)
    : interp k τ HC Δ v ≡ interp k τ HC' Δ v.
  Proof.
    revert k HC HC' Δ v.
    induction τ; intros k HC HC' Δ v; cbn;
    let rec tac :=
        match goal with
        | |- (∃ _, _)%I ≡ (∃ _, _)%I =>
          progress repeat let w := fresh "w" in apply exist_proper => w; tac
        | |- (_ ∧ _)%I ≡ (_ ∧ _)%I => progress repeat apply and_proper; tac
        | |- (_ ★ _)%I ≡ (_ ★ _)%I => progress repeat apply sep_proper; tac
        | |- (_ ∨ _)%I ≡ (_ ∨ _)%I => progress repeat apply or_proper; tac
        | |- (▷ _)%I ≡ (▷ _)%I => progress repeat apply later_proper; tac
        | |- (∀ _, _)%I ≡ (∀ _, _)%I =>
          progress repeat let w := fresh "w" in apply forall_proper => w; tac
        | |- (□ _)%I ≡ (□ _)%I => progress repeat apply always_proper; tac
        | |- (_ → _)%I ≡ (_ → _)%I => progress repeat apply impl_proper; tac
        | |- (WP _ @ _ {{_}})%I ≡ (WP _ @ _ {{_}})%I =>
          progress repeat apply wp_proper; try intros ?; tac
        | |- (ownI _ _)%I ≡ (ownI _ _)%I =>
          progress repeat apply ownI_proper; try intros ?; tac
        | _ => unfold interp_rec; rewrite fixpoint_proper; eauto;
              intros ? ?; unfold interp_rec_pre; cbn; tac
        | _ => auto
        end
    in tac.
    - unfold force_lookup.
      match goal with
        [|- _ (match ?A with |Some _ => _ |None => _ end ?B) _ ≡ _ (match ?A with |Some _ => _ |None => _ end ?C) _] => 
        generalize B; generalize C; destruct A; auto;
        let H := fresh "H" in intros H; inversion H; congruence
      end.
  Qed.
    
  Definition env_subst (vs : list val) (x : var) : expr :=
    from_option (Var x) (of_val <$> vs !! x).
  
  Lemma typed_subst_head_simpl k Δ τ e w ws :
    typed k Δ e τ -> length Δ = S (length ws) →
    e.[# w .: env_subst ws] = e.[env_subst (w :: ws)]
  .
  Proof.
    intros H1 H2.
    rewrite /env_subst. eapply typed_subst_invariant; eauto=> /= -[|x] ? //=.
    destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first omega; simpl.
      by rewrite Hv.
  Qed.

  Class VlistAlwaysStable {k} (Δ : Vlist (leibniz_val -n> iPropG lang Σ) k) :=
    vlistalwaysstable : Forall Val_to_IProp_AlwaysStable (` Δ).

  Global Instance Val_to_IProp_AlwaysStable_Always_Stable
           (f : leibniz_val -n> iPropG lang Σ)
           {Hf : Val_to_IProp_AlwaysStable f}
           (v : val)
    : Persistent (f v).
  Proof. apply Hf. Qed.
    
  Global Instance interp_always_stable
           k τ H (Δ : Vlist (leibniz_val -n> iPropG lang Σ) k)
           {HΔ : VlistAlwaysStable Δ}
    : Val_to_IProp_AlwaysStable (interp k τ H Δ).
  Proof.
    induction τ; cbn; intros v; try apply _.
  - rewrite /interp_rec /Persistent fixpoint_unfold /interp_rec_pre.
    apply always_intro'; trivial.
  - apply (@force_lookup_Forall
             _ _
             (λ f : leibniz_val -n> iPropG lang Σ, Persistent (f v))).
    apply Forall_forall => f H1.
    eapply Forall_forall in HΔ; [apply HΔ|trivial].
  Qed.

  Global Instance alwyas_stable_Δ k Δ Γ vs
           (Hctx : closed_ctx k Γ)
           {HΔ : VlistAlwaysStable Δ}
    : Persistent (Π∧ zip_with (λ τ v, interp k (` τ) (proj2_sig τ) Δ v) (closed_ctx_list _ Γ Hctx) vs)%I.
  Proof. typeclasses eauto. Qed.

  Global Instance alwyas_stable_Vlist_cons k f Δ
           (Hf : Val_to_IProp_AlwaysStable f)
           {HΔ : VlistAlwaysStable Δ}
    : VlistAlwaysStable (@Vlist_cons _ k f Δ).
  Proof. constructor; auto. Qed.

  Lemma type_context_closed_irrel
        (k : nat) (Δ : Vlist (leibniz_val -n> iPropG lang Σ) k) (Γ : list type)
        (vs : list leibniz_val)
        (Hctx Hctx' : closed_ctx k Γ) :
    (Π∧ zip_with
          (λ (τ : {τ : type | closed_type k τ}) (v0 : leibniz_val),
           ((interp k (` τ) (proj2_sig τ)) Δ) v0)
          (closed_ctx_list k Γ Hctx)
          vs)%I
      ≡
      (Π∧ zip_with
           (λ (τ : {τ : type | closed_type k τ}) (v : leibniz_val),
            ((interp k (` τ) (proj2_sig τ)) Δ) v)
           (closed_ctx_list k Γ Hctx')
           vs)%I.
  Proof.
    revert vs.
    induction Γ; cbn; auto.
    destruct vs; cbn; auto.
    apply and_proper.
    - apply interp_closed_irrel.
    - apply IHΓ.
  Qed.    

  Local Ltac ipropsimpl :=
    repeat
      match goal with
      | [|- (_ ⊢ (_ ∧ _))%I] => eapply and_intro
      | [|- (▷ _ ⊢ ▷ _)%I] => apply later_mono
      | [|- (_ ⊢ ∃ _, _)%I] => rewrite -exist_intro
      | [|- ((∃ _, _) ⊢ _)%I] => let v := fresh "v" in rewrite exist_elim; [|intros v]
      end.

  Local Hint Extern 1 => progress ipropsimpl.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) uconstr(t) ident(v) :=
    rewrite -(@wp_bind _ _ _ [ctx]) /= -wp_impl_l; apply and_intro; [
    apply (@always_intro _ _ _ t), forall_intro=> v /=; apply impl_intro_l| eauto with itauto].

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) :=
    rewrite -(@wp_bind _ _ _ [ctx]) /= -wp_mono; eauto; intros v; cbn.

  Create HintDb itauto.

  Local Hint Extern 3 ((_ ∧ _) ⊢ _)%I => rewrite and_elim_r : itauto.
  Local Hint Extern 3 ((_ ∧ _) ⊢ _)%I => rewrite and_elim_l : itauto.
  Local Hint Extern 3 (_ ⊢ (_ ∨ _))%I => rewrite -or_intro_l : itauto.
  Local Hint Extern 3 (_ ⊢ (_ ∨ _))%I => rewrite -or_intro_r : itauto.
  Local Hint Extern 2 (_ ⊢ ▷ _)%I => etransitivity; [|rewrite -later_intro] : itauto.
  
  Local Ltac value_case := rewrite -wp_value/= ?to_of_val //; auto 2.


  Lemma interp_subst_weaken
        (k m n : nat)
        (Δ : Vlist (leibniz_val -n> iPropG lang Σ) k)
        (Ξ : Vlist (leibniz_val -n> iPropG lang Σ) m)
        (ξ : Vlist (leibniz_val -n> iPropG lang Σ) n)
        (τ : type)
        (HC : closed_type (m + k) τ)
        (HC' : closed_type (m + (n + k)) τ.[iter m up (ren (+n))])
    : interp (m + k) τ HC (Vlist_app Ξ Δ)
             ≡ interp (m + (n + k))
             τ.[iter m up (ren (+n))] HC' (Vlist_app Ξ (Vlist_app ξ Δ)).
  Proof.
    revert k m n Δ Ξ ξ HC HC'.
    induction τ; intros k m n Δ Ξ ξ HC HC' w; cbn; auto.
    - apply exist_proper =>w1; apply exist_proper =>w2;
        repeat apply and_proper; try apply later_proper;
        solve [trivial|apply IHτ1|apply IHτ2].
    - apply or_proper; apply exist_proper =>w1;
        repeat apply and_proper; try apply later_proper;
        solve [trivial|apply IHτ1|apply IHτ2].
    - apply always_proper, forall_proper => w1;
        apply impl_proper; try apply later_proper; try apply wp_proper;
        solve [apply IHτ1|apply IHτ2].
    - apply interp_rec_proper =>f; cbn.
      change (S (m + k)) with (S m + k).
      change (S (m + (n + k))) with (S m + (n + k)).
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      rewrite !Vlist_app_cons.
      apply IHτ.
    - asimpl in *.          
      revert HC'; rewrite iter_up; intros HC'.
      destruct lt_dec; asimpl; unfold ids, Ids_type; cbn.
      + rewrite !force_lookup_l; trivial.
      + inversion HC'; subst.
        rewrite force_lookup_r; try lia; intros Hlt.
        rewrite force_lookup_r; try lia; intros Hlt'.
        rewrite force_lookup_r; try lia; intros Hlt''.
        revert Hlt''.
        match goal with
          [|- ∀ _, _ (force_lookup _ ?A _) _ ≡ _ (force_lookup _ ?B _) _] =>
          replace B with A by lia; intros Hlt''
        end.
        rewrite force_lookup_proper; eauto.
    - apply exist_proper =>w1; apply and_proper; auto.
      apply forall_proper; intros [f Hf].
      apply always_proper, later_proper, wp_proper => w2.
      cbn.
      change (S (m + k)) with (S m + k).
      change (S (m + (n + k))) with (S m + (n + k)).
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      rewrite !Vlist_app_cons.
      apply IHτ.
    - apply exist_proper =>w1; apply and_proper; auto.
      apply exist_proper => l; apply and_proper; auto.
      apply ownI_proper; rewrite interp_ref_pred_proper; trivial.
  Qed.

  Lemma interp_ren_S (k : nat) (τ : type)
        (Δ : Vlist (leibniz_val -n> iPropG lang Σ) k)
        (τi : leibniz_val -n> iPropG lang Σ)
        (HC : closed_type k τ) (HC' : closed_type (S k) τ.[ren (+1)])
        (v : leibniz_val)
    : interp k τ HC Δ v ≡ interp (S k) τ.[ren (+1)] HC' (Vlist_cons τi Δ) v.
  Proof.
    rewrite -(Vlist_nil_app Δ).
    rewrite (Vlist_app_cons τi Vlist_nil Δ).
    rewrite -(Vlist_nil_app (Vlist_app (Vlist_cons τi Vlist_nil) Δ)).
    apply (interp_subst_weaken k 0 1).
  Qed.

  Lemma interp_subst_iter_up
        (k m : nat)
        (Δ : Vlist (leibniz_val -n> iPropG lang Σ) k)
        (Ξ : Vlist (leibniz_val -n> iPropG lang Σ) m)
        (τ : type)
        (τ' : type) (HC' : closed_type k τ')
        (HC : closed_type (m + S k) τ)
        (HC'' : closed_type (m + k) τ.[iter m up (τ' .: ids)])
    : interp (m + S k) τ HC (Vlist_app Ξ (Vlist_cons (interp k τ' HC' Δ) Δ))
             ≡ interp (m + k) τ.[iter m up (τ' .: ids)] HC'' (Vlist_app Ξ Δ).
  Proof.
    revert k m Δ Ξ τ' HC' HC HC''.
    induction τ; intros k m Δ Ξ τ' HC' HC HC'' w; cbn; auto.
    - apply exist_proper =>w1; apply exist_proper =>w2;
        repeat apply and_proper; try apply later_proper;
        solve [trivial|apply IHτ1|apply IHτ2].
    - apply or_proper; apply exist_proper =>w1;
        repeat apply and_proper; try apply later_proper;
        solve [trivial|apply IHτ1|apply IHτ2].
    - apply always_proper, forall_proper => w1;
        apply impl_proper; try apply later_proper; try apply wp_proper;
        solve [apply IHτ1|apply IHτ2].
    - apply interp_rec_proper =>f; cbn.
      change (S (m + S k)) with (S m + S k).
      change (S (m + k)) with (S m + k).
      change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids)).
      rewrite !Vlist_app_cons.
      apply IHτ.
    - asimpl in *.
      revert HC''; rewrite iter_up; intros HC''.
      destruct lt_dec.
      + unfold ids, Ids_type; cbn.
        rewrite !force_lookup_l; trivial.
      + remember (x - m) as u.
        destruct (nat_eq_dec x m); try lia.
        * revert HC''; replace u with 0 by lia; asimpl; intros HC''.
          rewrite force_lookup_r; try lia; rewrite -Hequ; intros HC3.
          destruct u; try lia; cbn.
          rewrite -(Vlist_nil_app (Vlist_app Ξ Δ)).
          rewrite -(interp_subst_weaken _ 0 m).
          rewrite Vlist_nil_app; trivial.
        * destruct u; try lia; destruct x; try lia.
          revert HC''; asimpl; intros HC''; inversion HC''.
          unfold ids, Ids_type; cbn.
          rewrite !force_lookup_r; try lia; rewrite -Hequ; intros HC3 HC4.
          rewrite force_lookup_Vlist_cons; try lia; intros HC5.
          revert HC3.
          match goal with
            [|- ∀ _, _ (force_lookup _ ?A _) _ ≡ _ (force_lookup _ ?B _) _] =>
            replace B with A by lia; intros HC3
          end.
          rewrite force_lookup_proper; eauto.
    - apply exist_proper =>w1; apply and_proper; auto.
      apply forall_proper; intros [f Hf].
      apply always_proper, later_proper, wp_proper => w2.
      cbn.
      change (S (m + S k)) with (S m + S k).
      change (S (m + k)) with (S m + k).
      change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids)).
      rewrite !Vlist_app_cons.
      apply IHτ.
    - apply exist_proper =>w1; apply and_proper; auto.
      apply exist_proper => l; apply and_proper; auto.
      apply ownI_proper; rewrite interp_ref_pred_proper; trivial.
  Qed.

  Lemma interp_subst
    (k : nat)
    (Δ : Vlist (leibniz_val -n> iPropG lang Σ) k)
    (τ : type)
    (τ' : type) (HC' : closed_type k τ')
    (HC : closed_type (S k) τ)
    (HC'' : closed_type k τ.[τ'/])
    : interp (S k) τ HC (Vlist_cons (interp k τ' HC' Δ) Δ)
             ≡ interp k τ.[τ'/] HC'' Δ.
  Proof.
    rewrite <- (Vlist_nil_app Δ) at 3.
    rewrite <- (Vlist_nil_app (Vlist_cons ((interp k τ' HC') Δ) Δ)).
    apply (interp_subst_iter_up k 0 Δ Vlist_nil τ τ' HC' HC HC'').
  Qed.

  Lemma zip_with_closed_ctx_list_subst
        (k : nat) (Δ : Vlist (leibniz_val -n> iPropG lang Σ) k) (Γ : list type) 
        (Hctx : closed_ctx k Γ)
        (Hctx' : closed_ctx (S k) (map (λ t : type, t.[ren (+1)]) Γ))
        (vs : list leibniz_val) (τi : leibniz_val -n> iPropG lang Σ)
    : ((Π∧ zip_with
             (λ (τ : {τ : type | closed_type k τ}) (v : leibniz_val),
              ((interp k (` τ) (proj2_sig τ)) Δ) v)
             (closed_ctx_list k Γ Hctx) vs)%I)
        ≡ (Π∧ zip_with
                (λ (τ : {τ : type | closed_type (S k) τ}) (v : leibniz_val),
                 ((interp (S k) (` τ) (proj2_sig τ)) (Vlist_cons τi Δ)) v)
                (closed_ctx_list (S k) (map (λ t : type, t.[ren (+1)]) Γ) Hctx') vs)%I.
  Proof.
    revert k Δ Hctx Hctx' vs τi.
    induction Γ as [|τ Γ]; intros k Δ Hctx Hctx' vs τi; cbn; trivial.
    destruct vs; cbn; trivial.
    apply and_proper.
    - apply interp_ren_S.
    - apply IHΓ.
  Qed.

End logrel.