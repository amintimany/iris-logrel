Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import iris_logrel.F_mu_ref_par.lang iris_logrel.F_mu_ref_par.typing
        iris_logrel.F_mu_ref_par.rules iris_logrel.F_mu_ref_par.rules_binary.
From iris.program_logic Require Export lifting.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
Require Import iris.proofmode.pviewshifts.
Import uPred.

(** interp : is a unary logical relation. *)
Section logrel.
  Context {Σ : gFunctors}.

  Canonical Structure bivalC := prodC valC valC.

  (** Just to get nicer closed forms, we define extend_context_interp in
      three steps. *)
  Program Definition extend_context_interp_fun1
      (τi : bivalC -n> iPropG lang Σ)
      (f : varC -n> bivalC -n> iPropG lang Σ) :
      (varC -n> bivalC -n> iPropG lang Σ) := λne x,
    match x return bivalC -n> iPropG lang Σ with O => τi | S x' => f x' end.

  Program Definition extend_context_interp_fun2
      (τi : bivalC -n> iPropG lang Σ) :
      (varC -n> bivalC -n> iPropG lang Σ) -n>
      (varC -n> bivalC -n> iPropG lang Σ) := λne f,
    extend_context_interp_fun1 τi f.
  Next Obligation. intros ???? Hfg x; destruct x; cbn; trivial. Qed.

  Program Definition extend_context_interp :
      (bivalC -n> iPropG lang Σ) -n>
      (varC -n> bivalC -n> iPropG lang Σ) -n>
      (varC -n> bivalC -n> iPropG lang Σ) := λne τi,
    extend_context_interp_fun2 τi.
  Next Obligation. intros n g h H Δ x y. destruct x; cbn; auto. Qed.

  Program Definition extend_context_interp_apply :
      ((varC -n> bivalC -n> iPropG lang Σ)) -n>
      ((varC -n> bivalC -n> iPropG lang Σ) -n>
       bivalC -n> iPropG lang Σ) -n>
      (bivalC -n> iPropG lang Σ) -n> (bivalC -n> iPropG lang Σ) := λne Δ f g,
    f (extend_context_interp g Δ).
  Solve Obligations with
  repeat intros ?; (cbn + idtac);
    try match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.
  Next Obligation.
    intros n Δ Δ' HΔ f g x.  cbn.
    match goal with
      |- _ _ ?F x ≡{n}≡ _ _ ?G x =>
      assert (F ≡{n}≡ G) as HFG; [|rewrite HFG; trivial]
    end.
    apply cofe_mor_car_ne; trivial. intros y. cbn.
    destruct y; trivial.
  Qed.

  Program Definition interp_unit : bivalC -n> iPropG lang Σ := λne w,
    (w.1 = UnitV ∧ w.2 = UnitV)%I.
  Next Obligation. intros n x y [H1 H2]; rewrite H1 H2; trivial. Qed.

  Program Definition interp_nat : bivalC -n> iPropG lang Σ := λne w,
    (∃ n, w.1 = (♯v n) ∧ w.2 = (♯v n))%I.
  Next Obligation. intros n x y [H1 H2]; rewrite H1 H2; trivial. Qed.

  Program Definition interp_bool : bivalC -n> iPropG lang Σ :=λne w,
    (∃ b, w.1 = (♭v b) ∧ w.2 = (♭v b))%I.
  Next Obligation. intros n x y [H1 H2]; rewrite H1 H2; trivial. Qed.

  Program Definition interp_prod :
      (bivalC -n> iPropG lang Σ) -n> (bivalC -n> iPropG lang Σ) -n>
      bivalC -n> iPropG lang Σ := λne τ1i τ2i w,
    (∃ w1 w2, w = (PairV (w1.1) (w1.2), PairV (w2.1) (w2.2)) ∧
              τ1i (w1.1, w2.1) ∧ τ2i (w1.2, w2.2))%I.
  Next Obligation.
    intros τ1i τ2i n [x1 x2] [y1 y2] [H1 H2]; simpl in *.
    rewrite H1 H2; trivial.
  Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.

  Program Definition interp_sum :
      (bivalC -n> iPropG lang Σ) -n> (bivalC -n> iPropG lang Σ) -n>
      bivalC -n> iPropG lang Σ := λne τ1i τ2i w,
    ((∃ w1, w = (InjLV (w1.1), InjLV (w1.2)) ∧ τ1i w1) ∨
     (∃ w2, w = (InjRV (w2.1), InjRV (w2.2)) ∧ τ2i w2))%I.
  Next Obligation.
    intros τ1i τ2i n [x1 x2] [y1 y2] [H1 H2]; simpl in *.
    rewrite H1 H2; trivial.
  Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.

  Context `{Si : cfgSG Σ}.

  Program Definition interp_arrow :
      (bivalC -n> iPropG lang Σ) -n> (bivalC -n> iPropG lang Σ) -n>
      bivalC -n> iPropG lang Σ := λne τ1i τ2i w,
    (□ ∀ j K v,
      τ1i v ★ j ⤇ (fill K (App (# w.2) (# v.2))) →
      WP App (# w.1) (# v.1) {{ z, ∃ z', j ⤇ (fill K (# z')) ★ τ2i (z, z') }})%I.
  Next Obligation. 
    intros τ1i τ2i n [x1 x2] [y1 y2] [H1 H2]; simpl in *.
    rewrite H1 H2; trivial.
  Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.

  Program Definition interp_forall :
      ((bivalC -n> iPropG lang Σ) -n> (bivalC -n> iPropG lang Σ)) -n>
      bivalC -n> iPropG lang Σ := λne τi w,
    (□ ∀ (f : bivalC -n> iPropG lang Σ) j K,
       (■ (∀ vw, PersistentP (f vw))) →
       j ⤇ (fill K (TApp (# w.2))) →
       WP TApp (# w.1) {{ v, ∃ v', j ⤇ fill K (# v') ★ τi f (v, v')}})%I.
  Next Obligation.
    intros τi n [x1 x2] [y1 y2 ] [H1 H2]. simpl in *; auto.
    inversion H1; subst; inversion H2; subst; trivial.
  Qed.
  Next Obligation. solve_proper. Qed.

  Program Definition interp_rec_pre :
      ((bivalC -n> iPropG lang Σ) -n> (bivalC -n> iPropG lang Σ)) -n>
      (bivalC -n> iPropG lang Σ) -n>
      (bivalC -n> iPropG lang Σ) := λne τi rec_appr w,
    (□ (∃ v, w = (FoldV (v.1), FoldV (v.2)) ∧ ▷ (τi rec_appr v)))%I.
  Next Obligation.
    intros τi rec_appr n [x1 x2] [y1 y2] [H1 H2]; simpl in *.
    inversion H1; inversion H2; subst; trivial.
  Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.

  Global Instance interp_rec_pre_contr
      (τi : (bivalC -n> iPropG lang Σ) -n> (bivalC -n> iPropG lang Σ)) :
    Contractive (interp_rec_pre τi).
  Proof.
    intros n f g H w; cbn.
    apply always_ne, exist_ne; intros e; apply and_ne; trivial.
    apply later_contractive =>i Hi. rewrite H; trivial.
  Qed.

  Program Definition interp_rec :
      ((bivalC -n> iPropG lang Σ) -n> (bivalC -n> iPropG lang Σ)) -n>
      (bivalC -n> iPropG lang Σ) := λne τi,
    fixpoint (interp_rec_pre τi).
  Next Obligation. intros n f g H; apply fixpoint_ne => z; rewrite H; trivial. Qed.

  Context `{i : heapIG Σ} (L : namespace).

  Program Definition interp_ref_pred (l : loc * loc) :
      (bivalC -n> iPropG lang Σ) -n> iPropG lang Σ := λne τi,
    (∃ v, (l.1) ↦ᵢ (v.1) ★ (l.2) ↦ₛ (v.2) ★ (τi v))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition interp_ref :
      (bivalC -n> iPropG lang Σ) -n> bivalC -n> iPropG lang Σ := λne τi w,
    (∃ l, w = (LocV (l.1), LocV (l.2)) ∧ inv (L .@ l) (interp_ref_pred l τi))%I.
  Next Obligation.
    intros τi n [x1 x2] [y1 y2] [H1 H2]; simpl in *.
    inversion H1; inversion H2; subst; trivial.
  Qed.
  Next Obligation. solve_proper. Qed.

  Program Fixpoint interp (τ : type) {struct τ} :
      (varC -n> bivalC -n> iPropG lang Σ) -n> bivalC -n> iPropG lang Σ :=
    match τ return (varC -n> bivalC -n> iPropG lang Σ) -n>
                   bivalC -n> iPropG lang Σ with
    | TUnit => λne Δ, interp_unit
    | TNat => λne Δ, interp_nat
    | TBool => λne Δ, interp_bool
    | TProd τ1 τ2 => λne Δ, interp_prod (interp τ1 Δ) (interp τ2 Δ)
    | TSum τ1 τ2 => λne Δ, interp_sum(interp τ1 Δ) (interp τ2 Δ)
    | TArrow τ1 τ2 => λne Δ, interp_arrow (interp τ1 Δ) (interp τ2 Δ)
    | TVar v => λne Δ, (Δ v)
    | TForall τ' =>λne Δ, interp_forall  (extend_context_interp_apply Δ (interp τ'))
    | TRec τ' => λne Δ, interp_rec (extend_context_interp_apply Δ (interp τ'))
    | Tref τ' => λne Δ, interp_ref (interp τ' Δ)
    end%I.
  Solve Obligations
  with repeat intros ?;
              match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.

  Global Instance interp_Persistent
      τ (Δ : varC -n> bivalC -n> iPropG lang Σ)
      {HΔ : ∀ x vw, PersistentP (Δ x vw)} :
    ∀ vw, PersistentP (interp τ Δ vw).
  Proof.
    revert Δ HΔ.
    induction τ; cbn; intros Δ HΔ v; try apply _.
    rewrite /PersistentP /interp_rec fixpoint_unfold /interp_rec_pre; cbn.
    apply always_intro'; trivial.
  Qed.

  Global Instance extend_context_interp_Persistent
    (f : bivalC -n> iPropG lang Σ) (Δ : varC -n> bivalC -n> iPropG lang Σ)
           (Hf : ∀ vw, PersistentP (f vw))
           {HΔ : ∀ x vw, PersistentP (Δ x vw)}
    : ∀ x vw, PersistentP (@extend_context_interp f Δ x vw).
  Proof. intros x v. destruct x; cbn; trivial. Qed.

  Local Ltac properness :=
    repeat
      match goal with
      | |- (∃ _: _, _)%I ≡ (∃ _: _, _)%I => apply exist_proper =>?
      | |- (∀ _: _, _)%I ≡ (∀ _: _, _)%I => apply forall_proper =>?
      | |- (_ ∧ _)%I ≡ (_ ∧ _)%I => apply and_proper
      | |- (_ ∨ _)%I ≡ (_ ∨ _)%I => apply or_proper
      | |- (_ → _)%I ≡ (_ → _)%I => apply impl_proper
      | |- (WP _ {{ _ }})%I ≡ (WP _ {{ _ }})%I => apply wp_proper =>?
      | |- (▷ _)%I ≡ (▷ _)%I => apply later_proper
      | |- (□ _)%I ≡ (□ _)%I => apply always_proper
      | |- (inv _ _)%I ≡ (inv _ _)%I => apply (contractive_proper _)
      | |- (_ ★ _)%I ≡ (_ ★ _)%I => apply sep_proper
      end.

  Lemma interp_unused_contex_irrel
        (m n : nat)
        (Δ Δ' : varC -n> bivalC -n> iPropG lang Σ)
        (HΔ : ∀ v, Δ (if lt_dec v m then v else (n + v)) ≡
                     Δ' (if lt_dec v m then v else (n + v)))
        (τ : type)
    :
      interp τ.[iter m up (ren (+n))] Δ ≡ interp τ.[iter m up (ren (+n))] Δ'.
  Proof.
    revert m n Δ Δ' HΔ.
    induction τ; intros m n Δ Δ' HΔ v; cbn; auto.
    - properness; trivial; try apply IHτ1; try apply IHτ2; trivial.
    - properness; trivial; try apply IHτ1; try apply IHτ2; trivial.
    - properness; trivial; try apply IHτ1; try apply IHτ2; trivial.
    - match goal with
        |- _ _ ?f ?x ≡ _ _ ?g ?x =>
        assert (f ≡ g) as Hfg; [|rewrite Hfg; trivial]
      end.
      apply fixpoint_proper => ??; cbn.
      properness; trivial.
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      apply IHτ.
      {
        intros x y. destruct x; cbn; trivial.
        destruct lt_dec.
        - specialize (HΔ x); destruct lt_dec; auto with omega.
        - destruct (n + S x) as [|k] eqn:Heq; trivial.
          specialize (HΔ x); destruct lt_dec; auto with omega.
          replace (n + x) with k in HΔ by omega; trivial.
      }
    -  rewrite iter_up. destruct lt_dec; cbn.
       + specialize (HΔ x); destruct lt_dec; auto with omega.
       + asimpl; unfold ids; cbn.
         specialize (HΔ x); destruct lt_dec; auto with omega.
         replace (m + n + (x - m)) with (n + x) by omega. trivial.
    - properness; trivial.
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      apply IHτ.
      {
        intros x y. destruct x; cbn; trivial.
        destruct lt_dec.
        - specialize (HΔ x); destruct lt_dec; auto with omega.
        - destruct (n + S x) as [|k] eqn:Heq; trivial.
          specialize (HΔ x); destruct lt_dec; auto with omega.
          replace (n + x) with k in HΔ by omega; trivial.
      }
    - properness; trivial; try apply IHτ; trivial.
  Qed.

  Program Definition hop_context_interp (m n : nat) :
      (varC -n> bivalC -n> iPropG lang Σ) -n>
      (varC -n> bivalC -n> iPropG lang Σ) := λne Δ v,
    if lt_dec v m then Δ v else Δ (v - n).
  Next Obligation. intros ?????? Hxy; destruct Hxy; trivial. Qed.
  Next Obligation.
    intros ????? Hfg ?; cbn. destruct lt_dec; rewrite Hfg; trivial.
  Qed.

  Lemma extend_bofore_hop_context_interp (m n : nat)
      (Δ : varC -n> bivalC -n> iPropG lang Σ)
      (τi : bivalC -n> iPropG lang Σ) (v : var) :
    extend_context_interp τi (hop_context_interp m n Δ)
                             (if lt_dec v (S m) then v else n + v)
    ≡ hop_context_interp (S m) n (extend_context_interp τi Δ)
                                 (if lt_dec v (S m) then v else n + v).
  Proof.
    destruct v; cbn; trivial.
    repeat (destruct lt_dec; cbn); auto with omega.
    destruct (n + S v - n) eqn:Heq1;
      destruct (n + S v) eqn:Heq2; try destruct lt_dec; auto with omega.
    match goal with
      [ |- _ _ _ Δ ?a ≡ _ _ _ Δ ?b] => assert (Heq : a = b) by omega;
                                       rewrite Heq; trivial
    end.
  Qed.

  Lemma interp_subst_weaken
      (m n : nat) (Δ : varC -n> bivalC -n> iPropG lang Σ) (τ : type) :
    interp τ Δ ≡ interp τ.[iter m up (ren (+n))] (hop_context_interp m n Δ).
  Proof.
    revert m n Δ.
    induction τ; intros m n Δ v; cbn -[extend_context_interp]; auto.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - match goal with
        |- _ _ ?f ?x ≡ _ _ ?g ?x =>
        assert (f ≡ g) as Hfg; [|rewrite Hfg; trivial]
      end.
      apply fixpoint_proper => ??; cbn -[extend_context_interp].
      properness; trivial.
      rewrite IHτ.
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      apply interp_unused_contex_irrel.
      intros w; rewrite extend_bofore_hop_context_interp; trivial.
    - rewrite iter_up.
      asimpl; unfold ids; cbn; destruct lt_dec; cbn; destruct lt_dec; auto with omega.
      replace (m + n + (x - m)) with (x + n) by omega.
      replace (x + n - n) with x; trivial.
      { unfold var in *; omega. }
    - properness; trivial.
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      rewrite IHτ.
      apply interp_unused_contex_irrel.
      intros w; rewrite extend_bofore_hop_context_interp; trivial.
    - properness; trivial; try apply IHτ; trivial.
  Qed.

  Lemma interp_ren_S (τ : type)
      (Δ : varC -n> bivalC -n> iPropG lang Σ) (τi : bivalC -n> iPropG lang Σ) :
    interp τ Δ ≡ interp τ.[ren (+1)] (extend_context_interp τi Δ).
  Proof.
    rewrite (interp_subst_weaken 0 1).
    apply interp_unused_contex_irrel.
    clear. intros [|v]; cbn; trivial.
  Qed.

  Local Opaque eq_nat_dec.

  Program Definition context_interp_insert (m : nat) :
      (bivalC -n> iPropG lang Σ) -n>
      (varC -n> bivalC -n> iPropG lang Σ) -n>
      (varC -n> bivalC -n> iPropG lang Σ) := λne τi Δ v,
    if lt_dec v m then Δ v else if eq_nat_dec v m then τi else Δ (v - 1).
  Next Obligation. intros m τi Δ n x y Hxy; destruct Hxy; trivial. Qed.
  Next Obligation.
    intros m τi n Δ Δ' HΔ x; cbn;
      destruct lt_dec; try destruct eq_nat_dec; auto.
  Qed.
  Next Obligation.
    intros m n f g Hfg F Δ x; cbn;
      destruct lt_dec; try destruct eq_nat_dec; auto.
  Qed.

  Lemma extend_context_interp_insert (m : nat)
      (τi : bivalC -n> iPropG lang Σ)
      (Δ : varC -n> bivalC -n> iPropG lang Σ)
      (Ti : bivalC -n> iPropG lang Σ) :
    extend_context_interp Ti (context_interp_insert m τi Δ)
    ≡ context_interp_insert (S m) τi (extend_context_interp Ti Δ).
  Proof.
    intros [|v]; cbn; trivial.
    repeat destruct lt_dec; trivial;
      repeat destruct eq_nat_dec; cbn; auto with omega.
    destruct v; cbn; auto with omega.
    replace (v - 0) with v by omega; trivial.
  Qed.

  Lemma context_interp_insert_O_extend
      (τi : bivalC -n> iPropG lang Σ)
      (Δ : varC -n> bivalC -n> iPropG lang Σ) :
    context_interp_insert O τi Δ ≡ extend_context_interp τi Δ.
  Proof.
    intros [|v]; cbn; trivial.
    repeat destruct lt_dec; trivial;
      repeat destruct eq_nat_dec; cbn; auto with omega.
    destruct v; cbn; auto with omega.
  Qed.

  Lemma iter_up_subst_type (m : nat) (τ : type) (x : var) :
    iter m up (τ .: ids) x =
      if lt_dec x m then ids x else
        if eq_nat_dec x m then τ.[ren (+m)] else ids (x - 1).
  Proof.
    revert x τ.
    induction m; intros x τ; cbn.
    - destruct x; cbn.
      + destruct eq_nat_dec; auto with omega.
        asimpl; trivial.
      + destruct eq_nat_dec; auto with omega.
    - destruct x; asimpl; trivial.
      rewrite IHm.
      repeat destruct lt_dec; repeat destruct eq_nat_dec;
        asimpl; auto with omega.
  Qed.

  Lemma interp_subst_iter_up
      (m : nat) (Δ : varC -n> bivalC -n> iPropG lang Σ) (τ τ' : type) :
    interp τ (context_interp_insert m (interp τ'.[ren (+m)] Δ) Δ)
    ≡ interp τ.[iter m up (τ' .: ids)] Δ.
  Proof.
    revert m Δ.
    induction τ; intros m Δ v; cbn -[extend_context_interp]; auto.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - match goal with
        |- _ _ ?f ?x ≡ _ _ ?g ?x =>
        assert (f ≡ g) as Hfg; [|rewrite Hfg; trivial]
      end.
      apply fixpoint_proper => ??; cbn -[extend_context_interp].
      properness; trivial.
      rewrite extend_context_interp_insert.
      change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids)).
      rewrite -IHτ.
      replace (τ'.[ren (+S m)]) with ((τ'.[ren (+m)]).[ren (+1)])
        by (asimpl; trivial).
      rewrite -interp_ren_S; trivial.
    - rewrite iter_up_subst_type.
      repeat destruct lt_dec; repeat destruct eq_nat_dec;
        unfold ids; asimpl; trivial.
    - properness; trivial.
      rewrite extend_context_interp_insert.
      change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids)).
      rewrite -IHτ.
      replace (τ'.[ren (+S m)]) with ((τ'.[ren (+m)]).[ren (+1)])
        by (asimpl; trivial).
      rewrite -interp_ren_S; trivial.
    - properness; trivial; try apply IHτ; trivial.
  Qed.

  Lemma interp_subst
      (Δ : varC -n> bivalC -n> iPropG lang Σ) (τ τ' : type) :
    interp τ (extend_context_interp (interp τ' Δ) Δ) ≡ interp τ.[τ'/] Δ.
  Proof.
    rewrite -(interp_subst_iter_up O Δ τ τ').
    rewrite context_interp_insert_O_extend.
    asimpl; trivial.
  Qed.

  Lemma zip_with_context_interp_subst
      (Δ : varC -n> bivalC -n> iPropG lang Σ) (Γ : list type)
      (vs : list bivalC) (τi : bivalC -n> iPropG lang Σ) :
    ([∧] zip_with (λ τ, interp τ Δ) Γ vs)
    ⊣⊢ ([∧] zip_with (λ τ, interp τ (extend_context_interp τi Δ))
                     (map (λ t : type, t.[ren (+1)]) Γ) vs).
  Proof.
    revert Δ vs τi.
    induction Γ as [|Γ]; intros Δ vs τi; cbn; trivial.
    destruct vs; cbn; trivial.
    apply and_proper. apply interp_ren_S. apply IHΓ.
  Qed.

  Lemma EqType_related_eq τ {H : EqType τ} v v' (Δ : varC -n> bivalC -n> iPropG lang Σ)
      {HΔ : ∀ x vw, PersistentP (Δ x vw)} :
    interp τ Δ (v, v') ⊢ ■ (v = v').
  Proof.
    revert v v'; induction H => v v'; iIntros "#H1".
    - simpl; iDestruct "H1" as "[% %]"; subst; trivial.
    - simpl; iDestruct "H1" as {n} "[% %]"; subst; trivial.
    - simpl; iDestruct "H1" as {b} "[% %]"; subst; trivial.
    - iDestruct "H1" as {w1 w2} "[% [H1 H2]]".
      destruct w1; destruct w2; simpl in *.
      inversion H1; subst.
      rewrite IHEqType1 IHEqType2.
      iDestruct "H1" as "%". iDestruct "H2" as "%". subst; trivial.
    - iDestruct "H1" as "[H1|H1]".
      + iDestruct "H1" as {w} "[% H1]".
        destruct w; simpl in *.
        inversion H1; subst.
        rewrite IHEqType1.
        iDestruct "H1" as "%". subst; trivial.
      + iDestruct "H1" as {w} "[% H1]".
        destruct w; simpl in *.
        inversion H1; subst.
        rewrite IHEqType2.
        iDestruct "H1" as "%". subst; trivial.
  Qed.
End logrel.
