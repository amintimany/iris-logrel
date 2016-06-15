Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import iris_logrel.F_mu.lang iris_logrel.F_mu.typing
        iris_logrel.F_mu.rules.
Import uPred.

(** interp : is a unary logical relation. *)
Section logrel.
  Context {Σ : iFunctor}.
  Notation "# v" := (of_val v) (at level 20).

  Canonical Structure leibniz_val := leibnizC val.
  Canonical Structure leibniz_var := leibnizC var.

  Class Val_to_IProp_Persistent (f : leibniz_val -n> iProp lang Σ) :=
    val_to_iprop_persistent : ∀ v : val, PersistentP ((cofe_mor_car _ _ f) v).

  Arguments Val_to_IProp_Persistent /.

  (** Just to get nicer closed forms, we define extend_context_interp in three steps. *)
  Program Definition extend_context_interp_fun1
    (τi : leibniz_val -n> iProp lang Σ)
    (f : leibniz_var -n> leibniz_val -n> iProp lang Σ) :
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) :=
    {| cofe_mor_car :=
         λ x,
         match x return leibniz_val -n> iProp lang Σ with
         | O => τi
         | S x' => f x'
         end
    |}.

  Program Definition extend_context_interp_fun2
    (τi : leibniz_val -n> iProp lang Σ) :
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) -n>
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) :=
    {|
      cofe_mor_car := λ f, extend_context_interp_fun1 τi f
    |}.
  Next Obligation.
  Proof. intros ???? Hfg x; destruct x; cbn; trivial. Qed.

  Program Definition extend_context_interp :
    (leibniz_val -n> iProp lang Σ) -n>
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) -n>
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) :=
    {|
      cofe_mor_car := λ τi, extend_context_interp_fun2 τi
    |}.
  Next Obligation.
  Proof. intros n g h H Δ x y. destruct x; cbn; auto. Qed.

  Program Definition extend_context_interp_apply :
    ((leibniz_var -n> leibniz_val -n> iProp lang Σ)) -n>
    ((leibniz_var -n> leibniz_val -n> iProp lang Σ) -n>
     leibniz_val -n> iProp lang Σ) -n>
    (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ) :=
    {|
      cofe_mor_car := λ Δ,
        {|
          cofe_mor_car := λ f,
            {|
              cofe_mor_car := λ g, f (extend_context_interp g Δ)
            |}
        |}
    |}.
  Solve Obligations with
  repeat intros ?; (cbn + idtac);
    try match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.
  Next Obligation.
  Proof.
    intros n Δ Δ' HΔ f g x.  cbn.
    match goal with
      |- _ _ ?F x ≡{n}≡ _ _ ?G x =>
      assert (F ≡{n}≡ G) as HFG; [|rewrite HFG; trivial]
    end.
    apply cofe_mor_car_ne; trivial. intros y. cbn.
    destruct y; trivial.
  Qed.

  Definition interp_unit : leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car := λ w, (w = UnitV)%I
    |}.

  Program Definition interp_prod :
    (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ) -n>
    leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car :=
        λ τ1i,
        {|
          cofe_mor_car :=
            λ τ2i,
            {|
              cofe_mor_car :=
                λ w, (∃ w1 w2, w = PairV w1 w2 ∧ τ1i w1 ∧ τ2i w2)%I
            |}
        |}
    |}.
  Solve Obligations with
  repeat intros ?; cbn;
    repeat apply exist_ne =>?;
        try match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.

  Program Definition interp_sum :
    (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ) -n>
    leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car :=
        λ τ1i,
        {|
          cofe_mor_car :=
            λ τ2i,
            {|
              cofe_mor_car :=
                λ w, ((∃ w1, w = InjLV w1 ∧ τ1i w1) ∨
                      (∃ w2, w = InjRV w2 ∧ τ2i w2))%I
            |}
        |}
    |}.
  Solve Obligations with
  repeat intros ?; cbn; try apply or_ne;
    try apply exist_ne =>?;
        try match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.

  Program Definition interp_arrow :
    (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ) -n>
    leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car :=
        λ τ1i,
        {|
          cofe_mor_car :=
            λ τ2i,
            {|
              cofe_mor_car :=
                λ w, (□ ∀ v, τ1i v → WP (App (# w) (# v)) @ ⊤ {{τ2i}})%I
            |}
        |}
    |}.
  Solve Obligations with
  repeat intros ?; cbn;
    try apply always_ne;
    try apply forall_ne=>?; try apply impl_ne; trivial;
      try apply wp_ne =>?;
          try match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.

  Program Definition interp_forall :
    ((leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ)) -n>
    leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car :=
        λ τi,
        {|
          cofe_mor_car :=
            λ w,
            (∀ (τ'i : {f : (leibniz_val -n> iProp lang Σ) |
                       Val_to_IProp_Persistent f}),
                □ (WP TApp (# w) @ ⊤ {{λ v, (τi (`τ'i) v)}}))%I
        |}
    |}.
  Next Obligation.
  Proof.
    intros τ τ' x y Hxy; cbn; rewrite Hxy; trivial.
  Qed.
  Next Obligation.
    intros n f g Hfg x; cbn.
    apply forall_ne=> P.
    apply always_ne, wp_ne => w.
    rewrite Hfg; trivial.
  Qed.

  Program Definition interp_rec_pre :
    ((leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ)) -n>
    (leibniz_val -n> iProp lang Σ) -n>
    (leibniz_val -n> iProp lang Σ) :=
    {|
      cofe_mor_car :=
        λ τi,
        {| cofe_mor_car :=
             λ rec_appr,
             {|
               cofe_mor_car := λ w, (□ (∃ v, w = FoldV v ∧ ▷ (τi rec_appr v)))%I
             |}
        |}
    |}.
  Next Obligation.
  Proof.
    intros τi rec_appr n x y Hxy; rewrite Hxy; trivial.
  Qed.
  Next Obligation.
  Proof.
    intros τi n f g Hfg x. cbn.
    apply always_ne, exist_ne =>w; rewrite Hfg; trivial.
  Qed.
  Next Obligation.
  Proof.
    intros n τi τi' Hτi f x. cbn.
    apply always_ne, exist_ne =>w; rewrite Hτi; trivial.
  Qed.

  Global Instance interp_rec_pre_contr
           (τi : (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ))
    :
      Contractive (interp_rec_pre τi).
  Proof.
    intros n f g H w; cbn.
    apply always_ne, exist_ne; intros e; apply and_ne; trivial.
    apply later_contractive =>i Hi.
    rewrite H; trivial.
  Qed.

  Program Definition interp_rec :
    ((leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ)) -n>
    (leibniz_val -n> iProp lang Σ)
    :=
      {|
        cofe_mor_car := λ τi, fixpoint (interp_rec_pre τi)
      |}.
  Next Obligation.
  Proof. intros n f g H; apply fixpoint_ne => z; rewrite H; trivial. Qed.

  Program Fixpoint interp (τ : type) {struct τ}
    : (leibniz_var -n> (leibniz_val -n> iProp lang Σ)) -n> leibniz_val -n> iProp lang Σ
    :=
      match τ with
        | TUnit => {| cofe_mor_car := λ Δ, interp_unit |}
        | TProd τ1 τ2 =>
          {| cofe_mor_car := λ Δ, interp_prod (interp τ1 Δ) (interp τ2 Δ)|}
        | TSum τ1 τ2 => {| cofe_mor_car := λ Δ,interp_sum (interp τ1 Δ) (interp τ2 Δ)|}
        | TArrow τ1 τ2 => {|cofe_mor_car := λ Δ, interp_arrow (interp τ1 Δ) (interp τ2 Δ)|}
        | TVar v => {| cofe_mor_car :=
                        λ Δ : (leibniz_var -n> (leibniz_val -n> iProp lang Σ)), (Δ v) |}
        | TForall τ' =>
          {| cofe_mor_car := λ Δ,
                             interp_forall (extend_context_interp_apply Δ (interp τ'))|}
        | TRec τ' =>
          {| cofe_mor_car := λ Δ,
                             interp_rec (extend_context_interp_apply Δ (interp τ'))|}
        end%I.
  Solve Obligations with
  repeat intros ?; match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.

  Class context_interp_Persistent (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ) :=
    contextinterppersistent : ∀ v : var, Val_to_IProp_Persistent (Δ v).

  Global Instance Val_to_IProp_Persistent_Persistent
           (f : leibniz_val -n> iProp lang Σ)
           {Hf : Val_to_IProp_Persistent f}
           (v : val)
    : PersistentP (f v).
  Proof. apply Hf. Qed.

  Global Instance interp_Persistent
         τ (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
         {HΔ : context_interp_Persistent Δ}
    : Val_to_IProp_Persistent (interp τ Δ).
  Proof.
    revert Δ HΔ.
    induction τ; cbn; intros Δ HΔ v; try apply _.
    - rewrite /PersistentP /interp_rec fixpoint_unfold /interp_rec_pre; cbn.
      apply always_intro'; trivial.
    - apply Val_to_IProp_Persistent_Persistent; apply HΔ.
  Qed.

  Global Instance Persistent_context_interp_rel Δ Γ vs
           {HΔ : context_interp_Persistent Δ}
    : PersistentP (Π∧ zip_with(λ τ v, interp τ Δ v) Γ vs)%I.
  Proof. typeclasses eauto. Qed.

  Global Program Instance extend_context_interp_Persistent f Δ
           (Hf : Val_to_IProp_Persistent f)
           {HΔ : context_interp_Persistent Δ}
    : context_interp_Persistent (@extend_context_interp f Δ).
  Next Obligation.
    intros f Δ Hf HΔ v w; destruct v; cbn; trivial.
    apply HΔ.
  Qed.

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
      end.

  Lemma interp_unused_contex_irrel
        (m n : nat)
        (Δ Δ' : leibniz_var -n> leibniz_val -n> iProp lang Σ)
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
  Qed.

  Program Definition hop_context_interp (m n : nat) :
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) -n>
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) :=
    {| cofe_mor_car :=
         λ Δ,
         {| cofe_mor_car := λ v, if lt_dec v m then Δ v else Δ (v - n) |}
    |}.
  Next Obligation.
  Proof. intros ?????? Hxy; destruct Hxy; trivial. Qed.
  Next Obligation.
  Proof.
    intros ????? Hfg ?; cbn. destruct lt_dec; rewrite Hfg; trivial.
  Qed.

  Lemma extend_bofore_hop_context_interp (m n : nat)
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
        (τi : leibniz_val -n> iProp lang Σ)
        (v : var)
    :
      (extend_context_interp τi (hop_context_interp m n Δ)
                             (if lt_dec v (S m) then v else n + v))
        ≡ (hop_context_interp (S m) n (extend_context_interp τi Δ)
                              (if lt_dec v (S m) then v else n + v)).
  Proof.
    destruct v; cbn; trivial.
    repeat (destruct lt_dec; cbn); auto with omega.
    destruct (n + S v - n) eqn:Heq1;
      destruct (n + S v) eqn:Heq2; try destruct lt_dec; auto with omega.
    match goal with
      [ |- _ _ _ Δ ?a ≡ _ _ _ Δ ?b] => assert (Heq : a = b) by omega; rewrite Heq; trivial
    end.
  Qed.

  Lemma interp_subst_weaken
        (m n : nat)
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
        (τ : type)
    : interp τ Δ ≡ interp τ.[iter m up (ren (+n))] (hop_context_interp m n Δ).
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
      { (** An incompleteness in omega and lia! *)
        clear.
        replace (x + n) with (n + x) by omega.
        induction n; cbn; auto with omega.
        induction x; cbn; trivial.
      }
    - properness; trivial.
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      rewrite IHτ.
      apply interp_unused_contex_irrel.
      intros w; rewrite extend_bofore_hop_context_interp; trivial.
  Qed.

  Lemma interp_ren_S (τ : type)
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
        (τi : leibniz_val -n> iProp lang Σ)
    : interp τ Δ ≡ interp τ.[ren (+1)] (extend_context_interp τi Δ).
  Proof.
    rewrite (interp_subst_weaken 0 1).
    apply interp_unused_contex_irrel.
    { clear. intros [|v]; cbn; trivial. }
  Qed.

  Local Opaque eq_nat_dec.

  Program Definition context_interp_insert (m : nat) :
    (leibniz_val -n> iProp lang Σ) -n>
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) -n>
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) :=
    {| cofe_mor_car :=
         λ τi,
         {| cofe_mor_car :=
              λ Δ,
              {| cofe_mor_car :=
                   λ v, if lt_dec v m then Δ v else
                          if eq_nat_dec v m then τi else Δ (v - 1)
              |}
         |}
    |}.
  Next Obligation.
  Proof. intros m τi Δ n x y Hxy; destruct Hxy; trivial. Qed.
  Next Obligation.
  Proof.
    intros m τi n Δ Δ' HΔ x; cbn;
      destruct lt_dec; try destruct eq_nat_dec; auto.
  Qed.
  Next Obligation.
  Proof.
    intros m n f g Hfg F Δ x; cbn;
      destruct lt_dec; try destruct eq_nat_dec; auto.
  Qed.

  Lemma extend_context_interp_insert (m : nat)
        (τi : leibniz_val -n> iProp lang Σ)
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
        (Ti : leibniz_val -n> iProp lang Σ)
    :
      (extend_context_interp Ti (context_interp_insert m τi Δ))
        ≡ (context_interp_insert (S m) τi (extend_context_interp Ti Δ)).
  Proof.
    intros [|v]; cbn; trivial.
    repeat destruct lt_dec; trivial;
      repeat destruct eq_nat_dec; cbn; auto with omega.
    destruct v; cbn; auto with omega.
    replace (v - 0) with v by omega; trivial.
  Qed.

  Lemma context_interp_insert_O_extend
        (τi : leibniz_val -n> iProp lang Σ)
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
    :
      (context_interp_insert O τi Δ)
        ≡ (extend_context_interp τi Δ).
  Proof.
    intros [|v]; cbn; trivial.
    repeat destruct lt_dec; trivial;
      repeat destruct eq_nat_dec; cbn; auto with omega.
    destruct v; cbn; auto with omega.
  Qed.

  Lemma iter_up_subst_type (m : nat) (τ : type) (x : var)
    :
      (iter m up (τ .: ids) x) =
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
        (m : nat)
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
        (τ : type)
        (τ' : type)
    : interp τ (context_interp_insert m (interp τ'.[ren (+m)] Δ) Δ)
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
      replace (τ'.[ren (+S m)]) with ((τ'.[ren (+m)]).[ren (+1)]) by (asimpl; trivial).
      rewrite -interp_ren_S; trivial.
    - rewrite iter_up_subst_type.
      repeat destruct lt_dec; repeat destruct eq_nat_dec;
        unfold ids; asimpl; trivial.
    - properness; trivial.
      rewrite extend_context_interp_insert.
      change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids)).
      rewrite -IHτ.
      replace (τ'.[ren (+S m)]) with ((τ'.[ren (+m)]).[ren (+1)]) by (asimpl; trivial).
      rewrite -interp_ren_S; trivial.
  Qed.

  Lemma interp_subst
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
        (τ : type)
        (τ' : type)
    : interp τ (extend_context_interp (interp τ' Δ) Δ) ≡ interp τ.[τ'/] Δ.
  Proof.
    rewrite -(interp_subst_iter_up O Δ τ τ').
    rewrite context_interp_insert_O_extend.
    asimpl; trivial.
  Qed.

  Lemma zip_with_context_interp_subst
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ) (Γ : list type)
        (vs : list leibniz_val) (τi : leibniz_val -n> iProp lang Σ) :
    ((Π∧ zip_with (λ τ v, interp τ Δ v) Γ vs)%I)
      ≡ (Π∧ zip_with (λ τ v, interp τ (extend_context_interp τi Δ) v)
                    (map (λ t : type, t.[ren (+1)]) Γ) vs)%I.
  Proof.
    revert Δ vs τi.
    induction Γ as [|Γ]; intros Δ vs τi; cbn; trivial.
    destruct vs; cbn; trivial.
    apply and_proper.
    - apply interp_ren_S.
    - apply IHΓ.
  Qed.

End logrel.