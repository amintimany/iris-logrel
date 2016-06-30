From iris_logrel.F_mu_ref Require Export lang.

Inductive type :=
  | TUnit : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TForall (τ : {bind 1 of type})
  | Tref (τ : type).

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).

Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → Γ ⊢ₜ Var x : τ
  | Unit_typed : Γ ⊢ₜ Unit : TUnit
  | Pair_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Snd e : τ2
  | InjL_typed e τ1 τ2 : Γ ⊢ₜ e : τ1 → Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 : Γ ⊢ₜ e : τ2 → Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 ρ :
     Γ ⊢ₜ e0 : TSum τ1 τ2 → τ1 :: Γ ⊢ₜ e1 : ρ → τ2 :: Γ ⊢ₜ e2 : ρ →
     Γ ⊢ₜ Case e0 e1 e2 : ρ
  | Lam_typed e τ1 τ2 : τ1 :: Γ ⊢ₜ e : τ2 → Γ ⊢ₜ Lam e : TArrow τ1 τ2
  | App_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : TArrow τ1 τ2 → Γ ⊢ₜ e2 : τ1 → Γ ⊢ₜ App e1 e2 : τ2
  | TLam_typed e τ :
     map (λ t : type, t.[ren (+1)]) Γ ⊢ₜ e : τ → Γ ⊢ₜ TLam e : TForall τ
  | TApp_typed e τ τ' : Γ ⊢ₜ e : TForall τ → Γ ⊢ₜ TApp e : τ.[τ'/]
  | TFold e τ : map (λ t, t.[ren (+1)]) Γ ⊢ₜ e : τ → Γ ⊢ₜ Fold e : TRec τ
  | TUnfold e τ : Γ ⊢ₜ e : TRec τ → Γ ⊢ₜ Unfold e : τ.[TRec τ/]
  | TAlloc e τ : Γ ⊢ₜ e : τ → Γ ⊢ₜ Alloc e : Tref τ
  | TLoad e τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ Load e : τ
  | TStore e e' τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ e' : τ → Γ ⊢ₜ Store e e' : TUnit
where "Γ ⊢ₜ e : τ" := (typed Γ e τ).

Local Hint Extern 1 =>
  match goal with
  | H : context [length (map _ _)] |- _ => rewrite map_length in H
  end : typed_subst_invariant.

Lemma typed_subst_invariant Γ e τ s1 s2 :
  Γ ⊢ₜ e : τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ {A} `{Ids A} `{Rename A}
            (s1 s2 : nat → A) x, (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { intros A H1 H2. rewrite /up=> s1 s2 [|x] //=; auto with f_equal omega. }
  induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with omega typed_subst_invariant.
Qed.

Definition env_subst (vs : list val) (x : var) : expr :=
  from_option id (Var x) (of_val <$> vs !! x).

Lemma typed_subst_head_simpl Δ τ e w ws :
  Δ ⊢ₜ e : τ → length Δ = S (length ws) →
  e.[# w .: env_subst ws] = e.[env_subst (w :: ws)].
Proof.
  intros H1 H2.
  rewrite /env_subst. eapply typed_subst_invariant; eauto=> /= -[|x] ? //=.
  destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first omega; simpl.
    by rewrite Hv.
Qed.

Local Opaque eq_nat_dec.

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
