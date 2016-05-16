Require Import prelude.base.
Require Import F_mu_ref_par.lang.

Inductive type :=
| TUnit : type
| TProd : type → type → type
| TSum : type → type → type
| TArrow : type → type → type
| TRec (τ : {bind 1 of type})
| TVar (x : var)
| TForall (τ : {bind 1 of type})
| Tref (τ : type)
.

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Notation TBOOL := (TSum TUnit TUnit).

Inductive typed (Γ : list type) : expr → type → Prop :=
| Var_typed x τ : Γ !! x = Some τ → typed Γ (Var x) τ
| Unit_typed : typed Γ Unit TUnit
| Pair_typed e1 e2 τ1 τ2 :
    typed Γ e1 τ1 → typed Γ e2 τ2 → typed Γ (Pair e1 e2) (TProd τ1 τ2)
| Fst_typed e τ1 τ2 : typed Γ e (TProd τ1 τ2) → typed Γ (Fst e) τ1
| Snd_typed e τ1 τ2 : typed Γ e (TProd τ1 τ2) → typed Γ (Snd e) τ2
| InjL_typed e τ1 τ2 : typed Γ e τ1 → typed Γ (InjL e) (TSum τ1 τ2)
| InjR_typed e τ1 τ2 : typed Γ e τ2 → typed Γ (InjR e) (TSum τ1 τ2)
| Case_typed e0 e1 e2 τ1 τ2 τ3 :
    typed Γ e0 (TSum τ1 τ2) →
    typed (τ1 :: Γ) e1 τ3 → typed (τ2 :: Γ) e2 τ3 →
    typed Γ (Case e0 e1 e2) τ3
| Lam_typed e τ1 τ2 :
    typed (τ1 :: Γ) e τ2 → typed Γ (Lam e) (TArrow τ1 τ2)
| App_typed e1 e2 τ1 τ2 :
    typed Γ e1 (TArrow τ1 τ2) → typed Γ e2 τ1 → typed Γ (App e1 e2) τ2
| TLam_typed e τ :
    typed (map (λ t, t.[ren (+1)]) Γ) e τ →
    typed Γ (TLam e) (TForall τ)
| TApp_typed e τ τ':
    typed Γ e (TForall τ) → typed Γ (TApp e) (τ.[τ'/])
| TFold e τ :
    typed (map (λ t, t.[ren (+1)]) Γ) e τ →
    typed Γ (Fold e) (TRec τ)
| TUnfold e τ : typed Γ e (TRec τ) → typed Γ (Unfold e) (τ.[(TRec τ)/])
| TFork e : typed Γ e TUnit → typed Γ (Fork e) TUnit
| TAlloc e τ : typed Γ e τ → typed Γ (Alloc e) (Tref τ)
| TLoad e τ : typed Γ e (Tref τ) → typed Γ (Load e) τ
| TStore e e' τ :
    typed Γ e (Tref τ) → typed Γ e' τ → typed Γ (Store e e') TUnit
| TCAS e1 e2 e3 τ :
    typed Γ e1 (Tref τ) → typed Γ e2 τ → typed Γ e3 τ →
    typed Γ (CAS e1 e2 e3) TBOOL
.

Local Hint Extern 1 =>
match goal with [H : context [length (map _ _)] |- _] => rewrite map_length in H end
: typed_subst_invariant.

Lemma typed_subst_invariant Γ e τ s1 s2 :
  typed Γ e τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ {A} `{Ids A} `{Rename A}
            (s1 s2 : nat → A) x, (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { intros A H1 H2. rewrite /up=> s1 s2 [|x] //=; auto with f_equal omega. }
  (induction Htyped => s1 s2 Hs; f_equal/=);
    eauto using lookup_lt_Some with omega typed_subst_invariant.
Qed.

Definition env_subst (vs : list val) (x : var) : expr :=
  from_option (Var x) (of_val <$> vs !! x).

Notation "# v" := (of_val v) (at level 20).

Lemma typed_subst_head_simpl Δ τ e w ws :
  typed Δ e τ -> List.length Δ = S (List.length ws) →
  e.[# w .: env_subst ws] = e.[env_subst (w :: ws)]
.
Proof.
  intros H1 H2.
  rewrite /env_subst. eapply typed_subst_invariant; eauto=> /= -[|x] ? //=.
  destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first omega; simpl.
    by rewrite Hv.
Qed.


Local Opaque eq_nat_dec.

Lemma iter_up_subst_type (m : nat) (τ : type) (x : var) :
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