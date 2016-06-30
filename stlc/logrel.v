From iris.program_logic Require Export weakestpre.
From iris_logrel.stlc Require Export lang typing.

(** interp : is a unary logical relation. *)
Section logrel.
Context {Σ : iFunctor}.
Implicit Types P Q R : iProp lang Σ.

Fixpoint interp (τ : type) (w : val) : iProp lang Σ :=
  match τ with
  | TUnit => w = UnitV
  | TProd τ1 τ2 => ∃ w1 w2, w = PairV w1 w2 ∧ interp τ1 w1 ∧ interp τ2 w2
  | TSum τ1 τ2 =>
     (∃ w1, w = InjLV w1 ∧ interp τ1 w1) ∨ (∃ w2, w = InjRV w2 ∧ interp τ2 w2)
  | TArrow τ1 τ2 =>
     □ ∀ v, interp τ1 v → wp ⊤ (App (of_val w) (of_val v)) (interp τ2)
  end%I.

Global Instance interp_always_stable τ v : PersistentP (interp τ v).
Proof. revert v; induction τ=> v /=; apply _. Qed.

Lemma typed_subst_invariant Γ e τ s1 s2 :
  typed Γ e τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ s1 s2 x, (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { rewrite /up=> s1 s2 [|x] //=; auto with f_equal omega. }
  induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with omega.
Qed.

Definition env_subst (vs : list val) (x : var) : expr :=
  from_option id (Var x) (of_val <$> vs !! x).

Lemma typed_subst_head_simpl Δ τ e w ws :
  typed Δ e τ → length Δ = S (length ws) →
  e.[# w .: env_subst ws] = e.[env_subst (w :: ws)].
Proof.
  intros H1 H2.
  rewrite /env_subst. eapply typed_subst_invariant; eauto=> /= -[|x] ? //=.
  destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first omega; simpl.
  by rewrite Hv.
Qed.
End logrel.
