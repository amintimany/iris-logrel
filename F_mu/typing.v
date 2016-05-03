Require Import F_mu.lang.
Require Import iris.prelude.base.

Inductive type :=
| TUnit : type
| TProd : type → type → type
| TSum : type → type → type
| TArrow : type → type → type
| TRec (τ : {bind 1 of type})
| TVar (x : var)
| TForall (τ : {bind 1 of type}).

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Inductive closed_type (k : nat) : type → Prop :=
| CLT_TUnit : closed_type k TUnit
| CLT_TProd t t' : closed_type k t → closed_type k t' → closed_type k (TProd t t')
| CLT_TSum t t' : closed_type k t → closed_type k t' → closed_type k (TSum t t')
| CLT_TArrow t t' : closed_type k t → closed_type k t' → closed_type k (TArrow t t')
| CLT_TRec t : closed_type (S k) t → closed_type k (TRec t)
| CLT_TVar n : n < k → closed_type k (TVar n)
| CLT_TForall t : closed_type (S k) t → closed_type k (TForall t).

Hint Constructors closed_type.

Lemma closed_type_prod_1 {k : nat} {τ1 τ2 : type} :
  closed_type k (TProd τ1 τ2) → closed_type k τ1.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_prod_2 {k : nat} {τ1 τ2 : type} :
  closed_type k (TProd τ1 τ2) → closed_type k τ2.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_sum_1 {k : nat} {τ1 τ2 : type} :
  closed_type k (TSum τ1 τ2) → closed_type k τ1.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_sum_2 {k : nat} {τ1 τ2 : type} :
  closed_type k (TSum τ1 τ2) → closed_type k τ2.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_arrow_1 {k : nat} {τ1 τ2 : type} :
  closed_type k (TArrow τ1 τ2) → closed_type k τ1.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_arrow_2 {k : nat} {τ1 τ2 : type} :
  closed_type k (TArrow τ1 τ2) → closed_type k τ2.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_rec {k : nat} {τ : type} :
  closed_type k (TRec τ) → closed_type (S k) τ.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_var {k : nat} {v : var} :
  closed_type k (TVar v) → v < k.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_forall {k : nat} {τ : type} :
  closed_type k (TForall τ) → closed_type (S k) τ.
Proof. intros H; inversion H; subst; trivial. Qed.

Local Hint Resolve closed_type_prod_1 closed_type_prod_2 closed_type_sum_1
      closed_type_sum_2 closed_type_arrow_1 closed_type_arrow_2
      closed_type_rec closed_type_var closed_type_forall.

Lemma closed_type_S (k : nat) (τ : type) : closed_type k τ → closed_type (S k) τ.
Proof. intros H; induction H; auto using closed_type with omega. Qed.

Lemma closed_type_le (k k' : nat) (τ : type) : k ≤ k' → closed_type k τ → closed_type k' τ.
Proof. intros H; induction H; auto using closed_type, closed_type_S with omega. Qed.

Definition closed_ctx (k : nat) (Γ : list type) := Forall (closed_type k) Γ.

Lemma closed_ctx_S (k : nat) (Γ : list type) : closed_ctx k Γ → closed_ctx (S k) Γ.
Proof. intros H. eapply Forall_impl; [|apply closed_type_S]; trivial. Qed.

Lemma closed_ctx_le (k k' : nat) (Γ : list type) : k ≤ k' → closed_ctx k Γ → closed_ctx k' Γ.
Proof. intros H; induction H; auto using closed_type, closed_ctx_S with omega. Qed.

Lemma closed_ctx_closed_type (k : nat) (Γ : list type) (x : var) (τ : type) :
  closed_ctx k Γ → Γ !! x = Some τ → closed_type k τ.
Proof. intros; eapply list.Forall_lookup; eauto. Qed.

Lemma closed_ctx_map (k k' : nat) (Γ : list type) (f : type → type) :
  closed_ctx k Γ →
  (∀ τ, closed_type k τ → closed_type k' (f τ)) →
  closed_ctx k' (map f Γ).
Proof.
  revert k k' f.
  induction Γ; intros k k' f H1 H2; cbn; constructor;
  inversion H1; subst; auto.
  eapply IHΓ; eauto.
Qed.

Program Fixpoint zipwith_Forall {A : Type} {P : A → Prop} (l : list A) (H : Forall P l) :
  list ({x : A | P x}) :=
  match l as u return Forall P u → _ with
  | [] => λ _, []
  | a :: l' => λ H, (a ↾ _) :: (zipwith_Forall l' _)
  end H.
Solve Obligations with repeat intros ?; match goal with [H : Forall _ _ |- _] => inversion H; trivial end.

Lemma zipwith_Forall_lookup {A : Type} {P : A → Prop} (l : list A) (Hf : Forall P l) (x : A) (n : nat) :
  l !! n = Some x → {Hx : P x| (zipwith_Forall l Hf) !! n = Some (x ↾ Hx)}.
Proof.
  revert n.
  induction l; intros n H1; cbn in *; [inversion H1|].
  destruct n; [cbn in *; inversion H1; subst|]; eauto.
Qed.  
  
Definition closed_ctx_list (k : nat) (Γ : list type) (H : closed_ctx k Γ) :
  list ({τ : type | closed_type k τ}) := zipwith_Forall Γ H.

Inductive typed (k : nat) (Γ : list type) : expr → type → Prop :=
| Var_typed x τ : (closed_ctx k Γ) → Γ !! x = Some τ → typed k Γ (Var x) τ
| Unit_typed : closed_ctx k Γ → typed k Γ Unit TUnit
| Pair_typed e1 e2 τ1 τ2 :
    typed k Γ e1 τ1 → typed k Γ e2 τ2 → typed k Γ (Pair e1 e2) (TProd τ1 τ2)
| Fst_typed e τ1 τ2 : typed k Γ e (TProd τ1 τ2) → typed k Γ (Fst e) τ1
| Snd_typed e τ1 τ2 : typed k Γ e (TProd τ1 τ2) → typed k Γ (Snd e) τ2
| InjL_typed e τ1 τ2 : typed k Γ e τ1 → closed_type k τ2 → typed k Γ (InjL e) (TSum τ1 τ2)
| InjR_typed e τ1 τ2 : typed k Γ e τ2 → closed_type k τ1 → typed k Γ (InjR e) (TSum τ1 τ2)
| Case_typed e0 e1 e2 τ1 τ2 ρ :
    typed k Γ e0 (TSum τ1 τ2) →
    typed k (τ1 :: Γ) e1 ρ → typed k (τ2 :: Γ) e2 ρ →
    typed k Γ (Case e0 e1 e2) ρ
| Lam_typed e τ1 τ2 :
    typed k (τ1 :: Γ) e τ2 → typed k Γ (Lam e) (TArrow τ1 τ2)
| App_typed e1 e2 τ1 τ2 :
    typed k Γ e1 (TArrow τ1 τ2) → typed k Γ e2 τ1 → typed k Γ (App e1 e2) τ2
| TLam_typed e τ :
    typed (S k) (map (λ t, t.[ren (+1)]) Γ) e τ →
    typed k Γ (TLam e) (TForall τ)
| TApp_typed e τ τ':
    typed k Γ e (TForall τ) → closed_type k τ' → typed k Γ (TApp e) (τ.[τ'/])
| TFold e τ :
    typed (S k) (map (λ t, t.[ren (+1)]) Γ) e τ →
    typed k Γ (Fold e) (TRec τ)
| TUnfold e τ : typed k Γ e (TRec τ) → typed k Γ (Unfold e) (τ.[(TRec τ)/])
.

Lemma closed_type_subst_invariant k τ s1 s2 :
  closed_type k τ → (∀ x, x < k → s1 x = s2 x) → τ.[s1] = τ.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ {A} `{Ids A} `{Rename A}
            (s1 s2 : nat → A) x, (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { intros A H1 H2. rewrite /up=> s1 s2 [|x] //=; auto with f_equal omega. }
  induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with omega.
Qed.

Fixpoint iter (n : nat) `(f : A → A) :=
  match n with
  | O => λ x, x
  | S n' => λ x, f (iter n' f x)
  end.

Lemma iter_S (n : nat) `(f : A → A) (x : A) : iter (S n) f x = iter n f (f x).
Proof.
  induction n; cbn; trivial.
  rewrite -IHn; trivial.
Qed.
  
Lemma iter_upren (m x : nat) f : iter m upren f x = if lt_dec x m then x else m + (f (x - m)).
Proof.
  revert x; induction m; cbn; auto with omega.
  intros x; destruct x; cbn; trivial.
  rewrite IHm; repeat destruct lt_dec; auto with omega.  
Qed.
  
Lemma iter_up (m x : nat) (f : var → type) : iter m up f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
Proof.
  revert x; induction m; cbn; auto with omega.
  intros x; destruct x; cbn; asimpl; trivial.
  intros x; destruct x; cbn; asimpl; trivial.
  rewrite IHm; repeat destruct lt_dec; auto with omega.
  asimpl; trivial.
Qed.

Lemma closed_type_S_ren1:
  ∀ (τ : type) (n m : nat) (k : nat) (Hle : m ≤ k),
    (closed_type (n + k) τ.[ren ((iter m upren) (+n))] → closed_type k τ).
Proof.
  induction τ; intros n m k Hle H; inversion H; subst; constructor; eauto 2 with omega;
  try eapply (IHτ n (S m)); asimpl in *; auto with omega.
  rewrite iter_upren in H1; destruct lt_dec; cbn in *; omega.
Qed.

Lemma closed_type_S_ren2:
  ∀ (τ : type) (n m : nat) (k : nat),
    (closed_type k τ → closed_type (n + k) τ.[ren ((iter m upren) (+n))]).
Proof.
  induction τ; intros n m k H; inversion H; subst; constructor; eauto 2 with omega;
  try (replace (up (ren (iter m upren (+n)))) with
    (ren (iter (S m) upren (+n))) by (asimpl; trivial);
    replace (S (n + k)) with (n + (S k)) by omega; auto with omega).
  rewrite iter_upren; destruct lt_dec; cbn in *; omega.
Qed.

Lemma closed_type_pred_ren1:
  ∀ (τ : type) (n m : nat) (k : nat),
    (closed_type k τ.[ren ((iter m upren) (λ x, x - n))] → closed_type (n + k) τ).
Proof.
  induction τ; intros n m k H; inversion H; subst; constructor; eauto 2 with omega;  
  try (replace (S (n + k)) with (n + (S k)) by omega;
  apply IHτ with (S m);
  replace (up (ren (iter m upren (λ x, x - n)))) with
  (ren (iter (S m) upren (λ x, x - n))) in H1 by (asimpl; trivial); trivial).
  rewrite iter_upren in H1; destruct lt_dec; omega.
Qed.

Lemma closed_type_pred_ren2:
  ∀ (τ : type) (n m : nat) (k : nat) (Hle : m < k),
    closed_type (n + k) τ → closed_type k τ.[ren ((iter m upren) (λ x, x - n))].
Proof.
  induction τ; intros n m k Hle H; inversion H; subst; constructor; eauto 2 with omega;
  try (replace (up (ren (iter m upren (λ x, x - n)))) with
    (ren (iter (S m) upren (λ x, x - n))) by (asimpl; trivial); trivial;
    eapply (IHτ n (S m)); asimpl in *; auto with omega).
  rewrite iter_upren; destruct lt_dec; omega.
Qed.

Lemma closed_ctx_map_S:
  ∀ (k : nat) (Γ : list type), closed_ctx (S k) (map (λ t : type, t.[ren (+1)]) Γ) → closed_ctx k Γ.
Proof.
  intros k Γ H.
  induction Γ; constructor; inversion H; subst.
  eapply closed_type_S_ren1 with 1 0; cbn; auto with omega.
  apply IHΓ; trivial.
Qed.

Lemma closed_type_subst_up_subst (m : nat) (k : nat) (τ : {bind type}) (τ' : type) :
  closed_type k τ' → closed_type (m + k) τ → closed_type (m + k) τ.[iter m up (τ' .: ids)].
Proof.
  revert m k τ'.
  induction τ; intros m k τ' H1 H2; try constructor; inversion H2; subst; auto;
  try (change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids));
        change (S (m + k)) with (S m + k);
        apply IHτ; cbn; auto using closed_type_S).
  cbn; rewrite iter_up; destruct lt_dec.
  constructor; auto.
  asimpl; apply (closed_type_S_ren2 _ m 0).
  remember (x - m) as u; destruct u; try constructor; auto with omega.
Qed.

Lemma closed_type_all_closed_subst (m k : nat) (τ : type) (f : var → type) :
  (∀ x, closed_type k (f x)) → closed_type (m + k) τ.[iter m up f].
Proof.
  revert m k.
  induction τ; intros m k H; try constructor; auto;
  try (change (up (iter m up f)) with (iter (S m) up f);
        change (S (m + k)) with (S m + k);
        apply IHτ; cbn; auto using closed_type_S).
  cbn; rewrite iter_up; destruct lt_dec.
  constructor; auto with omega.
  asimpl; apply (closed_type_S_ren2 _ m 0); trivial.
Qed.

Lemma closed_type_rel_closed_subst (n k : nat) (τ : type) (f : var → type) :
  (∀ x, x < n → closed_type k (f x)) → closed_type n τ → closed_type k τ.[f].
Proof.
  revert f n k.
  induction τ; intros f n k H1 H2; inversion H2; subst; try constructor; cbn; auto;
  try ((eapply IHτ + eapply IHτ1 + eapply IHτ2); cbn; eauto 2 using closed_type_S; fail);
  try (eapply IHτ; eauto 2;
       intros x Hx; destruct x; asimpl;
       try constructor; auto using (closed_type_S_ren2 _ 1 0) with omega).
Qed.

Lemma closed_type_subst_wiht_up (k m : nat) (τ : type) (τ' : type) :
  m ≤ k → closed_type (k - m) τ' → closed_type (S k) τ →
  closed_type k τ.[iter m up (τ' .: ids)].
Proof.
  revert k m τ'.
  induction τ; intros k m τ' Hlt H1 H2; inversion H2; subst; try constructor; auto.
  - change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids));
    apply IHτ; auto with omega.
  - cbn.
    rewrite iter_up.
    destruct lt_dec.
    + auto with omega.
    + asimpl.
      remember (x - m) as u.
      destruct u; cbn in *.
      * replace k with (m + (k - m)) by omega.
        apply (closed_type_S_ren2 _ m 0); trivial.
      * asimpl; constructor; omega.
  - change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids));
    apply IHτ; auto with omega.
Qed.

Lemma closed_type_subst (k : nat) (τ : type) (τ' : type) :
  closed_type k τ' → closed_type (S k) τ → closed_type k τ.[τ'/].
Proof.
  intros H1 H2.
  apply (closed_type_subst_wiht_up _ 0);
    try replace (k - 0) with k; auto with omega.
Qed.

Lemma typed_closed_ctx_closed_type (k : nat) (Γ : list type) (e : expr) (τ : type) :
  typed k Γ e τ → closed_ctx k Γ ∧ closed_type k τ.
Proof.
  intros H; induction H; intuition; eauto 3 using closed_ctx_closed_type;
  match goal with
  | [H : closed_ctx _ (_ :: _) |- _] =>
    inversion H; clear H; subst;
    auto
  | [H : closed_type _ _ |- _] =>
    inversion H; clear H; subst;
    auto using closed_ctx_map_S, closed_type_subst
  end.
Qed.

Lemma typed_closed_ctx (k : nat) (Γ : list type) (e : expr) (τ : type) :
  typed k Γ e τ → closed_ctx k Γ.
Proof. apply typed_closed_ctx_closed_type. Qed.

Lemma typed_closed_type (k : nat) (Γ : list type) (e : expr) (τ : type) :
  typed k Γ e τ → closed_type k τ.
Proof. apply typed_closed_ctx_closed_type. Qed.

Local Hint Extern 1 =>
match goal with [H : context [length (map _ _)] |- _] => rewrite map_length in H end
: typed_subst_invariant.

Lemma typed_subst_invariant k Γ e τ s1 s2 :
  typed k Γ e τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ {A} `{Ids A} `{Rename A}
            (s1 s2 : nat → A) x, (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { intros A H1 H2. rewrite /up=> s1 s2 [|x] //=; auto with f_equal omega. }
  induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with omega typed_subst_invariant.
Qed.

Lemma closed_ctx_map_S_back (k : nat) (Γ : list type) (e : expr) (τ : type) :
  closed_ctx k Γ →
  closed_ctx (S k) (map (λ t : type, t.[ren (+1)]) Γ).
Proof.
  intros H.
  eapply closed_ctx_map; [eassumption|].
  clear; intros τ' H'.
  set (HW := closed_type_S_ren2 τ' 1 0); cbn in HW; apply HW; trivial.
Qed.