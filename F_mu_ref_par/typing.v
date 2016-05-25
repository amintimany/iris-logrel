Require Import prelude.base.
Require Import F_mu_ref_par.lang.

Inductive type :=
| TUnit : type
| TNat : type
| TBool : type
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

Fixpoint NatBinOP_res_type (op : NatBinOP) : type :=
  match op with
  | Add => TNat | Sub => TNat
  | Eq => TBool | Le => TBool | Lt => TBool
  end.

Inductive EqType : type → Prop :=
| EqTUnit : EqType TUnit
| EqTNat : EqType TNat
| EqTBool : EqType TBool
| EqTProd τ τ' : EqType τ → EqType τ' → EqType (TProd τ τ')
| EqSum τ τ' : EqType τ → EqType τ' → EqType (TSum τ τ')
.

Inductive typed (Γ : list type) : expr → type → Prop :=
| Var_typed x τ : Γ !! x = Some τ → typed Γ (Var x) τ
| Unit_typed : typed Γ Unit TUnit
| Nat_typed n : typed Γ (♯ n) TNat
| Bool_typed b : typed Γ (♭ b) TBool
| NBOP_typed op e1 e2 :
    typed Γ e1 TNat → typed Γ e2 TNat →
    typed Γ (NBOP op e1 e2) (NatBinOP_res_type op)
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
| If_typed e0 e1 e2 τ :
    typed Γ e0 TBool → typed Γ e1 τ → typed Γ e2 τ →
    typed Γ (If e0 e1 e2) τ
| Lam_typed e τ1 τ2 :
    typed (TArrow τ1 τ2 :: τ1 :: Γ) e τ2 → typed Γ (Lam e) (TArrow τ1 τ2)
| App_typed e1 e2 τ1 τ2 :
    typed Γ e1 (TArrow τ1 τ2) → typed Γ e2 τ1 → typed Γ (App e1 e2) τ2
| TLam_typed e τ :
    typed (map (λ t, t.[ren (+1)]) Γ) e τ →
    typed Γ (TLam e) (TForall τ)
| TApp_typed e τ τ':
    typed Γ e (TForall τ) → typed Γ (TApp e) (τ.[τ'/])
| TFold e τ :
    typed Γ e (τ.[(TRec τ)/]) →
    typed Γ (Fold e) (TRec τ)
| TUnfold e τ : typed Γ e (TRec τ) → typed Γ (Unfold e) (τ.[(TRec τ)/])
| TFork e : typed Γ e TUnit → typed Γ (Fork e) TUnit
| TAlloc e τ : typed Γ e τ → typed Γ (Alloc e) (Tref τ)
| TLoad e τ : typed Γ e (Tref τ) → typed Γ (Load e) τ
| TStore e e' τ :
    typed Γ e (Tref τ) → typed Γ e' τ → typed Γ (Store e e') TUnit
| TCAS e1 e2 e3 τ :
    EqType τ →
    typed Γ e1 (Tref τ) → typed Γ e2 τ → typed Γ e3 τ →
    typed Γ (CAS e1 e2 e3) TBool
.

Local Hint Extern 1 =>
match goal with [H : context [length (map _ _)] |- _] =>
                rewrite map_length in H end : typed_subst_invariant.

Lemma typed_subst_invariant Γ e τ s1 s2 :
  typed Γ e τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ {A} `{Ids A} `{Rename A}
            (s1 s2 : nat → A) x, (x ≠ 0 → s1 (pred x) = s2 (pred x)) →
                               up s1 x = up s2 x).
  { intros A H1 H2. rewrite /up=> s1 s2 [|x] //=; auto with f_equal omega. }
  (induction Htyped => s1 s2 Hs; f_equal/=);
    eauto using lookup_lt_Some with omega typed_subst_invariant.
Qed.

Definition env_subst (vs : list val) (x : var) : expr :=
  from_option (Var x) (of_val <$> vs !! x).

Lemma context_gen_weakening ξ Γ' Γ e τ :
  typed (Γ' ++ Γ) e τ →
  typed (Γ' ++ ξ ++ Γ) e.[iter (List.length Γ') up (ren (+ (List.length ξ)))] τ.
Proof.
  intros H1.
  remember (Γ' ++ Γ) as Ξ. revert Γ' Γ ξ HeqΞ.
  induction H1 => Γ1 Γ2 ξ HeqΞ; subst; asimpl in *; eauto using typed.
  - rewrite iter_up; destruct lt_dec as [Hl | Hl].
    + constructor. rewrite lookup_app_l; trivial. by rewrite lookup_app_l in H.
    + asimpl. constructor. rewrite lookup_app_r; auto with omega.
      rewrite lookup_app_r; auto with omega.
      rewrite lookup_app_r in H; auto with omega.
      match goal with
        |- _ !! ?A = _ => by replace A with (x - List.length Γ1) by omega
      end.
  - econstructor; eauto.
    + eapply (IHtyped2 (_ :: Γ1) Γ2 ξ Logic.eq_refl).
    + eapply (IHtyped3 (_ :: Γ1) Γ2 ξ Logic.eq_refl).
  - constructor.
    eapply (IHtyped (_ :: _ :: Γ1) Γ2 ξ Logic.eq_refl).
  - constructor.
    specialize (IHtyped
                  (map (λ t : type, t.[ren (+1)]) Γ1)
                  (map (λ t : type, t.[ren (+1)]) Γ2)
                  (map (λ t : type, t.[ren (+1)]) ξ)).
    asimpl in *. rewrite ?map_length in IHtyped.
    repeat rewrite map_app. apply IHtyped.
    by repeat rewrite map_app.
Qed.

Lemma context_weakening ξ Γ e τ :
  typed Γ e τ → typed (ξ ++ Γ) e.[(ren (+ (List.length ξ)))] τ.
Proof. eapply (context_gen_weakening _ []). Qed.

Lemma closed_context_weakening ξ Γ e τ :
  (∀ f, e.[f] = e) → typed Γ e τ → typed (ξ ++ Γ) e τ.
Proof. intros H1 H2. erewrite <- H1. by eapply context_weakening. Qed.

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

Lemma typed_subst_head_simpl_2 Δ τ e w w' ws :
  typed Δ e τ -> List.length Δ = 2 + (List.length ws) →
  e.[# w .: # w' .: env_subst ws] = e.[env_subst (w :: w' :: ws)]
.
Proof.
  intros H1 H2.
  rewrite /env_subst. eapply typed_subst_invariant; eauto => /= -[|[|x]] H3 //=.
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

Lemma empty_env_subst e : e.[env_subst []] = e.
  replace (env_subst []) with (@ids expr _) by reflexivity.
  asimpl; trivial.
Qed.