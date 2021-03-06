From iris_logrel.F_mu_ref_conc Require Export lang.

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
  | Tref (τ : type).

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Fixpoint binop_res_type (op : binop) : type :=
  match op with
  | Add => TNat | Sub => TNat
  | Eq => TBool | Le => TBool | Lt => TBool
  end.

Inductive EqType : type → Prop :=
  | EqTUnit : EqType TUnit
  | EqTNat : EqType TNat
  | EqTBool : EqType TBool
  | EqTProd τ τ' : EqType τ → EqType τ' → EqType (TProd τ τ')
  | EqSum τ τ' : EqType τ → EqType τ' → EqType (TSum τ τ').

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).

Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → Γ ⊢ₜ Var x : τ
  | Unit_typed : Γ ⊢ₜ Unit : TUnit
  | Nat_typed n : Γ ⊢ₜ #n n : TNat
  | Bool_typed b : Γ ⊢ₜ #♭ b : TBool
  | BinOp_typed op e1 e2 :
     Γ ⊢ₜ e1 : TNat → Γ ⊢ₜ e2 : TNat → Γ ⊢ₜ BinOp op e1 e2 : binop_res_type op
  | Pair_typed e1 e2 τ1 τ2 : Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Snd e : τ2
  | InjL_typed e τ1 τ2 : Γ ⊢ₜ e : τ1 → Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 : Γ ⊢ₜ e : τ2 → Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 τ3 :
     Γ ⊢ₜ e0 : TSum τ1 τ2 → τ1 :: Γ ⊢ₜ e1 : τ3 → τ2 :: Γ ⊢ₜ e2 : τ3 →
     Γ ⊢ₜ Case e0 e1 e2 : τ3
  | If_typed e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool → Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ If e0 e1 e2 : τ
  | Rec_typed e τ1 τ2 :
     TArrow τ1 τ2 :: τ1 :: Γ ⊢ₜ e : τ2 → Γ ⊢ₜ Rec e : TArrow τ1 τ2
  | App_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : TArrow τ1 τ2 → Γ ⊢ₜ e2 : τ1 → Γ ⊢ₜ App e1 e2 : τ2
  | TLam_typed e τ :
     subst (ren (+1)) <$> Γ ⊢ₜ e : τ → Γ ⊢ₜ TLam e : TForall τ
  | TApp_typed e τ τ' : Γ ⊢ₜ e : TForall τ → Γ ⊢ₜ TApp e : τ.[τ'/]
  | TFold e τ : Γ ⊢ₜ e : τ.[TRec τ/] → Γ ⊢ₜ Fold e : TRec τ
  | TUnfold e τ : Γ ⊢ₜ e : TRec τ → Γ ⊢ₜ Unfold e : τ.[TRec τ/]
  | TFork e : Γ ⊢ₜ e : TUnit → Γ ⊢ₜ Fork e : TUnit
  | TAlloc e τ : Γ ⊢ₜ e : τ → Γ ⊢ₜ Alloc e : Tref τ
  | TLoad e τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ Load e : τ
  | TStore e e' τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ e' : τ → Γ ⊢ₜ Store e e' : TUnit
  | TCAS e1 e2 e3 τ :
     EqType τ → Γ ⊢ₜ e1 : Tref τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ e3 : τ →
     Γ ⊢ₜ CAS e1 e2 e3 : TBool
where "Γ ⊢ₜ e : τ" := (typed Γ e τ).

Lemma typed_subst_invariant Γ e τ s1 s2 :
  Γ ⊢ₜ e : τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ x Γ, x < length (subst (ren (+1)) <$> Γ) → x < length Γ).
  { intros ??. by rewrite fmap_length. } 
  assert (∀ {A} `{Ids A} `{Rename A} (s1 s2 : nat → A) x,
    (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { intros A H1 H2. rewrite /up=> s1 s2 [|x] //=; auto with f_equal omega. }
  induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with omega.
Qed.
Lemma n_closed_invariant n (e : expr) s1 s2 :
  (∀ f, e.[upn n f] = e) → (∀ x, x < n → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Hnc. specialize (Hnc (ren (+1))).
  revert n Hnc s1 s2.
  induction e => m Hmc s1 s2 H1; asimpl in *; try f_equal;
    try (match goal with H : _ |- _ => eapply H end; eauto;
         try inversion Hmc; try match goal with H : _ |- _ => by rewrite H end;
         fail).
  - apply H1. rewrite iter_up in Hmc. destruct lt_dec; try omega.
    asimpl in *. cbv in x. replace (m + (x - m)) with x in Hmc by omega.
    inversion Hmc; omega.
  - unfold upn in *.
    change (e.[up (up (upn m (ren (+1))))]) with
    (e.[iter (S (S m)) up (ren (+1))]) in *.
    apply (IHe (S (S m))).
    + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end.
    + intros [|[|x]] H2; [by cbv|by cbv |].
      asimpl; rewrite H1; auto with omega.
  - change (e1.[up (upn m (ren (+1)))]) with
    (e1.[iter (S m) up (ren (+1))]) in *.
    apply (IHe0 (S m)).
    + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end.
    + intros [|x] H2; [by cbv |].
      asimpl; rewrite H1; auto with omega.
  - change (e2.[up (upn m (ren (+1)))]) with
    (e2.[upn (S m) (ren (+1))]) in *.
    apply (IHe1 (S m)).
    + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end.
    + intros [|x] H2; [by cbv |].
      asimpl; rewrite H1; auto with omega.
Qed.

Definition env_subst (vs : list val) (x : var) : expr :=
  from_option id (Var x) (of_val <$> vs !! x).

Lemma typed_n_closed Γ τ e : Γ ⊢ₜ e : τ → (∀ f, e.[upn (length Γ) f] = e).
Proof.
  intros H. induction H => f; asimpl; simpl in *; auto with f_equal.
  - apply lookup_lt_Some in H. rewrite iter_up. destruct lt_dec; auto with omega.
  - f_equal. apply IHtyped.
  - by f_equal; rewrite map_length in IHtyped.
Qed.

Lemma n_closed_subst_head_simpl n e w ws :
  (∀ f, e.[upn n f] = e) →
  S (length ws) = n →
  e.[of_val w .: env_subst ws] = e.[env_subst (w :: ws)].
Proof.
  intros H1 H2.
  rewrite /env_subst. eapply n_closed_invariant; eauto=> /= -[|x] ? //=.
  destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first omega; simpl.
  by rewrite Hv.
Qed.

Lemma typed_subst_head_simpl Δ τ e w ws :
  Δ ⊢ₜ e : τ → length Δ = S (length ws) →
  e.[of_val w .: env_subst ws] = e.[env_subst (w :: ws)].
Proof. eauto using n_closed_subst_head_simpl, typed_n_closed. Qed.

Lemma n_closed_subst_head_simpl_2 n e w w' ws :
  (∀ f, e.[upn n f] = e) → (S (S (length ws))) = n →
  e.[of_val w .: of_val w' .: env_subst ws] = e.[env_subst (w :: w' :: ws)].
Proof.
  intros H1 H2.
  rewrite /env_subst. eapply n_closed_invariant; eauto => /= -[|[|x]] H3 //=.
  destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first omega; simpl.
  by rewrite Hv.
Qed.

Lemma typed_subst_head_simpl_2 Δ τ e w w' ws :
  Δ ⊢ₜ e : τ → length Δ = 2 + length ws →
  e.[of_val w .: of_val w' .: env_subst ws] = e.[env_subst (w :: w' :: ws)].
Proof. eauto using n_closed_subst_head_simpl_2, typed_n_closed. Qed.

Lemma empty_env_subst e : e.[env_subst []] = e.
Proof. change (env_subst []) with (@ids expr _). by asimpl. Qed.

(** Weakening *)
Lemma context_gen_weakening ξ Γ' Γ e τ :
  Γ' ++ Γ ⊢ₜ e : τ →
  Γ' ++ ξ ++ Γ ⊢ₜ e.[upn (length Γ') (ren (+ (length ξ)))] : τ.
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
        |- _ !! ?A = _ => by replace A with (x - length Γ1) by omega
      end.
  - econstructor; eauto. by apply (IHtyped2 (_::_)). by apply (IHtyped3 (_::_)).
  - constructor. by apply (IHtyped (_ :: _ :: _)).
  - constructor.
    specialize (IHtyped
      (subst (ren (+1)) <$> Γ1) (subst (ren (+1)) <$> Γ2) (subst (ren (+1)) <$> ξ)).
    asimpl in *. rewrite ?map_length in IHtyped.
    repeat rewrite fmap_app. apply IHtyped.
    by repeat rewrite fmap_app.
Qed.

Lemma context_weakening ξ Γ e τ :
  Γ ⊢ₜ e : τ → ξ ++ Γ ⊢ₜ e.[(ren (+ (length ξ)))] : τ.
Proof. eapply (context_gen_weakening _ []). Qed.

Lemma closed_context_weakening ξ Γ e τ :
  (∀ f, e.[f] = e) → Γ ⊢ₜ e : τ → ξ ++ Γ ⊢ₜ e : τ.
Proof. intros H1 H2. erewrite <- H1. by eapply context_weakening. Qed.
