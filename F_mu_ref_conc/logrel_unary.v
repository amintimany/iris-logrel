From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris_logrel.F_mu_ref_conc Require Export rules typing.
From iris.algebra Require Import list.
From iris.base_logic Require Import big_op namespaces invariants.
Import uPred.

Definition logN : namespace := nroot .@ "logN".

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{heapIG Σ}.
  Notation D := (valC -n> iProp Σ).
  Implicit Types τi : D.
  Implicit Types Δ : listC D.
  Implicit Types interp : listC D → D.

  Program Definition env_lookup (x : var) : listC D -n> D := λne Δ,
    from_option id (cconst True)%I (Δ !! x).
  Solve Obligations with solve_proper_alt.

  Definition interp_unit : listC D -n> D := λne Δ w, (w = UnitV)%I.
  Definition interp_nat : listC D -n> D := λne Δ w, (∃ n, w = #nv n)%I.
  Definition interp_bool : listC D -n> D := λne Δ w, (∃ n, w = #♭v n)%I.

  Program Definition interp_prod
      (interp1 interp2 : listC D -n> D) : listC D -n> D := λne Δ w,
    (∃ w1 w2, w = PairV w1 w2 ∧ interp1 Δ w1 ∧ interp2 Δ w2)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_sum
      (interp1 interp2 : listC D -n> D) : listC D -n> D := λne Δ w,
    ((∃ w1, w = InjLV w1 ∧ interp1 Δ w1) ∨ (∃ w2, w = InjRV w2 ∧ interp2 Δ w2))%I.
  Solve Obligations with solve_proper.

  Program Definition interp_arrow
      (interp1 interp2 : listC D -n> D) : listC D -n> D := λne Δ w,
    (□ ∀ v, interp1 Δ v → WP App (of_val w) (of_val v) {{ interp2 Δ }})%I.
  Solve Obligations with solve_proper.

  Program Definition interp_forall
      (interp : listC D -n> D) : listC D -n> D := λne Δ w,
    (□ ∀ τi : D,
      ■ (∀ v, PersistentP (τi v)) → WP TApp (of_val w) {{ interp (τi :: Δ) }})%I.
  Solve Obligations with solve_proper.

  Definition interp_rec1
      (interp : listC D -n> D) (Δ : listC D) (τi : D) : D := λne w,
    (□ (∃ v, w = FoldV v ∧ ▷ interp (τi :: Δ) v))%I.

  Global Instance interp_rec1_contractive
    (interp : listC D -n> D) (Δ : listC D) : Contractive (interp_rec1 interp Δ).
  Proof.
    intros n τi1 τi2 Hτi w; cbn.
    apply always_ne, exist_ne; intros v; apply and_ne; trivial.
    apply later_contractive =>i Hi. by rewrite Hτi.
  Qed.

  Program Definition interp_rec (interp : listC D -n> D) : listC D -n> D := λne Δ,
    fixpoint (interp_rec1 interp Δ).
  Next Obligation.
    intros interp n Δ1 Δ2 HΔ; apply fixpoint_ne => τi w. solve_proper.
  Qed.

  Program Definition interp_ref_inv (l : loc) : D -n> iProp Σ := λne τi,
    (∃ v, l ↦ᵢ v ∗ τi v)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref
      (interp : listC D -n> D) : listC D -n> D := λne Δ w,
    (∃ l, w = LocV l ∧ inv (logN .@ l) (interp_ref_inv l (interp Δ)))%I.
  Solve Obligations with solve_proper.

  Fixpoint interp (τ : type) : listC D -n> D :=
    match τ return _ with
    | TUnit => interp_unit
    | TNat => interp_nat
    | TBool => interp_bool
    | TProd τ1 τ2 => interp_prod (interp τ1) (interp τ2)
    | TSum τ1 τ2 => interp_sum (interp τ1) (interp τ2)
    | TArrow τ1 τ2 => interp_arrow (interp τ1) (interp τ2)
    | TVar x => env_lookup x
    | TForall τ' => interp_forall (interp τ')
    | TRec τ' => interp_rec (interp τ')
    | Tref τ' => interp_ref (interp τ')
    end.
  Notation "⟦ τ ⟧" := (interp τ).

  Definition interp_env (Γ : list type)
      (Δ : listC D) (vs : list val) : iProp Σ :=
    (length Γ = length vs ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs)%I.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Definition interp_expr (τ : type) (Δ : listC D) (e : expr) : iProp Σ :=
    WP e {{ ⟦ τ ⟧ Δ }}%I.

  Class env_PersistentP Δ :=
    env_persistentP : Forall (λ τi, ∀ v, PersistentP (τi v)) Δ.
  Global Instance env_persistent_nil : env_PersistentP [].
  Proof. by constructor. Qed.
  Global Instance env_persistent_cons τi Δ :
    (∀ v, PersistentP (τi v)) → env_PersistentP Δ → env_PersistentP (τi :: Δ).
  Proof. by constructor. Qed.
  Global Instance env_persistent_lookup Δ x v :
    env_PersistentP Δ → PersistentP (env_lookup x Δ v).
  Proof. intros HΔ; revert x; induction HΔ=>-[|?] /=; apply _. Qed.
  Global Instance interp_persistent τ Δ v :
    env_PersistentP Δ → PersistentP (interp τ Δ v).
  Proof.
    revert v Δ; induction τ=> v Δ HΔ; simpl; try apply _.
    rewrite /PersistentP /interp_rec fixpoint_unfold /interp_rec1 /=.
    by apply always_intro'.
  Qed.
  Global Instance interp_env_persistent Γ Δ vs :
    env_PersistentP Δ → PersistentP (⟦ Γ ⟧* Δ vs) := _.

  Lemma interp_weaken Δ1 Π Δ2 τ :
    ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ (Δ1 ++ Π ++ Δ2)
    ≡ ⟦ τ ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2; simpl; auto.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - apply fixpoint_proper=> τi w /=.
      properness; auto. apply (IHτ (_ :: _)).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia. done.
    - intros w; simpl; properness; auto. apply (IHτ (_ :: _)).
    - intros w; simpl; properness; auto. by apply IHτ.
  Qed.

  Lemma interp_subst_up Δ1 Δ2 τ τ' :
    ⟦ τ ⟧ (Δ1 ++ interp τ' Δ2 :: Δ2)
    ≡ ⟦ τ.[upn (length Δ1) (τ' .: ids)] ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Δ2; induction τ=> Δ1 Δ2; simpl; auto.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - apply fixpoint_proper=> τi w /=.
      properness; auto. apply (IHτ (_ :: _)).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      rewrite !lookup_app_r; [|lia ..].
      destruct (x - length Δ1) as [|n] eqn:?; simpl.
      { symmetry. asimpl. apply (interp_weaken [] Δ1 Δ2 τ'). }
      rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia. done.
    - intros w; simpl; properness; auto. apply (IHτ (_ :: _)).
    - intros w; simpl; properness; auto. by apply IHτ.
  Qed.

  Lemma interp_subst Δ2 τ τ' : ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) ≡ ⟦ τ.[τ'/] ⟧ Δ2.
  Proof. apply (interp_subst_up []). Qed.

  Lemma interp_env_length Δ Γ vs : ⟦ Γ ⟧* Δ vs ⊢ length Γ = length vs.
  Proof. by iIntros "[% ?]". Qed.

  Lemma interp_env_Some_l Δ Γ vs x τ :
    Γ !! x = Some τ → ⟦ Γ ⟧* Δ vs ⊢ ∃ v, vs !! x = Some v ∧ ⟦ τ ⟧ Δ v.
  Proof.
    iIntros (?) "[Hlen HΓ]"; iDestruct "Hlen" as %Hlen.
    destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
    { by rewrite -Hlen; apply lookup_lt_Some with τ. }
    iExists v; iSplit. done. iApply (big_sep_elem_of with "HΓ").
    apply elem_of_list_lookup_2 with x.
    rewrite lookup_zip_with; by simplify_option_eq.
  Qed.

  Lemma interp_env_nil Δ : True ⊢ ⟦ [] ⟧* Δ [].
  Proof. iIntros ""; iSplit; auto. Qed.
  Lemma interp_env_cons Δ Γ vs τ v :
    ⟦ τ :: Γ ⟧* Δ (v :: vs) ⊣⊢ ⟦ τ ⟧ Δ v ∗ ⟦ Γ ⟧* Δ vs.
  Proof.
    rewrite /interp_env /= (assoc _ (⟦ _ ⟧ _ _)) -(comm _ (_ = _)%I) -assoc.
    by apply sep_proper; [apply pure_proper; omega|].
  Qed.

  Lemma interp_env_ren Δ (Γ : list type) (vs : list val) τi :
    ⟦ subst (ren (+1)) <$> Γ ⟧* (τi :: Δ) vs ⊣⊢ ⟦ Γ ⟧* Δ vs.
  Proof.
    apply sep_proper; [apply pure_proper; by rewrite fmap_length|].
    revert Δ vs τi; induction Γ=> Δ [|v vs] τi; csimpl; auto.
    apply sep_proper; auto. apply (interp_weaken [] [τi] Δ).
  Qed.
End logrel.

Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr τ).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
