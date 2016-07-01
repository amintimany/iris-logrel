From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris_logrel.F_mu_ref_par Require Export rules_binary typing.
Import uPred.

(* HACK: move somewhere else *)
Ltac auto_proper ::=
  (* Deal with "pointwise_relation" *)
  repeat lazymatch goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  end;
  (* Normalize away equalities. *)
  repeat match goal with
  | H : _ ≡{_}≡ _ |-  _ => apply (timeless_iff _ _) in H
  | _ => progress simplify_eq
  end;
  (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
  try (f_equiv; fast_done || auto_proper).

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{heapIG Σ, cfgSG Σ} (L : namespace).
  Notation D := (prodC valC valC -n> iPropG lang Σ).
  Implicit Types τi : D.
  Implicit Types Δ : listC D.
  Implicit Types interp : listC D → D.

  Program Definition ctx_lookup (x : var) : listC D -n> D := λne Δ,
    from_option id (cconst True)%I (Δ !! x).
  Solve Obligations with solve_proper_alt.

  Program Definition interp_unit : listC D -n> D := λne Δ ww,
    (ww.1 = UnitV ∧ ww.2 = UnitV)%I.
  Solve Obligations with solve_proper_alt.
  Program Definition interp_nat : listC D -n> D := λne Δ ww,
    (∃ n : nat, ww.1 = ♯v n ∧ ww.2 = ♯v n)%I.
  Solve Obligations with solve_proper.
  Program Definition interp_bool : listC D -n> D := λne Δ ww,
    (∃ b : bool, ww.1 = ♭v b ∧ ww.2 = ♭v b)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_prod
      (interp1 interp2 : listC D -n> D) : listC D -n> D := λne Δ ww,
    (∃ vv1 vv2, ww = (PairV (vv1.1) (vv2.1), PairV (vv1.2) (vv2.2)) ∧
                interp1 Δ vv1 ∧ interp2 Δ vv2)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_sum
      (interp1 interp2 : listC D -n> D) : listC D -n> D := λne Δ ww,
    ((∃ vv, ww = (InjLV (vv.1), InjLV (vv.2)) ∧ interp1 Δ vv) ∨
     (∃ vv, ww = (InjRV (vv.1), InjRV (vv.2)) ∧ interp2 Δ vv))%I.
  Solve Obligations with solve_proper.

  Program Definition interp_arrow
      (interp1 interp2 : listC D -n> D) : listC D -n> D := λne Δ ww,
    (□ ∀ j K vv,
      interp1 Δ vv ★ j ⤇ fill K (App (# ww.2) (# vv.2)) →
      WP App (# ww.1) (# vv.1) {{ v, ∃ v', j ⤇ fill K (# v') ★ interp2 Δ (v, v') }})%I.
  Solve Obligations with solve_proper.

  Program Definition interp_forall
      (interp : listC D -n> D) : listC D -n> D := λne Δ ww,
    (□ ∀ τi j K,
       (■ ∀ ww, PersistentP (τi ww)) →
       j ⤇ fill K (TApp (# ww.2)) →
       WP TApp (# ww.1) {{ v, ∃ v', j ⤇ fill K (# v') ★ interp (τi :: Δ) (v, v')}})%I.
  Solve Obligations with solve_proper.

  Program Definition interp_rec1
      (interp : listC D -n> D) (Δ : listC D) (τi : D) : D := λne ww,
    (□ ∃ vv, ww = (FoldV (vv.1), FoldV (vv.2)) ∧ ▷ interp (τi :: Δ) vv)%I.
  Solve Obligations with solve_proper.

  Global Instance interp_rec1_contractive
    (interp : listC D -n> D) (Δ : listC D) : Contractive (interp_rec1 interp Δ).
  Proof.
    intros n τi1 τi2 Hτi ww; cbn.
    apply always_ne, exist_ne; intros vv; apply and_ne; trivial.
    apply later_contractive =>i Hi. by rewrite Hτi.
  Qed.

  Program Definition interp_rec (interp : listC D -n> D) : listC D -n> D := λne Δ,
    fixpoint (interp_rec1 interp Δ).
  Next Obligation.
    intros interp n Δ1 Δ2 HΔ; apply fixpoint_ne => τi ww. solve_proper.
  Qed.

  Program Definition interp_ref_inv (ll : loc * loc) : D -n> iPropG lang Σ := λne τi,
    (∃ vv, ll.1 ↦ᵢ vv.1 ★ ll.2 ↦ₛ vv.2 ★ τi vv)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref
      (interp : listC D -n> D) : listC D -n> D := λne Δ ww,
    (∃ ll, ww = (LocV (ll.1), LocV (ll.2)) ∧
           inv (L .@ ll) (interp_ref_inv ll (interp Δ)))%I.
  Solve Obligations with solve_proper.

  Fixpoint interp (τ : type) : listC D -n> D :=
    match τ return _ with
    | TUnit => interp_unit
    | TNat => interp_nat
    | TBool => interp_bool
    | TProd τ1 τ2 => interp_prod (interp τ1) (interp τ2)
    | TSum τ1 τ2 => interp_sum (interp τ1) (interp τ2)
    | TArrow τ1 τ2 => interp_arrow (interp τ1) (interp τ2)
    | TVar x => ctx_lookup x
    | TForall τ' => interp_forall (interp τ')
    | TRec τ' => interp_rec (interp τ')
    | Tref τ' => interp_ref (interp τ')
    end.

  Class ctx_PersistentP Δ :=
    ctx_persistentP : Forall (λ τi, ∀ vv, PersistentP (τi vv)) Δ.
  Global Instance ctx_persistent_nil : ctx_PersistentP [].
  Proof. by constructor. Qed.
  Global Instance ctx_persistent_cons τi Δ :
    (∀ vv, PersistentP (τi vv)) → ctx_PersistentP Δ → ctx_PersistentP (τi :: Δ).
  Proof. by constructor. Qed.
  Global Instance ctx_persistent_lookup Δ x vv :
    ctx_PersistentP Δ → PersistentP (ctx_lookup x Δ vv).
  Proof. intros HΔ; revert x; induction HΔ=>-[|?] /=; apply _. Qed.

  Global Instance interp_var_persistent τ Δ vv :
    ctx_PersistentP Δ → PersistentP (interp τ Δ vv).
  Proof.
    revert vv Δ; induction τ=> vv Δ HΔ; simpl; try apply _.
    rewrite /PersistentP /interp_rec fixpoint_unfold /interp_rec1 /=.
    by apply always_intro'.
  Qed.

  Lemma interp_weaken Δ1 Π Δ2 τ :
    interp τ.[iter (length Δ1) up (ren (+ length Π))] (Δ1 ++ Π ++ Δ2)
    ≡ interp τ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2; simpl; auto.
    - intros ww; simpl; properness; auto.
    - intros ww; simpl; properness; auto.
    - intros ww; simpl; properness; auto.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - apply fixpoint_proper=> τi ww /=.
      properness; auto. apply (IHτ (_ :: _)).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      change (uPredC (iResUR lang _)) with (iPropG lang Σ).
      rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia. done.
    - intros ww; simpl; properness; auto. by apply (IHτ (_ :: _)).
    - intros ww; simpl; properness; auto. by apply IHτ.
  Qed.

  Lemma interp_subst_up Δ1 Δ2 τ τ' :
    interp τ (Δ1 ++ interp τ' Δ2 :: Δ2)
    ≡ interp τ.[iter (length Δ1) up (τ' .: ids)] (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Δ2; induction τ=> Δ1 Δ2; simpl; auto.
    - intros ww; simpl; properness; auto.
    - intros ww; simpl; properness; auto.
    - intros ww; simpl; properness; auto.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - apply fixpoint_proper=> τi ww /=.
      properness; auto. apply (IHτ (_ :: _)).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      change (uPredC (iResUR lang _)) with (iPropG lang Σ).
      rewrite !lookup_app_r; [|lia ..].
      destruct (x - length Δ1) as [|n] eqn:?; simpl.
      { symmetry. asimpl. apply (interp_weaken [] Δ1 Δ2 τ'). }
      change (uPredC (iResUR lang _)) with (iPropG lang Σ).
      rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia. done.
    - intros ww; simpl; properness; auto. apply (IHτ (_ :: _)).
    - intros ww; simpl; properness; auto. by apply IHτ.
  Qed.

  Lemma interp_subst Δ2 τ τ' : interp τ (interp τ' Δ2 :: Δ2) ≡ interp τ.[τ'/] Δ2.
  Proof. apply (interp_subst_up []). Qed.

  Lemma context_interp_ren_S Δ (Γ : list type) (vvs : list (val * val)) τi :
    ([∧] zip_with (λ τ, interp τ Δ) Γ vvs)
    ⊣⊢ ([∧] zip_with (λ τ, interp τ.[ren (+1)] (τi :: Δ)) Γ vvs).
  Proof.
    revert Δ vvs τi; induction Γ=> Δ [|vv vvs] τi; simpl; auto.
    apply and_proper; auto.
    symmetry. apply (interp_weaken [] [τi] Δ).
  Qed.

  Lemma interp_EqType_agree τ v v' Δ :
    ctx_PersistentP Δ → EqType τ → interp τ Δ (v, v') ⊢ ■ (v = v').
  Proof.
    intros ? Hτ; revert v v'; induction Hτ; iIntros {v v'} "#H1 /=".
    - by iDestruct "H1" as "[% %]"; subst.
    - by iDestruct "H1" as {n} "[% %]"; subst.
    - by iDestruct "H1" as {b} "[% %]"; subst.
    - iDestruct "H1" as { [??] [??] } "[% [H1 H2]]"; simplify_eq/=.
      rewrite IHHτ1 IHHτ2.
      by iDestruct "H1" as "%"; iDestruct "H2" as "%"; subst.
    - iDestruct "H1" as "[H1|H1]".
      + iDestruct "H1" as { [??] } "[% H1]"; simplify_eq/=.
        rewrite IHHτ1. by iDestruct "H1" as "%"; subst.
      + iDestruct "H1" as { [??] } "[% H1]"; simplify_eq/=.
        rewrite IHHτ2. by iDestruct "H1" as "%"; subst.
  Qed.
End logrel.
