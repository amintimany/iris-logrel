From iris.proofmode Require Import invariants ghost_ownership tactics.
From F_mu_ref_par Require Import lang rules rules_binary typing.
Import uPred.

Definition newlock : expr := Alloc (♭ false).
Definition acquire : expr :=
  Lam (If (CAS (Var 1) (♭ false) (♭ true)) (Unit) (App (Var 0) (Var 1))).
Definition release : expr := Lam (Store (Var 1) (♭ false)).

Definition with_lock (e : expr) (l : expr) : expr :=
  App
    (Lam
       (App (Lam (App (Lam (App release (Var 5))) (App e Unit)))
            (App acquire (Var 1))
       )
    )
    l
.

Lemma newlock_closed f : newlock.[f] = newlock.
Proof. by asimpl. Qed.

Lemma acquire_closed f : acquire.[f] = acquire.
Proof. by asimpl. Qed.

Lemma release_closed f : release.[f] = release.
Proof. by asimpl. Qed.

Lemma with_lock_closed e l:
  (∀ f : var → expr, e.[f] = e) →
  (∀ f : var → expr, l.[f] = l) →
  ∀ f, (with_lock e l).[f] = with_lock e l.
Proof. asimpl => H1 H2 f. by rewrite H1 H2. Qed.

Definition LockType := Tref TBool.

Lemma newlock_type Γ : typed Γ newlock LockType.
Proof. repeat constructor. Qed.

Lemma acquire_type Γ : typed Γ acquire (TArrow LockType TUnit).
Proof. do 3 econstructor; eauto using EqTBool; repeat constructor. Qed.

Lemma release_type Γ : typed Γ release (TArrow LockType TUnit).
Proof. repeat econstructor. Qed.

Lemma with_lock_type e l Γ τ :
  (∀ f : var → expr, e.[f] = e) →
  typed Γ e (TArrow TUnit τ) →
  typed Γ l LockType →
  typed Γ (with_lock e l) TUnit.
Proof.
  intros H1 H2 H3. econstructor; eauto.
  repeat (econstructor; eauto using release_type, acquire_type).
  eapply (closed_context_weakening [_; _; _; _]); eauto.
Qed.

Section proof.
  Context {Σ : gFunctors} {iS : cfgSG Σ}.

  Lemma steps_newlock N E ρ j K :
    nclose N ⊆ E →
    (((Spec_ctx N ρ ★ j ⤇ (fill K (newlock)))%I)
      ⊢ |={E}=>(∃ l, j ⤇ (fill K (Loc l)) ★ l ↦ₛ (♭v false))%I).
  Proof.
    intros HNE.
    iIntros "[#Hspec Hj]".
    iPvs (step_alloc _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial.
    Unshelve. all: trivial.
  Qed.

  Global Opaque newlock.

  Lemma steps_acquire N E ρ j K l :
    nclose N ⊆ E →
    (((Spec_ctx N ρ ★ l ↦ₛ (♭v false) ★ j ⤇ (fill K (App acquire (Loc l))))%I)
      ⊢ |={E}=>(j ⤇ (fill K Unit) ★ l ↦ₛ (♭v true))%I).
  Proof.
    intros HNE.
    iIntros "[#Hspec [Hl Hj]]". unfold acquire.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. simpl.
    iPvs (step_cas_suc _ _ _ j (K ++ [IfCtx _ _])
                       _ _ _ _ _ _ _ _ _ with "[Hj Hl]") as "[Hj Hl]"; trivial.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj Hl"; trivial.
    iNext; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_if_true _ _ _ j K _ _ _ with "[Hj]") as "Hj"; trivial.
    iFrame "Hspec Hj"; trivial.
    iPvsIntro. iFrame "Hj Hl"; trivial.
    Unshelve. all:trivial.
  Qed.

  Global Opaque acquire.

  Lemma steps_release N E ρ j K l b:
    nclose N ⊆ E →
    (((Spec_ctx N ρ ★ l ↦ₛ (♭v b) ★ j ⤇ (fill K (App release (Loc l))))%I)
      ⊢ |={E}=>(j ⤇ (fill K Unit) ★ l ↦ₛ (♭v false))%I).
  Proof.
    intros HNE.
    iIntros "[#Hspec [Hl Hj]]". unfold release.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. simpl.
    iPvs (step_store _ _ _ j K _ _ _ _ _ with "[Hj Hl]") as "[Hj Hl]"; eauto.
    iFrame "Hspec Hj"; trivial.
    iPvsIntro. iFrame "Hj Hl"; trivial.
    Unshelve. all: trivial.
  Qed.

  Global Opaque release.

  Lemma steps_with_lock N E ρ j K e l P Q :
    nclose N ⊆ E →
    (∀ f, e.[f] = e) (* e is a closed term *)
    →
    (∃ v, ∀ K', ((Spec_ctx N ρ ★ P ★ j ⤇ (fill K' (App e Unit)))%I)
            ⊢ |={E}=>(j ⤇ (fill K' (of_val v)) ★ Q)%I)
    →
    (((Spec_ctx N ρ ★ P ★ l ↦ₛ (♭v false)
                ★ j ⤇ (fill K (with_lock e (Loc l))))%I)
      ⊢ |={E}=>(j ⤇ (fill K (Unit)) ★ Q ★ l ↦ₛ (♭v false))%I).
  Proof.
    intros HNE H1 [v H2].
    iIntros "[#Hspec [HP [Hl Hj]]]".
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. simpl.
    rewrite acquire_closed release_closed H1. asimpl.
    iPvs (steps_acquire _ _ _ j (K ++ [AppRCtx (LamV _)])
                   _ _ with "[Hj Hl]") as "[Hj Hl]"; eauto.
    rewrite fill_app; simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite fill_app; simpl.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. asimpl.
    rewrite release_closed H1.
    iPvs (H2 (K ++ [AppRCtx (LamV _)]) with "[Hj HP]") as "[Hj HQ]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial. simpl.
    rewrite release_closed.
    iPvs (steps_release _ _ _ j K _ _ with "[Hj Hl]") as "[Hj Hl]"; eauto.
    iFrame "Hspec Hl Hj"; trivial.
    iPvsIntro. iFrame "Hj HQ Hl"; trivial.
    Unshelve.
    all: try match goal with |- to_val _ = _ => auto using to_of_val end.
    trivial.
  Qed.

  Global Opaque with_lock.
End proof.