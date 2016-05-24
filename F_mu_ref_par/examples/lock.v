From iris.proofmode Require Import invariants ghost_ownership tactics.
From F_mu_ref_par Require Import lang rules rules_binary.
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

Section proof.
  Context {Σ : gFunctors} {iS : cfgSG Σ}.
  Context (S : namespace).

  Lemma steps_with_lock N E ρ j K e l P Q :
    nclose N ⊆ E →
    (∀ f, e.[f] = e) (* e is a closed term *)
    →
    (∃ v, ∀ K', ((Spec_ctx N ρ ★ P ★ j ⤇ (fill K' (App e Unit)))%I)
            ⊢ |={E}=>(j ⤇ (fill K' (of_val v)) ★ Q)%I)
    →
    (((Spec_ctx N ρ ★ P ★ l ↦ₛ (♭v false) ★ j ⤇ (fill K (with_lock e (Loc l))))%I)
      ⊢ |={E}=>(j ⤇ (fill K (Unit)) ★ Q ★ l ↦ₛ (♭v false))%I).
  Proof.
    intros HNE H1 [v H2].
    iIntros "[#Hspec [HP [Hl Hj]]]".
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial.
    asimpl.
    Unshelve. 3: simpl; auto.
    iPvs (step_lam _ _ _ j (K ++ [AppRCtx (LamV _)])
                   _ _ _ _ with "[Hj]") as "Hj"; eauto.
    rewrite fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    Unshelve. 3: simpl; trivial.
    asimpl.
    iPvs (step_cas_suc _ _ _ j (K ++ [AppRCtx (LamV _); IfCtx _ _])
                       _ _ _ _ _ _ _ _ _ with "[Hj Hl]") as "[Hj Hl]"; trivial.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj Hl"; trivial.
    Unshelve. 7: simpl; trivial. 5: simpl; trivial. 4: trivial.
    iNext; trivial.
    rewrite fill_app. simpl.
    iPvs (step_if_true _ _ _ j (K ++ [AppRCtx (LamV _)])
                       _ _ _ with "[Hj]") as "Hj"; trivial.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite fill_app. simpl.
    Unshelve. all: trivial.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial.
    asimpl.
    Unshelve. 3: simpl; auto.
    rewrite H1.
    iPvs (H2 (K ++ [AppRCtx (LamV _)]) with "[Hj HP]") as "[Hj HQ]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial.
    asimpl.
    Unshelve. 3: auto using to_of_val.
    iPvs (step_lam _ _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iFrame "Hspec Hj"; trivial.
    asimpl.
    Unshelve. 3: simpl; auto.
    iPvs (step_store _ _ _ j K _ _ _ _ _ with "[Hj Hl]") as "[Hj Hl]"; eauto.
    iFrame "Hspec Hj"; trivial.
    Unshelve. 3: auto.
    iPvsIntro. iFrame "HQ Hj Hl"; trivial.
  Qed.

End proof.