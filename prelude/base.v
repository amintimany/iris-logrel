Require Export iris.proofmode.tactics.
From iris.program_logic Require Import wsat.
Require Import iris.program_logic.weakestpre.
Require Import iris.program_logic.language.
From mathcomp Require Export ssreflect.
From iris.prelude Require Export prelude.
Global Set Bullet Behavior "Strict Subproofs".
Global Open Scope general_if_scope.
Ltac done := prelude.tactics.done.
Require Export Autosubst.Autosubst.

Fixpoint iter (n : nat) `(f : A → A) :=
  match n with
  | O => λ x, x
  | S n' => λ x, f (iter n' f x)
  end.

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.
  
  Lemma iter_up (m x : nat) (f : var → term) :
    iter m up f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
  Proof.
    revert x; induction m; cbn; auto with omega.
    intros x; destruct x; cbn; asimpl; trivial.
    intros x; destruct x; cbn; asimpl; trivial.
    rewrite IHm; repeat destruct lt_dec;
      asimpl; auto with omega.
  Qed.

End Autosubst_Lemmas.
  
Section uPred_Lemmas.
  Import uPred.
  Context {Λ : language} {Σ : iFunctor}.
  Implicit Types P : iProp Λ Σ.
  Implicit Types Φ : val Λ → iProp Λ Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Definition double_exists M A ψ Q Y :=
    @exist_elim M A (λ x, ∃ b : A, ψ x b)%I Q (λ x, @exist_elim M A _ Q (Y x)).
  
  Lemma wp_impl_l E e Φ Ψ :
    ((□ ∀ v, Φ v → Ψ v) ∧ WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Ψ }}.
  Proof.
    rewrite wp_always_l; apply wp_mono=> // v.
  by rewrite always_elim (forall_elim v) impl_elim_l.
  Qed.
  Lemma wp_impl_r E e Φ Ψ :
    (WP e @ E {{ Φ }} ∧ □ (∀ v, Φ v → Ψ v)) ⊢ WP e @ E {{ Ψ }}.
  Proof. by rewrite comm wp_impl_l. Qed.
  Lemma wp_mask_weaken E1 E2 e Φ :
    E1 ⊆ E2 → WP e @ E1 {{ Φ }} ⊢ WP e @ E2 {{ Φ }}.
  Proof. auto using wp_mask_frame_mono. Qed.
  
End uPred_Lemmas.
