Require Export iris.proofmode.tactics.
Require Export Autosubst.Autosubst.

Canonical Structure varC := leibnizC var.

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
