From iris.program_logic Require Export weakestpre.
From iris_logrel.stlc Require Export lang typing.

(** interp : is a unary logical relation. *)
Section logrel.
Context `{irisG lang Σ}.

Fixpoint interp (τ : type) (w : val) : iProp Σ :=
  match τ with
  | TUnit => w = UnitV
  | TProd τ1 τ2 => ∃ w1 w2, w = PairV w1 w2 ∧ ⟦ τ1 ⟧ w1 ∧ ⟦ τ2 ⟧ w2
  | TSum τ1 τ2 =>
     (∃ w1, w = InjLV w1 ∧ ⟦ τ1 ⟧ w1) ∨ (∃ w2, w = InjRV w2 ∧ ⟦ τ2 ⟧ w2)
  | TArrow τ1 τ2 => □ ∀ v, ⟦ τ1 ⟧ v → WP App (# w) (# v) {{ ⟦ τ2 ⟧ }}
  end%I
where "⟦ τ ⟧" := (interp τ).

Definition interp_expr (τ : type) (e : expr) : iProp Σ :=
  WP e {{ ⟦ τ ⟧ }}%I.

Global Instance interp_persistent τ v : PersistentP (⟦ τ ⟧ v).
Proof. revert v; induction τ=> v /=; apply _. Qed.
End logrel.

Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr τ).
